/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.CompactSpectral
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.PDE.Elliptic.Dirichlet
import Numlib.Analysis.PDE.Elliptic.Regularity
import Numlib.MeasureTheory.Function.LpSpace.Convergence

/-!
# Eigenfunctions and spectral decomposition of the Dirichlet problem

Let $\Omega \subseteq \mathbb{R}^N$ be open. This module constructs the Dirichlet eigenfunctions of
$-\Delta$ on $\Omega$, following §9.8 of [brezis2011functional]. Theorem 9.31 there states: if
$\Omega$ is bounded, there are a Hilbert basis $(e_n)$ of $L^2(\Omega)$ and real numbers
$\lambda_n > 0$ with $\lambda_n \to +\infty$ such that $e_n \in H^1_0(\Omega) \cap C^\infty(\Omega)$
and $-\Delta e_n = \lambda_n e_n$ in $\Omega$. The weak form (83) of the equation is
$$\int_\Omega \nabla e_n \cdot \nabla \varphi = \lambda_n \int_\Omega e_n \varphi \qquad \text{for
  all } \varphi \in H^1_0(\Omega).$$

The construction works for any bounded form $a$ on $H^1(\Omega)$ that is symmetric and coercive on
$H^1_0(\Omega)$, and $\Omega$ need only have finite measure. For $f \in L^2(\Omega)$ let
$Sf \in H^1_0(\Omega)$ be the solution of $a(Sf, v) = \langle f, v \rangle_{L^2}$ for all
$v \in H^1_0(\Omega)$, and let the solution operator $T : L^2(\Omega) \to L^2(\Omega)$ map $f$ to
the function of $Sf$. Then $T$ is compact, symmetric, positive and injective. The spectral theorem
for compact symmetric operators gives a Hilbert basis $(e_n)$ of $L^2(\Omega)$ with
$T e_n = \mu_n e_n$, where $\mu_n > 0$ decreases to $0$. The eigenvalues of the problem are
$\lambda_n = 1/\mu_n$, which increase to $+\infty$, and the eigenfunctions are the elements
$u_n = \lambda_n S e_n \in H^1_0(\Omega)$, whose functions are the $e_n$. The case
$a(u, v) = \int_\Omega \nabla u \cdot \nabla v$ is Theorem 9.31. The module also proves Remark 28
(the normalized eigenfunctions are Hilbert bases of $H^1_0(\Omega)$), Remark 29 (smoothness up to
the boundary on a smooth domain) and Remark 30 (a general symmetric elliptic operator) of
[brezis2011functional], Chapter 9.

## Main definitions

* `Elliptic.eigenbasis`, `Elliptic.eigenvalue`, `Elliptic.eigenfunction`: for a symmetric form $a$
  coercive on $H^1_0(\Omega)$, the Hilbert basis $(e_n)$ of $L^2(\Omega)$, the eigenvalues
  $\lambda_n$, and the eigenfunctions $u_n \in H^1_0(\Omega)$ with function $e_n$.
* `Elliptic.dirichletEigenbasis`, `Elliptic.dirichletEigenvalue`, `Elliptic.dirichletEigenfunction`:
  the same objects for $a(u, v) = \int_\Omega \nabla u \cdot \nabla v$ on a bounded $\Omega$.
* `HilbertBasis.ofInnerEqMul`: a Hilbert basis transported from $L$ to $E$ along an injective map
  and a family $u_i$ with $\langle u_i, x \rangle_E = c_i \langle b_i, Tx \rangle_L$.
* `Elliptic.restrictOperator`, `Elliptic.dirichletOperator`: the bounded operator $A$ on
  $H^1_0(\Omega)$ with $\langle Au, v \rangle_{H^1} = a(u, v)$, and its case for the Dirichlet form.
* `Elliptic.energyEigenbasis`, `Elliptic.sobolevZeroEigenbasis`: the Hilbert bases
  $(u_n / \sqrt{\lambda_n})$ of $H^1_0(\Omega)$ for the inner product $a$, and
  $(u_n / \sqrt{\lambda_n + 1})$ for the $H^1$ inner product.

## Main results

* `Elliptic.solutionOperator_isSymmetric`, `Elliptic.inner_solutionOperator_nonneg`,
  `Elliptic.solutionOperator_ker_eq_bot`: the solution operator $T$ is symmetric, positive and
  injective.
* `Elliptic.eigenvalue_pos`, `Elliptic.monotone_eigenvalue`, `Elliptic.tendsto_eigenvalue_atTop`:
  $0 < \lambda_0 \le \lambda_1 \le \dots$ and $\lambda_n \to +\infty$.
* `Elliptic.form_eigenfunction`: the weak equation $a(u_n, \varphi) = \lambda_n \langle e_n, \varphi
  \rangle_{L^2}$ for $\varphi \in H^1_0(\Omega)$.
* `Elliptic.dirichletForm_dirichletEigenfunction`, `Elliptic.dirichletEigenvalue_pos`,
  `Elliptic.tendsto_dirichletEigenvalue_atTop`: the Hilbert-space part of Theorem 9.31.
* `Elliptic.dirichletEigenbasis_exists_contDiffOn`: the smoothness part of Theorem 9.31: $e_n$ has a
  representative $\tilde u$ of class $C^\infty$ on $\Omega$ with
  $-\Delta \tilde u = \lambda_n \tilde u$ at every point of $\Omega$.
* `Elliptic.hilbertBasis_energy`, `Elliptic.hilbertBasis_sobolevZero`: Remark 28, the two Hilbert
  bases of $H^1_0(\Omega)$.
* `Elliptic.exists_contDiffOn_closure_eigenfunction`: Remark 29,
  $e_n \in C^\infty(\overline{\Omega})$ on a bounded domain of class $C^\infty$.
* `Elliptic.exists_hilbertBasis_eigen_general`: Remark 30, the eigenfunction basis of a symmetric
  uniformly elliptic operator with $L^\infty$ coefficients.

## Proof outline

The solution operator $T$ is compact by the Rellich–Kondrachov theorem when $\Omega$ has finite
measure (`Elliptic.solutionOperator_isCompactOperator`). It is symmetric because $\langle Tf, g
\rangle_{L^2} = a(Sg, Sf) = a(Sf, Sg) = \langle f, Tg \rangle_{L^2}$. It is injective because
$Tf = 0$ gives $\int_\Omega f \varphi = 0$ for all $\varphi \in H^1_0(\Omega)$. Since $L^2(\Omega)$
is infinite-dimensional for a nonempty open $\Omega \subseteq \mathbb{R}^N$ with $N \ge 1$, the
spectral theorem `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` gives the basis. Interior
regularity (Remark 25, `Elliptic.regularity_interior_higher`) applied to
$-\Delta e_n = \lambda_n e_n$ gives $e_n \in H^m_{\mathrm{loc}}(\Omega)$ for all $m$, hence a
$C^\infty$ representative. The weak equation then gives the pointwise equation for that
representative. On a domain of class $C^\infty$, Theorem 9.25 gives $e_n \in H^m(\Omega)$ for all
$m$ and $e_n \in C^\infty(\overline{\Omega})$.

## Implementation notes

* The basis and the eigenvalues are data, not the content of an existential statement. The weak
  equation (83) is a theorem about these data (`Elliptic.form_eigenfunction`). The heat and wave
  equations in `Numlib.Analysis.PDE.Heat` and `Numlib.Analysis.PDE.Wave` use them.
* The spaces are on $\mathbb{R}^N$ with `N = d + 1`. For $N = 0$ the open set $\Omega$ is at most a
  point and $L^2(\Omega)$ is finite-dimensional, so there is no basis indexed by $\mathbb{N}$. The
  symmetry and the injectivity of the solution operator hold for every $N$.
* The Lean types `Lp ℝ 2 (volume.restrict Ω)`, `SobolevEuclidean N 1 2 Ω` and
  `SobolevEuclideanZero N 1 2 Ω` are $L^2(\Omega)$, $H^1(\Omega)$ and $H^1_0(\Omega)$. The space
  $H^1_0(\Omega)$ carries the $H^1$ inner product $\int_\Omega (\nabla u \cdot \nabla v + uv)$. The
  function of $u \in H^1_0(\Omega)$ in $L^2(\Omega)$ is `SobolevMultiIndexZero.fnL … u`.
* The basis $(u_n / \sqrt{\lambda_n})$ lives on the energy space
  `WithEnergy (Elliptic.restrictOperator Ω a) _` of `Numlib.Analysis.InnerProductSpace.Energy`,
  which is $H^1_0(\Omega)$ with the inner product $a(u, v)$. The basis
  $(u_n / \sqrt{\lambda_n + 1})$ is a `HilbertBasis` of `SobolevEuclideanZero (d + 1) 1 2 Ω` itself,
  because the form of $-\Delta + 1$ is the $H^1$ inner product.
* In Remark 30 the coefficients $a_{ij}$ are assumed symmetric, $a_{ij} = a_{ji}$.
  [brezis2011functional] omits this hypothesis; without it the solution operator is not
  self-adjoint. The eigenvalues come from the form $a + \lambda_0 \langle \cdot, \cdot
  \rangle_{L^2}$, with $\lambda_0$ from Gårding's inequality, and are shifted back by $\lambda_0$.
  They need not be positive.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace Elliptic

/-! ### Symmetry, positivity and injectivity of the solution operator -/

section Symmetric

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N))) (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
  (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)

/-- Let $a$ be a bounded form on $H^1(\Omega)$ that is coercive on $H^1_0(\Omega)$, let $T$ be its
solution operator on $L^2(\Omega)$, and let $S f \in H^1_0(\Omega)$ be the solution with datum
$f$, so that $Tf$ is the function of $Sf$. Then for all $f, g \in L^2(\Omega)$
$$\langle Tf, g \rangle_{L^2} = a(Sg, Sf).$$

This is the weak equation for $Sg$ tested with $Sf \in H^1_0(\Omega)$. Here $S$ is
`Elliptic.solutionMap`. -/
theorem inner_solutionOperator_eq_form
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ⟪solutionOperator Ω a ha f, g⟫_ℝ = a (solutionMap Ω a ha g) (solutionMap Ω a ha f) := by
  rw [real_inner_comm, ← SesqForm.restrict_apply a (SobolevEuclideanZero N 1 2 Ω),
    restrict_apply_solutionMap]
  rfl

/-- Let $a$ be a bounded form on $H^1(\Omega)$ that is Hermitian and coercive on $H^1_0(\Omega)$.
Then the solution operator $T$ of $a$ is symmetric on $L^2(\Omega)$: $\langle Tf, g
\rangle_{L^2} = \langle f, Tg \rangle_{L^2}$ for all $f, g$.

Here $Sf \in H^1_0(\Omega)$ is the solution with datum $f$. The proof is $\langle Tf, g
\rangle_{L^2} = a(Sg, Sf) = a(Sf, Sg) = \langle f, Tg \rangle_{L^2}$. In the proof of Theorem
9.31, [brezis2011functional] says to repeat the proof of Theorem 8.21; the one-dimensional
Sturm–Liouville theorem is its Theorem 8.22. -/
theorem solutionOperator_isSymmetric (hsymm : a.IsHermitian) :
    (solutionOperator Ω a ha : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).IsSymmetric := by
  intro f g
  change ⟪solutionOperator Ω a ha f, g⟫_ℝ = ⟪f, solutionOperator Ω a ha g⟫_ℝ
  rw [inner_solutionOperator_eq_form, real_inner_comm (solutionOperator Ω a ha g) f,
    inner_solutionOperator_eq_form, SesqForm.isHermitian_real_iff] at *
  exact hsymm _ _

/-- Let $a$ be a bounded form on $H^1(\Omega)$ that is coercive on $H^1_0(\Omega)$, with solution
operator $T$ and solution map $S$. Then $\langle Tf, f \rangle_{L^2} = a(Sf, Sf)$ for every
$f \in L^2(\Omega)$. -/
theorem inner_solutionOperator_self_eq
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ⟪solutionOperator Ω a ha f, f⟫_ℝ = a (solutionMap Ω a ha f) (solutionMap Ω a ha f) :=
  inner_solutionOperator_eq_form Ω a ha f f

/-- Let $a$ be a bounded form on $H^1(\Omega)$ that is coercive on $H^1_0(\Omega)$. Then its
solution operator $T$ is positive: $\langle Tf, f \rangle_{L^2} \ge 0$ for every
$f \in L^2(\Omega)$.

The proof is $\langle Tf, f \rangle_{L^2} = a(Sf, Sf) \ge c \|Sf\|_{H^1}^2 \ge 0$, with the
coercivity constant $c > 0$. The form need not be Hermitian. -/
theorem inner_solutionOperator_nonneg
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    0 ≤ ⟪solutionOperator Ω a ha f, f⟫_ℝ := by
  rw [inner_solutionOperator_self_eq]
  obtain ⟨c, hc, hcoer⟩ := id ha
  have h := hcoer (solutionMap Ω a ha f)
  rw [SesqForm.restrict_apply] at h
  exact le_trans (by positivity) h

/-- Let $a$ be a bounded form on $H^1(\Omega)$ that is coercive on $H^1_0(\Omega)$. Then its
solution operator $T$ on $L^2(\Omega)$ is injective: $\ker T = \{0\}$.

This is the claim $N(T) = \{0\}$ in the proof of Theorem 9.31 of [brezis2011functional]. If
$Tf = 0$, the solution $u \in H^1_0(\Omega)$ is $0$, so
$\int_\Omega f \varphi = a(0, \varphi) = 0$ for every $\varphi \in H^1_0(\Omega)$. A function of
$L^2(\Omega)$ that is orthogonal to $H^1_0(\Omega)$ is zero
(`SobolevEuclideanZero.toDualL2_injective`). -/
theorem solutionOperator_ker_eq_bot :
    LinearMap.ker (solutionOperator Ω a ha :
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun f hf ↦ ?_
  have hu : solutionMap Ω a ha f = 0 :=
    SobolevMultiIndexZero.fnL_injective (hf.trans (map_zero _).symm)
  have h1 : loadL Ω (SobolevEuclideanZero N 1 2 Ω) f = 0 := by
    calc loadL Ω (SobolevEuclideanZero N 1 2 Ω) f
        = a.restrict (SobolevEuclideanZero N 1 2 Ω) (solutionMap Ω a ha f) :=
          (ContinuousLinearMap.ext (restrict_apply_solutionMap Ω a ha f)).symm
      _ = a.restrict (SobolevEuclideanZero N 1 2 Ω) 0 := congrArg _ hu
      _ = 0 := (a.restrict (SobolevEuclideanZero N 1 2 Ω)).map_zero
  have h2 : SobolevEuclideanZero.toDualL2 N Ω f = 0 := h1
  exact SobolevEuclideanZero.toDualL2_injective (h2.trans (map_zero _).symm)

end Symmetric

/-- Let $a$ be a bounded real form on a real inner product space $V$, and let $K$ be a subspace of
$V$. Then $a(cu, v) = c \, a(u, v)$ for all $c \in \mathbb{R}$, $u \in K$ and $v \in V$, where
$cu$ is formed in $K$. -/
theorem _root_.SesqForm.apply_coe_smul_left {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (a : SesqForm ℝ V) (K : Submodule ℝ V) (c : ℝ) (u : K) (v : V) :
    a (c • u : K) v = c * a u v := by
  rw [Submodule.coe_smul, map_smulₛₗ, conj_trivial, smul_apply, smul_eq_mul]

/-! ### The eigenbasis of a symmetric coercive form -/

section Eigenbasis

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
  (a : SesqForm ℝ (SobolevEuclidean (d + 1) 1 2 Ω)) (hsymm : a.IsHermitian)
  (ha : (a.restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoercive)

include hne in
/-- Let $\Omega \subseteq \mathbb{R}^N$ be a nonempty open set, with $N = d + 1 \ge 1$. Then
$L^2(\Omega)$ is infinite-dimensional.

This is the hypothesis of infinite dimension in the spectral theorem
`ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis`. The proof is
`MeasureTheory.Lp.not_finiteDimensional_of_isOpen`. -/
theorem not_finiteDimensional_L2 :
    ¬ FiniteDimensional ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :=
  Lp.not_finiteDimensional_of_isOpen volume 2 Ω.isOpen hne

/-- The **eigenbasis of a symmetric coercive form**. Let $\Omega \subseteq \mathbb{R}^N$,
$N = d + 1$, be a nonempty open set of finite measure, and let $a$ be a bounded form on
$H^1(\Omega)$ that is Hermitian and coercive on $H^1_0(\Omega)$. This is the Hilbert basis
$(e_n)_{n \in \mathbb{N}}$ of $L^2(\Omega)$ that consists of eigenvectors of the solution
operator $T$ of $a$.

The vector $e_n$ is the function of `Elliptic.eigenfunction … n` $\in H^1_0(\Omega)$. That
element solves $a(u_n, \varphi) = \lambda_n \langle e_n, \varphi \rangle_{L^2}$ for all
$\varphi \in H^1_0(\Omega)$, where $\lambda_n$ is `Elliptic.eigenvalue … n`
(`Elliptic.form_eigenfunction`). This is the abstract core of Theorem 9.31 of
[brezis2011functional].

The basis is `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` applied to $T$. Its
hypotheses are the symmetry, the compactness and the injectivity of $T$, and the infinite
dimension of $L^2(\Omega)$. -/
def eigenbasis :
    HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :=
  ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis
    (solutionOperator_isSymmetric Ω a ha hsymm) (solutionOperator_isCompactOperator Ω hΩ a ha)
    (solutionOperator_ker_eq_bot Ω a ha) (not_finiteDimensional_L2 Ω hne)

/-- The eigenvalues $\mu_n$ of the solution operator $T$ of the form $a$, listed with multiplicity
in decreasing order, so that $T e_n = \mu_n e_n$.

This is `ContinuousLinearMap.IsSymmetric.eigenvalueSeq` applied to $T$. -/
def eigenvalueSeq : ℕ → ℝ :=
  ContinuousLinearMap.IsSymmetric.eigenvalueSeq (solutionOperator_isSymmetric Ω a ha hsymm)
    (solutionOperator_isCompactOperator Ω hΩ a ha)

/-- The **eigenvalues** $\lambda_n = 1/\mu_n$ of the weak eigenvalue problem $a(u, \varphi) =
\lambda \langle u, \varphi \rangle_{L^2}$ for all $\varphi \in H^1_0(\Omega)$. They are the
reciprocals of the eigenvalues $\mu_n$ of the solution operator.

Lean's convention $0^{-1} = 0$ applies to the definition. When $\Omega$ is nonempty,
$\mu_n > 0$, and the eigenvalues are positive, nondecreasing and tend to $+\infty$: see
`Elliptic.eigenvalue_pos`, `Elliptic.monotone_eigenvalue` and
`Elliptic.tendsto_eigenvalue_atTop`. -/
def eigenvalue (n : ℕ) : ℝ := (eigenvalueSeq Ω hΩ a hsymm ha n)⁻¹

/-- The basis vector $e_n$ is an eigenvector of the solution operator: $T e_n = \mu_n e_n$ for every
$n$. -/
theorem solutionOperator_eigenbasis (n : ℕ) :
    solutionOperator Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)
      = eigenvalueSeq Ω hΩ a hsymm ha n • eigenbasis Ω hΩ hne a hsymm ha n :=
  ContinuousLinearMap.IsSymmetric.apply_eigenvectorHilbertBasis _ _ _ _ n

/-- The eigenvalues of the solution operator tend to $0$: $\mu_n \to 0$ as $n \to \infty$. -/
theorem tendsto_eigenvalueSeq_zero : Tendsto (eigenvalueSeq Ω hΩ a hsymm ha) atTop (𝓝 0) :=
  ContinuousLinearMap.IsSymmetric.tendsto_eigenvalueSeq_zero _ _

/-- The basis vectors are nonzero: $e_n \neq 0$ for every $n$. -/
theorem eigenbasis_ne_zero (n : ℕ) : eigenbasis Ω hΩ hne a hsymm ha n ≠ 0 :=
  (eigenbasis Ω hΩ hne a hsymm ha).orthonormal.ne_zero n

include hne in
/-- If $\Omega$ is nonempty, the eigenvalues of the solution operator are positive: $\mu_n > 0$ for
every $n$.

The proof: $\mu_n = \langle T e_n, e_n \rangle_{L^2} \ge 0$ because $T$ is positive, and
$\mu_n \neq 0$ because $T$ is injective. -/
theorem eigenvalueSeq_pos (n : ℕ) : 0 < eigenvalueSeq Ω hΩ a hsymm ha n := by
  have h1 := inner_solutionOperator_nonneg Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)
  rw [solutionOperator_eigenbasis, inner_smul_left, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq, (eigenbasis Ω hΩ hne a hsymm ha).orthonormal.1 n, one_pow,
    mul_one] at h1
  refine lt_of_le_of_ne h1 fun h0 ↦ eigenbasis_ne_zero Ω hΩ hne a hsymm ha n ?_
  have h2 := solutionOperator_eigenbasis Ω hΩ hne a hsymm ha n
  rw [← h0, zero_smul] at h2
  exact LinearMap.ker_eq_bot'.1 (solutionOperator_ker_eq_bot Ω a ha) _ h2

include hne in
/-- If $\Omega$ is nonempty, the eigenvalues of the solution operator are nonincreasing:
$\mu_{n+1} \le \mu_n$ for every $n$. -/
theorem eigenvalueSeq_antitone : Antitone (eigenvalueSeq Ω hΩ a hsymm ha) := fun m n hmn ↦ by
  have h : |eigenvalueSeq Ω hΩ a hsymm ha n| ≤ |eigenvalueSeq Ω hΩ a hsymm ha m| :=
    ContinuousLinearMap.IsSymmetric.eigenvalueSeq_antitone _ _ hmn
  rwa [abs_of_pos (eigenvalueSeq_pos Ω hΩ hne a hsymm ha n),
    abs_of_pos (eigenvalueSeq_pos Ω hΩ hne a hsymm ha m)] at h

include hne in
/-- If $\Omega$ is nonempty, the eigenvalues are positive: $\lambda_n > 0$ for every $n$. This is
part of Theorem 9.31 of [brezis2011functional]. -/
theorem eigenvalue_pos (n : ℕ) : 0 < eigenvalue Ω hΩ a hsymm ha n :=
  inv_pos.2 (eigenvalueSeq_pos Ω hΩ hne a hsymm ha n)

include hne in
/-- If $\Omega$ is nonempty, the eigenvalues are nondecreasing: $\lambda_n \le \lambda_m$ for
$n \le m$. -/
theorem monotone_eigenvalue : Monotone (eigenvalue Ω hΩ a hsymm ha) := fun _ n hmn ↦
  inv_anti₀ (eigenvalueSeq_pos Ω hΩ hne a hsymm ha n)
    (eigenvalueSeq_antitone Ω hΩ hne a hsymm ha hmn)

include hne in
/-- If $\Omega$ is nonempty, $\lambda_n \to +\infty$ as $n \to \infty$. This is part of Theorem 9.31
of [brezis2011functional]. -/
theorem tendsto_eigenvalue_atTop : Tendsto (eigenvalue Ω hΩ a hsymm ha) atTop atTop := by
  have h1 : Tendsto (eigenvalueSeq Ω hΩ a hsymm ha) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_eigenvalueSeq_zero Ω hΩ a hsymm ha,
      Eventually.of_forall fun n ↦ eigenvalueSeq_pos Ω hΩ hne a hsymm ha n⟩
  exact tendsto_inv_nhdsGT_zero.comp h1

/-- The **eigenfunctions** as elements of $H^1_0(\Omega)$: $u_n = \lambda_n \, S e_n$, where
$S e_n \in H^1_0(\Omega)$ is the solution with datum $e_n$.

The function of $u_n$ is $e_n$ (`Elliptic.fnL_eigenfunction`), and $a(u_n, \varphi) = \lambda_n
\langle e_n, \varphi \rangle_{L^2}$ for every $\varphi \in H^1_0(\Omega)$
(`Elliptic.form_eigenfunction`). -/
def eigenfunction (n : ℕ) : SobolevEuclideanZero (d + 1) 1 2 Ω :=
  eigenvalue Ω hΩ a hsymm ha n • solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)

/-- The function of the eigenfunction $u_n \in H^1_0(\Omega)$ in $L^2(\Omega)$ is the basis vector
$e_n$.

The proof is $T(\lambda_n e_n) = \lambda_n \mu_n e_n = e_n$. -/
theorem fnL_eigenfunction (n : ℕ) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (eigenfunction Ω hΩ hne a hsymm ha n) = eigenbasis Ω hΩ hne a hsymm ha n := by
  have h1 : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume (solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n))
      = eigenvalueSeq Ω hΩ a hsymm ha n • eigenbasis Ω hΩ hne a hsymm ha n :=
    solutionOperator_eigenbasis Ω hΩ hne a hsymm ha n
  calc SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (eigenfunction Ω hΩ hne a hsymm ha n)
      = eigenvalue Ω hΩ a hsymm ha n • SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
          (solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)) :=
        (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume).map_smul _ _
    _ = eigenvalue Ω hΩ a hsymm ha n
        • (eigenvalueSeq Ω hΩ a hsymm ha n • eigenbasis Ω hΩ hne a hsymm ha n) :=
        congrArg (fun x ↦ eigenvalue Ω hΩ a hsymm ha n • x) h1
    _ = eigenbasis Ω hΩ hne a hsymm ha n := by
        rw [smul_smul, eigenvalue, inv_mul_cancel₀ (eigenvalueSeq_pos Ω hΩ hne a hsymm ha n).ne',
          one_smul]

/-- The function of the eigenfunction $u_n$, as an element of $H^1(\Omega)$, agrees with $e_n$
almost everywhere on $\Omega$. -/
theorem fn_eigenfunction (n : ℕ) :
    SobolevMultiIndex.fn (eigenfunction Ω hΩ hne a hsymm ha n : SobolevEuclidean (d + 1) 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        eigenbasis Ω hΩ hne a hsymm ha n := by
  rw [← fnL_eigenfunction Ω hΩ hne a hsymm ha n]
  exact Filter.EventuallyEq.refl _ _

/-- The **weak eigenvalue equation** (83) for the form $a$: for every $n$ and every
$\varphi \in H^1_0(\Omega)$,
$$a(u_n, \varphi) = \lambda_n \langle e_n, \varphi \rangle_{L^2}.$$

This is (83) of Theorem 9.31 of [brezis2011functional], for a general form $a$. -/
theorem form_eigenfunction (n : ℕ) (φ : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    a (eigenfunction Ω hΩ hne a hsymm ha n) φ
      = eigenvalue Ω hΩ a hsymm ha n * ⟪eigenbasis Ω hΩ hne a hsymm ha n,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume φ⟫_ℝ :=
  calc a (eigenfunction Ω hΩ hne a hsymm ha n) φ
      = eigenvalue Ω hΩ a hsymm ha n
        * a (solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n)) φ :=
        SesqForm.apply_coe_smul_left a _ _ _ _
    _ = eigenvalue Ω hΩ a hsymm ha n
        * loadL Ω (SobolevEuclideanZero (d + 1) 1 2 Ω) (eigenbasis Ω hΩ hne a hsymm ha n) φ :=
        congrArg (fun x ↦ eigenvalue Ω hΩ a hsymm ha n * x)
          (restrict_apply_solutionMap Ω a ha (eigenbasis Ω hΩ hne a hsymm ha n) φ)
    _ = _ := rfl

/-- For every $n$ there is $u \in H^1_0(\Omega)$ whose function is $e_n$ and which satisfies $a(u,
\varphi) = \lambda_n \langle e_n, \varphi \rangle_{L^2}$ for every $\varphi \in H^1_0(\Omega)$.

This is the existential form of (83) of [brezis2011functional] for the form $a$. The element $u$
is `Elliptic.eigenfunction`. -/
theorem eigenbasis_mem_sobolevZero (n : ℕ) :
    ∃ u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u
        = eigenbasis Ω hΩ hne a hsymm ha n ∧
      ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, a u φ
        = eigenvalue Ω hΩ a hsymm ha n * ⟪eigenbasis Ω hΩ hne a hsymm ha n,
          SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume φ⟫_ℝ :=
  ⟨eigenfunction Ω hΩ hne a hsymm ha n, (eigenfunction Ω hΩ hne a hsymm ha n).2,
    fnL_eigenfunction Ω hΩ hne a hsymm ha n,
    fun φ hφ ↦ form_eigenfunction Ω hΩ hne a hsymm ha n ⟨φ, hφ⟩⟩

end Eigenbasis

/-! ### Theorem 9.31: the Dirichlet eigenfunctions of $-\Delta$ -/

section Dirichlet

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- **Poincaré's inequality** as coercivity of the Dirichlet form. Let $R \ge 0$ and
$\Omega \subseteq B(0, R)$. Then the Dirichlet form restricted to $H^1_0(\Omega)$ is coercive
with constant $(1 + (2R)^2)^{-1}$:
$$\int_\Omega |\nabla v|^2 \ge \frac{1}{1 + (2R)^2} \|v\|_{H^1}^2 \qquad \text{for all } v \in
  H^1_0(\Omega).$$

The proof uses `SobolevEuclideanZero.norm_le_gradNorm` (Corollary 9.19 of
[brezis2011functional]) in the form `Elliptic.norm_sq_le_dirichletForm_self`. -/
theorem dirichletForm_restrict_isCoerciveWith {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) :
    ((dirichletForm Ω).restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoerciveWith
      (1 + (2 * R) ^ 2)⁻¹ := by
  intro v
  rw [RCLike.re_to_real, SesqForm.restrict_apply, ← Submodule.norm_coe]
  have hpos : (0 : ℝ) < 1 + (2 * R) ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hpos]
  exact norm_sq_le_dirichletForm_self hR hΩ v.2

/-- If $\Omega$ is bounded, the Dirichlet form $\int_\Omega \nabla u \cdot \nabla v$ is coercive on
$H^1_0(\Omega)$.

This is Poincaré's inequality. It is the coercivity hypothesis of the solution operator and of
`Elliptic.eigenbasis` for the Dirichlet form. -/
theorem dirichletForm_restrict_isCoercive
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ((dirichletForm Ω).restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoercive := by
  obtain ⟨R, hR0, hR⟩ := hΩ.subset_ball_lt 0 0
  exact ⟨_, by positivity, dirichletForm_restrict_isCoerciveWith Ω hR0.le hR⟩

variable (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- The **Dirichlet eigenbasis** of $-\Delta$. Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be
a bounded nonempty open set. This is the Hilbert basis $(e_n)$ of $L^2(\Omega)$ of the
eigenfunctions of the Dirichlet problem for $-\Delta$.

Each $e_n$ is the function of `Elliptic.dirichletEigenfunction Ω hΩ hne n` $\in H^1_0(\Omega)$.
That element solves
$$\int_\Omega \nabla e_n \cdot \nabla \varphi = \lambda_n \int_\Omega e_n \varphi \qquad
  \text{for all } \varphi \in H^1_0(\Omega),$$
which is (83) (`Elliptic.dirichletForm_dirichletEigenfunction`), with the eigenvalue
$\lambda_n$ = `Elliptic.dirichletEigenvalue Ω hΩ n`. The eigenvalues are positive and tend to
$+\infty$. This is the basis of Theorem 9.31 of [brezis2011functional].

The definition is `Elliptic.eigenbasis` for the Dirichlet form, which is Hermitian, and coercive
on $H^1_0(\Omega)$ by Poincaré's inequality. -/
def dirichletEigenbasis :
    HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :=
  eigenbasis Ω hΩ.measure_lt_top.ne hne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- The **Dirichlet eigenvalues** $\lambda_n$ of $-\Delta$ on a bounded open set $\Omega$: the
eigenvalues `Elliptic.eigenvalue` of the Dirichlet form.

When $\Omega$ is nonempty they are positive (`Elliptic.dirichletEigenvalue_pos`), nondecreasing
(`Elliptic.monotone_dirichletEigenvalue`) and tend to $+\infty$
(`Elliptic.tendsto_dirichletEigenvalue_atTop`). These are the eigenvalues of Theorem 9.31 of
[brezis2011functional]. -/
def dirichletEigenvalue : ℕ → ℝ :=
  eigenvalue Ω hΩ.measure_lt_top.ne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- The **Dirichlet eigenfunctions** as elements of $H^1_0(\Omega)$: the element
$u_n \in H^1_0(\Omega)$ whose function is $e_n$ = `Elliptic.dirichletEigenbasis Ω hΩ hne n`. It
is `Elliptic.eigenfunction` for the Dirichlet form. -/
def dirichletEigenfunction (n : ℕ) : SobolevEuclideanZero (d + 1) 1 2 Ω :=
  eigenfunction Ω hΩ.measure_lt_top.ne hne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ) n

include hne in
/-- If $\Omega$ is bounded and nonempty, the Dirichlet eigenvalues are positive: $\lambda_n > 0$ for
every $n$. This is part of Theorem 9.31 of [brezis2011functional]. -/
theorem dirichletEigenvalue_pos (n : ℕ) : 0 < dirichletEigenvalue Ω hΩ n :=
  eigenvalue_pos Ω hΩ.measure_lt_top.ne hne _ _ _ n

include hne in
/-- If $\Omega$ is bounded and nonempty, the Dirichlet eigenvalues are nondecreasing:
$\lambda_n \le \lambda_m$ for $n \le m$. -/
theorem monotone_dirichletEigenvalue : Monotone (dirichletEigenvalue Ω hΩ) :=
  monotone_eigenvalue Ω hΩ.measure_lt_top.ne hne _ _ _

include hne in
/-- If $\Omega$ is bounded and nonempty, the Dirichlet eigenvalues tend to $+\infty$. This is part
of Theorem 9.31 of [brezis2011functional]. -/
theorem tendsto_dirichletEigenvalue_atTop : Tendsto (dirichletEigenvalue Ω hΩ) atTop atTop :=
  tendsto_eigenvalue_atTop Ω hΩ.measure_lt_top.ne hne _ _ _

/-- The function of the Dirichlet eigenfunction $u_n \in H^1_0(\Omega)$ in $L^2(\Omega)$ is the
basis vector $e_n$. In particular $e_n \in H^1_0(\Omega)$. -/
theorem fnL_dirichletEigenfunction (n : ℕ) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (dirichletEigenfunction Ω hΩ hne n) = dirichletEigenbasis Ω hΩ hne n :=
  fnL_eigenfunction Ω hΩ.measure_lt_top.ne hne _ _ _ n

/-- The function of the Dirichlet eigenfunction $u_n$, as an element of $H^1(\Omega)$, agrees with
$e_n$ almost everywhere on $\Omega$. -/
theorem fn_dirichletEigenfunction (n : ℕ) :
    SobolevMultiIndex.fn (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        dirichletEigenbasis Ω hΩ hne n :=
  fn_eigenfunction Ω hΩ.measure_lt_top.ne hne _ _ _ n

/-- The **weak eigenvalue equation** (83) of Theorem 9.31 of [brezis2011functional]: for every $n$
and every $\varphi \in H^1_0(\Omega)$,
$$\int_\Omega \nabla u_n \cdot \nabla \varphi = \lambda_n \int_\Omega e_n \varphi,$$
where $u_n \in H^1_0(\Omega)$ is the Dirichlet eigenfunction with function $e_n$. -/
theorem dirichletForm_dirichletEigenfunction (n : ℕ) (φ : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n) φ
      = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume φ⟫_ℝ :=
  form_eigenfunction Ω hΩ.measure_lt_top.ne hne _ _ _ n φ

/-- For every $n$ there is $u \in H^1_0(\Omega)$ whose function is $e_n$ and which satisfies
$\int_\Omega \nabla u \cdot \nabla \varphi = \lambda_n \int_\Omega e_n \varphi$ for every
$\varphi \in H^1_0(\Omega)$. This is the existential form of (83) of [brezis2011functional]. -/
theorem dirichletEigenbasis_mem_sobolevZero (n : ℕ) :
    ∃ u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u
        = dirichletEigenbasis Ω hΩ hne n ∧
      ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω u φ
        = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
          SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume φ⟫_ℝ :=
  eigenbasis_mem_sobolevZero Ω hΩ.measure_lt_top.ne hne _ _ _ n

end Dirichlet

/-! ### The classical eigenvalue equation for a $C^2$ eigenfunction -/

section Classical

open Laplacian

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-- The **classical eigenvalue equation**. Let $\Omega \subseteq \mathbb{R}^N$ be open, let
$U \in H^1(\Omega)$, and let $\lambda \in \mathbb{R}$. Assume that
$$\int_\Omega \nabla U \cdot \nabla V = \lambda \int_\Omega U V$$
for every element $V \in H^1(\Omega)$ whose function agrees almost everywhere on $\Omega$ with a
test function. Assume also that the function of $U$ agrees almost everywhere on $\Omega$ with a
function $u$ of class $C^2$ on $\Omega$. Then $-\Delta u(x) = \lambda u(x)$ at every point
$x \in \Omega$.

This is the reading of "$-\Delta e_n = \lambda_n e_n$ in $\Omega$" of Theorem 9.31 of
[brezis2011functional] for the smooth representative of $e_n$. The weak equation says that $U$
solves $-\Delta U + U = (\lambda + 1) U$ weakly. Step D of §9.5, Example 1
(`Elliptic.laplacian_ae_eq_of_forall_testFunction`) then gives $-\Delta u + u = (\lambda + 1) u$
almost everywhere on $\Omega$. Both sides are continuous on the open set $\Omega$, so they agree
everywhere (`MeasureTheory.Measure.eqOn_open_of_ae_eq`). The Laplacian $\Delta$ is Mathlib's. -/
theorem laplacian_eq_of_eigenfunction {U : SobolevEuclidean N 1 2 Ω} {lam : ℝ}
    (hUw : ∀ V ∈ SobolevMultiIndex.testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume, dirichletForm Ω U V
        = lam * ⟪SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          U, SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
            V⟫_ℝ)
    {u : EuclideanSpace ℝ (Fin N) → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) :
    ∀ x ∈ Ω, -Δ u x = lam * u x := by
  have hΩo := Ω.isOpen
  obtain ⟨f, hf⟩ : ∃ f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      f = (lam + 1) • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
        volume U := ⟨_, rfl⟩
  have hUw' : ∀ V ∈ SobolevMultiIndex.testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume, laplaceForm Ω U V = load Ω f V := fun V hV ↦ by
    rw [laplaceForm_apply_eq_dirichletForm_add, hUw V hV, load_apply_inner, hf, inner_smul_left,
      RCLike.conj_to_real, SobolevMultiIndex.fnL_eq_weakDeriv_zero,
      SobolevMultiIndex.fnL_eq_weakDeriv_zero]
    ring
  have h1 := laplacian_ae_eq_of_forall_testFunction Ω hUw' hu hU
  have h2 : (f : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ (lam + 1) * u x := by
    rw [hf]
    filter_upwards [Lp.coeFn_smul (lam + 1) (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U), hU] with x hx hx'
    rw [hx, Pi.smul_apply, smul_eq_mul, SobolevMultiIndex.fnL_apply, hx']
  have h3 : EqOn (fun x ↦ -Δ u x + u x) (fun x ↦ (lam + 1) * u x) Ω :=
    Measure.eqOn_open_of_ae_eq (h1.trans h2) hΩo
      ((continuousOn_laplacian Ω hu).neg.add
        (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn)
      ((hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn.const_smul (lam + 1))
  intro x hx
  have := h3 hx
  simp only at this
  linarith

end Classical

/-! ### Transporting a Hilbert basis along the eigenvalue equation -/

section Transport

variable {ι E L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup L]
  [InnerProductSpace ℝ L]

/-- Let $b$ be a Hilbert basis of a real inner product space $L$, and let $x \in L$ with
$\langle b_i, x \rangle = 0$ for every $i$. Then $x = 0$. -/
theorem _root_.HilbertBasis.eq_zero_of_forall_inner_eq_zero (b : HilbertBasis ι ℝ L) {x : L}
    (h : ∀ i, ⟪b i, x⟫_ℝ = 0) : x = 0 := by
  have hr : b.repr x = 0 := by
    ext i
    rw [b.repr_apply_apply, h i, lp.coeFn_zero, Pi.zero_apply]
  simpa using congrArg b.repr.symm hr

/-- Let $(v_i)$ be a family in a real inner product space $E$ such that only $0$ is orthogonal to
every $v_i$. Then the orthogonal complement of the span of $(v_i)$ is $\{0\}$. -/
theorem _root_.Submodule.orthogonal_span_range_eq_bot_of_forall {v : ι → E}
    (h : ∀ x, (∀ i, ⟪v i, x⟫_ℝ = 0) → x = 0) : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  exact h x fun i ↦ (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Let $(u_i)$ be a family in a real inner product space $E$ and let $c_i > 0$, with
$\langle u_i, u_i \rangle = c_i$ for every $i$ and $\langle u_i, u_j \rangle = 0$ for
$i \neq j$. Then the family $(c_i^{-1/2} u_i)$ is orthonormal. -/
theorem _root_.orthonormal_inv_sqrt_smul {u : ι → E} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (hd : ∀ i, ⟪u i, u i⟫_ℝ = c i) (ho : ∀ i j, i ≠ j → ⟪u i, u j⟫_ℝ = 0) :
    Orthonormal ℝ fun i ↦ (√(c i))⁻¹ • u i := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  split_ifs with hij
  · subst hij
    rw [hd, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt (hc i).le, inv_mul_cancel₀ (hc i).ne']
  · rw [ho i j hij, mul_zero, mul_zero]

variable [CompleteSpace E]

/-- **Transport of a Hilbert basis along a weak eigenvalue equation.** Let $E$ be a real Hilbert
space and $L$ a real inner product space. Let $b$ be a Hilbert basis of $L$, let $T : E \to L$
be linear and injective, and let $(u_i)$ be a family in $E$ and $c_i > 0$ such that
$T u_i = b_i$ and
$$\langle u_i, x \rangle_E = c_i \langle b_i, T x \rangle_L \qquad \text{for all } i \text{ and
  all } x \in E.$$
Then $(u_i / \sqrt{c_i})$ is a Hilbert basis of $E$.

The family is orthonormal because $\langle u_i, u_j \rangle_E = c_i \langle b_i, b_j \rangle_L =
c_i \delta_{ij}$. It is complete because $x \perp u_i$ for all $i$ gives $Tx \perp b_i$ for all
$i$, so $Tx = 0$ and $x = 0$. This is the argument of Remark 28 in Chapter 9 of
[brezis2011functional], with $E = H^1_0(\Omega)$, $L = L^2(\Omega)$, $T$ the inclusion, $b$ the
Dirichlet eigenbasis, and $c_i = \lambda_i$ or $c_i = \lambda_i + 1$. -/
def _root_.HilbertBasis.ofInnerEqMul (b : HilbertBasis ι ℝ L) (T : E →ₗ[ℝ] L)
    (hT : Function.Injective T) (u : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hTu : ∀ i, T (u i) = b i) (h : ∀ i x, ⟪u i, x⟫_ℝ = c i * ⟪b i, T x⟫_ℝ) :
    HilbertBasis ι ℝ E :=
  HilbertBasis.mkOfOrthogonalEqBot
    (orthonormal_inv_sqrt_smul hc
      (fun i ↦ by rw [h, hTu, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow, mul_one])
      fun i j hij ↦ by rw [h, hTu, b.orthonormal.2 hij, mul_zero])
    (Submodule.orthogonal_span_range_eq_bot_of_forall fun x hx ↦ by
      refine hT ((b.eq_zero_of_forall_inner_eq_zero fun i ↦ ?_).trans (map_zero T).symm)
      have hi := hx i
      rw [inner_smul_left, RCLike.conj_to_real, h, mul_eq_zero, mul_eq_zero] at hi
      rcases hi with hi | hi | hi
      · exact absurd hi (inv_ne_zero (Real.sqrt_pos.2 (hc i)).ne')
      · exact absurd hi (hc i).ne'
      · exact hi)

/-- The vectors of the Hilbert basis `HilbertBasis.ofInnerEqMul` are $u_i / \sqrt{c_i}$. -/
@[simp]
theorem _root_.HilbertBasis.coe_ofInnerEqMul (b : HilbertBasis ι ℝ L) (T : E →ₗ[ℝ] L)
    (hT : Function.Injective T) (u : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hTu : ∀ i, T (u i) = b i) (h : ∀ i x, ⟪u i, x⟫_ℝ = c i * ⟪b i, T x⟫_ℝ) :
    ⇑(HilbertBasis.ofInnerEqMul b T hT u c hc hTu h) = fun i ↦ (√(c i))⁻¹ • u i :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- **Transport of a Hilbert basis to an energy space.** Let $E$ be a real Hilbert space, $L$ a real
inner product space, and $A$ a bounded symmetric coercive operator on $E$. Let $b$ be a Hilbert
basis of $L$, let $T : E \to L$ be linear and injective, and let $(u_i)$ be a family in $E$ and
$c_i > 0$ such that $T u_i = b_i$ and
$$\langle A u_i, x \rangle_E = c_i \langle b_i, T x \rangle_L \qquad \text{for all } i \text{
  and all } x \in E.$$
Then $(u_i / \sqrt{c_i})$ is a Hilbert basis of the energy space `WithEnergy A _` of $A$, which
is $E$ with the inner product $\langle A u, x \rangle_E$.

The proof is `HilbertBasis.ofInnerEqMul` for the energy inner product. This is the first clause
of Remark 28 in Chapter 9 of [brezis2011functional] in abstract form, with $E = H^1_0(\Omega)$,
$A$ the operator of the form $a$, and $\langle A u_i, x \rangle = a(u_i, x) = \lambda_i \langle
e_i, x \rangle_{L^2}$. -/
def _root_.HilbertBasis.ofInnerEqMulEnergy (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetricCoercive)
    (b : HilbertBasis ι ℝ L) (T : E →ₗ[ℝ] L) (hT : Function.Injective T) (u : ι → E) (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) (hTu : ∀ i, T (u i) = b i)
    (h : ∀ i x, ⟪A (u i), x⟫_ℝ = c i * ⟪b i, T x⟫_ℝ) :
    HilbertBasis ι ℝ (WithEnergy A.toLinearMap hA) :=
  haveI := WithEnergy.instCompleteSpace_of_continuousLinearMap hA
  HilbertBasis.ofInnerEqMul b (T ∘ₗ (WithEnergy.equiv _ _).symm.toLinearMap)
    (hT.comp (WithEnergy.equiv _ _).symm.injective) (fun i ↦ WithEnergy.equiv _ _ (u i)) c hc
    (fun i ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hTu])
    (fun i x ↦ h i _)

/-- The vectors of the Hilbert basis `HilbertBasis.ofInnerEqMulEnergy` are $u_i / \sqrt{c_i}$, read
in the energy space. -/
@[simp]
theorem _root_.HilbertBasis.coe_ofInnerEqMulEnergy (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetricCoercive) (b : HilbertBasis ι ℝ L) (T : E →ₗ[ℝ] L)
    (hT : Function.Injective T) (u : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hTu : ∀ i, T (u i) = b i) (h : ∀ i x, ⟪A (u i), x⟫_ℝ = c i * ⟪b i, T x⟫_ℝ) :
    ⇑(HilbertBasis.ofInnerEqMulEnergy A hA b T hT u c hc hTu h)
      = fun i ↦ (√(c i))⁻¹ • WithEnergy.equiv _ _ (u i) :=
  haveI := WithEnergy.instCompleteSpace_of_continuousLinearMap hA
  HilbertBasis.coe_ofInnerEqMul _ _ _ _ _ _ _ _

end Transport

/-! ### The operator of a form restricted to $H^1_0(\Omega)$ -/

section RestrictOperator

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))
  (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω)) (hsymm : a.IsHermitian)
  (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)

/-- The **operator of a form restricted to $H^1_0(\Omega)$**: the bounded operator $A$ on
$H^1_0(\Omega)$ with $\langle A u, v \rangle_{H^1} = a(u, v)$ for all $u, v \in H^1_0(\Omega)$.

It is `SesqForm.toOperator` of the restricted form. When $a$ is Hermitian and coercive on
$H^1_0(\Omega)$, its energy space `WithEnergy` is $H^1_0(\Omega)$ with the inner product
$a(u, v)$. -/
def restrictOperator :
    SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclideanZero N 1 2 Ω :=
  SesqForm.toOperator (a.restrict (SobolevEuclideanZero N 1 2 Ω))

/-- The operator of the restricted form satisfies $\langle A u, v \rangle_{H^1} = a(u, v)$ for all
$u, v \in H^1_0(\Omega)$. -/
theorem inner_restrictOperator (u v : SobolevEuclideanZero N 1 2 Ω) :
    ⟪restrictOperator Ω a u, v⟫_ℝ = a u v :=
  SesqForm.inner_toOperator _ u v

include hsymm ha in
/-- If the form $a$ is Hermitian and coercive on $H^1_0(\Omega)$, its operator $A$ on
$H^1_0(\Omega)$ is symmetric and coercive. Thus $H^1_0(\Omega)$ with the inner product $a(u, v)$
is the energy space `WithEnergy (Elliptic.restrictOperator Ω a) _`. -/
theorem restrictOperator_isSymmetricCoercive :
    (restrictOperator Ω a).toLinearMap.IsSymmetricCoercive :=
  (hsymm.restrict _).isSymmetricCoercive_toOperator ha

/-- If the form $a$ is Hermitian and coercive on $H^1_0(\Omega)$, the energy space of its operator
on $H^1_0(\Omega)$ is complete.

The proof is `WithEnergy.instCompleteSpace_of_continuousLinearMap`. -/
theorem completeSpace_withEnergy_restrictOperator :
    CompleteSpace (WithEnergy (restrictOperator Ω a).toLinearMap
      (restrictOperator_isSymmetricCoercive Ω a hsymm ha)) :=
  WithEnergy.instCompleteSpace_of_continuousLinearMap _

/-- The **operator of the Dirichlet form** on $H^1_0(\Omega)$: the bounded operator $A$ on
$H^1_0(\Omega)$ with
$$\langle A u, v \rangle_{H^1} = \int_\Omega \nabla u \cdot \nabla v \qquad \text{for all } u, v
  \in H^1_0(\Omega)$$
(`Elliptic.inner_dirichletOperator`).

For a bounded $\Omega$ it is symmetric and coercive
(`Elliptic.dirichletOperator_isSymmetricCoercive`). Its energy space
`WithEnergy (Elliptic.dirichletOperator Ω) _` is $H^1_0(\Omega)$ with the scalar product
$\int_\Omega \nabla u \cdot \nabla v$ of Remark 28 in Chapter 9 of [brezis2011functional]. It is
the first factor of the phase space of the wave equation, whose energy $\int_\Omega |\nabla
u|^2 = \langle A u, u \rangle_{H^1}$ is (32) of §10.3 of [brezis2011functional]. -/
def dirichletOperator :
    SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclideanZero N 1 2 Ω :=
  restrictOperator Ω (dirichletForm Ω)

/-- The operator $A$ of the Dirichlet form satisfies $\langle A u, v \rangle_{H^1} = \int_\Omega
\nabla u \cdot \nabla v$ for all $u, v \in H^1_0(\Omega)$. -/
theorem inner_dirichletOperator (u v : SobolevEuclideanZero N 1 2 Ω) :
    ⟪dirichletOperator Ω u, v⟫_ℝ = dirichletForm Ω u v :=
  inner_restrictOperator Ω _ u v

/-- The operator $A$ of the Dirichlet form is symmetric: $\langle A u, v \rangle_{H^1} = \langle A
v, u \rangle_{H^1}$ for all $u, v \in H^1_0(\Omega)$. -/
theorem inner_dirichletOperator_comm (u v : SobolevEuclideanZero N 1 2 Ω) :
    ⟪dirichletOperator Ω u, v⟫_ℝ = ⟪dirichletOperator Ω v, u⟫_ℝ := by
  rw [inner_dirichletOperator, inner_dirichletOperator, dirichletForm_isHermitian Ω _ _,
    conj_trivial]

end RestrictOperator

/-! ### The energy basis of a symmetric coercive form (Remark 28, first clause) -/

section EnergyBasis

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
  (a : SesqForm ℝ (SobolevEuclidean (d + 1) 1 2 Ω)) (hsymm : a.IsHermitian)
  (ha : (a.restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoercive)

/-- The **energy eigenbasis** of a symmetric coercive form. Let $\Omega \subseteq \mathbb{R}^N$,
$N = d + 1$, be a nonempty open set of finite measure, and let $a$ be a bounded form on
$H^1(\Omega)$ that is Hermitian and coercive on $H^1_0(\Omega)$. This is the Hilbert basis
$(u_n / \sqrt{\lambda_n})$ of $H^1_0(\Omega)$ with the inner product $a(u, v)$, where $u_n$ are
the eigenfunctions and $\lambda_n$ the eigenvalues of $a$.

This is the first clause of Remark 28 in Chapter 9 of [brezis2011functional], for a general
form. The basis lives on the energy space `WithEnergy (Elliptic.restrictOperator Ω a) _`. It is
`HilbertBasis.ofInnerEqMulEnergy` with the weak equation $a(u_n, x) = \lambda_n \langle e_n, x
\rangle_{L^2}$ (`Elliptic.form_eigenfunction`). -/
def energyEigenbasis :
    HilbertBasis ℕ ℝ (WithEnergy (restrictOperator Ω a).toLinearMap
      (restrictOperator_isSymmetricCoercive Ω a hsymm ha)) :=
  HilbertBasis.ofInnerEqMulEnergy (restrictOperator Ω a)
    (restrictOperator_isSymmetricCoercive Ω a hsymm ha) (eigenbasis Ω hΩ hne a hsymm ha)
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume).toLinearMap
    SobolevMultiIndexZero.fnL_injective (eigenfunction Ω hΩ hne a hsymm ha)
    (eigenvalue Ω hΩ a hsymm ha) (eigenvalue_pos Ω hΩ hne a hsymm ha)
    (fnL_eigenfunction Ω hΩ hne a hsymm ha)
    (fun n x ↦ (inner_restrictOperator Ω a _ x).trans (form_eigenfunction Ω hΩ hne a hsymm ha n x))

/-- The vectors of the energy eigenbasis are $u_n / \sqrt{\lambda_n}$, read in the energy space. -/
theorem coe_energyEigenbasis :
    ⇑(energyEigenbasis Ω hΩ hne a hsymm ha) = fun n ↦ (√(eigenvalue Ω hΩ a hsymm ha n))⁻¹
      • WithEnergy.equiv _ _ (eigenfunction Ω hΩ hne a hsymm ha n) :=
  HilbertBasis.coe_ofInnerEqMulEnergy _ _ _ _ _ _ _ _ _ _

end EnergyBasis

/-! ### Remark 28: the two bases of $H^1_0(\Omega)$ for the Dirichlet form -/

section SobolevZeroBasis

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- Let $\Omega$ be bounded and nonempty. Then the $H^1$ inner product of the Dirichlet
eigenfunction $u_n$ with any $x \in H^1_0(\Omega)$ is
$$\langle u_n, x \rangle_{H^1} = (\lambda_n + 1) \langle e_n, x \rangle_{L^2}.$$

The proof uses the weak equation (83) and the fact that the form of $-\Delta + 1$ is the $H^1$
inner product. -/
theorem inner_dirichletEigenfunction_left (n : ℕ) (x : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ⟪dirichletEigenfunction Ω hΩ hne n, x⟫_ℝ
      = (dirichletEigenvalue Ω hΩ n + 1) * ⟪dirichletEigenbasis Ω hΩ hne n,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume x⟫_ℝ :=
  calc ⟪dirichletEigenfunction Ω hΩ hne n, x⟫_ℝ
      = laplaceForm Ω (dirichletEigenfunction Ω hΩ hne n) x :=
        (laplaceForm_apply_eq_inner Ω _ _).symm
    _ = dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n) x
        + ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume (dirichletEigenfunction Ω hΩ hne n),
          SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume x⟫_ℝ :=
        laplaceForm_apply_eq_dirichletForm_add Ω _ _
    _ = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
          SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume x⟫_ℝ
        + ⟪dirichletEigenbasis Ω hΩ hne n,
          SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume x⟫_ℝ :=
        congrArg₂ (· + ·) (dirichletForm_dirichletEigenfunction Ω hΩ hne n x)
          (congrArg (fun y ↦ ⟪y, SobolevMultiIndexZero.fnL ℝ
            (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume x⟫_ℝ)
            (fnL_dirichletEigenfunction Ω hΩ hne n))
    _ = _ := by ring

/-- The **$H^1$ eigenbasis** of $H^1_0(\Omega)$. Let $\Omega$ be bounded and nonempty. This is the
Hilbert basis $(u_n / \sqrt{\lambda_n + 1})$ of $H^1_0(\Omega)$ for its $H^1$ inner product
$\int_\Omega (\nabla u \cdot \nabla v + uv)$, where $u_n$ are the Dirichlet eigenfunctions.

This is the second clause of Remark 28 in Chapter 9 of [brezis2011functional]. It is
`HilbertBasis.ofInnerEqMul` with $\langle u_n, x \rangle_{H^1} = (\lambda_n + 1) \langle e_n, x
\rangle_{L^2}$. -/
def sobolevZeroEigenbasis : HilbertBasis ℕ ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  HilbertBasis.ofInnerEqMul (dirichletEigenbasis Ω hΩ hne)
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume).toLinearMap
    SobolevMultiIndexZero.fnL_injective (dirichletEigenfunction Ω hΩ hne)
    (fun n ↦ dirichletEigenvalue Ω hΩ n + 1)
    (fun n ↦ by linarith [dirichletEigenvalue_pos Ω hΩ hne n])
    (fnL_dirichletEigenfunction Ω hΩ hne) (inner_dirichletEigenfunction_left Ω hΩ hne)

/-- The vectors of the $H^1$ eigenbasis are $u_n / \sqrt{\lambda_n + 1}$. -/
theorem coe_sobolevZeroEigenbasis :
    ⇑(sobolevZeroEigenbasis Ω hΩ hne)
      = fun n ↦ (√(dirichletEigenvalue Ω hΩ n + 1))⁻¹ • dirichletEigenfunction Ω hΩ hne n :=
  HilbertBasis.coe_ofInnerEqMul _ _ _ _ _ _ _ _

/-- Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded nonempty open set. Then there is
a Hilbert basis of $H^1_0(\Omega)$, for the scalar product
$\int_\Omega (\nabla u \cdot \nabla v + uv)$, whose $n$-th vector is
$u_n / \sqrt{\lambda_n + 1}$. Here $u_n \in H^1_0(\Omega)$ is the $n$-th Dirichlet
eigenfunction, with function $e_n$.

This is the second clause of Remark 28 in Chapter 9 of [brezis2011functional], which writes the
basis as $(e_n / \sqrt{\lambda_n + 1})$. The basis is `Elliptic.sobolevZeroEigenbasis`. -/
theorem hilbertBasis_sobolevZero :
    ∃ b : HilbertBasis ℕ ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω),
      ∀ n, b n = (√(dirichletEigenvalue Ω hΩ n + 1))⁻¹ • dirichletEigenfunction Ω hΩ hne n :=
  ⟨sobolevZeroEigenbasis Ω hΩ hne, fun n ↦ congrFun (coe_sobolevZeroEigenbasis Ω hΩ hne) n⟩

include hΩ in
/-- If $\Omega$ is bounded, the operator of the Dirichlet form on $H^1_0(\Omega)$ is symmetric and
coercive. Coercivity is Poincaré's inequality. -/
theorem dirichletOperator_isSymmetricCoercive :
    (dirichletOperator Ω).toLinearMap.IsSymmetricCoercive :=
  restrictOperator_isSymmetricCoercive Ω _ (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- The **Dirichlet energy eigenbasis**. Let $\Omega$ be bounded and nonempty. This is the Hilbert
basis $(u_n / \sqrt{\lambda_n})$ of $H^1_0(\Omega)$ for the scalar product
$\int_\Omega \nabla u \cdot \nabla v$, where $u_n$ are the Dirichlet eigenfunctions.

This is the first clause of Remark 28 in Chapter 9 of [brezis2011functional]. The basis lives on
the energy space `WithEnergy (Elliptic.dirichletOperator Ω) _`. -/
def dirichletEnergyEigenbasis :
    HilbertBasis ℕ ℝ (WithEnergy (dirichletOperator Ω).toLinearMap
      (dirichletOperator_isSymmetricCoercive Ω hΩ)) :=
  energyEigenbasis Ω hΩ.measure_lt_top.ne hne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- The vectors of the Dirichlet energy eigenbasis are $u_n / \sqrt{\lambda_n}$, read in the energy
space. -/
theorem coe_dirichletEnergyEigenbasis :
    ⇑(dirichletEnergyEigenbasis Ω hΩ hne) = fun n ↦ (√(dirichletEigenvalue Ω hΩ n))⁻¹
      • WithEnergy.equiv _ _ (dirichletEigenfunction Ω hΩ hne n) :=
  coe_energyEigenbasis Ω hΩ.measure_lt_top.ne hne (dirichletForm Ω) (dirichletForm_isHermitian Ω)
    (dirichletForm_restrict_isCoercive Ω hΩ)

/-- Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded nonempty open set. Then there is
a Hilbert basis of $H^1_0(\Omega)$, for the scalar product
$\int_\Omega \nabla u \cdot \nabla v$, whose $n$-th vector is $u_n / \sqrt{\lambda_n}$. Here
$u_n \in H^1_0(\Omega)$ is the $n$-th Dirichlet eigenfunction, with function $e_n$.

This is the first clause of Remark 28 in Chapter 9 of [brezis2011functional], which writes the
basis as $(e_n / \sqrt{\lambda_n})$. The space with this scalar product is the energy space
`WithEnergy (Elliptic.dirichletOperator Ω) _`, and the basis is
`Elliptic.dirichletEnergyEigenbasis`. -/
theorem hilbertBasis_energy :
    ∃ b : HilbertBasis ℕ ℝ (WithEnergy (dirichletOperator Ω).toLinearMap
      (dirichletOperator_isSymmetricCoercive Ω hΩ)),
      ∀ n, b n = (√(dirichletEigenvalue Ω hΩ n))⁻¹
        • WithEnergy.equiv _ _ (dirichletEigenfunction Ω hΩ hne n) :=
  ⟨dirichletEnergyEigenbasis Ω hΩ hne, fun n ↦ congrFun (coe_dirichletEnergyEigenbasis Ω hΩ hne) n⟩

end SobolevZeroBasis

/-! ### Remark 30: a general symmetric elliptic operator -/

section General

/-- The sum of two Hermitian forms is Hermitian. -/
theorem _root_.SesqForm.IsHermitian.add {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] {a b : SesqForm 𝕜 V} (ha : a.IsHermitian) (hb : b.IsHermitian) :
    (a + b).IsHermitian := fun u v ↦ by
  rw [add_apply, add_apply, add_apply, add_apply, map_add, ha u v, hb u v]

/-- A real multiple $c \, a$ of a Hermitian real form $a$ is Hermitian. -/
theorem _root_.SesqForm.IsHermitian.smul_real {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} (c : ℝ) (ha : a.IsHermitian) :
    (c • a).IsHermitian := fun u v ↦ by
  rw [smul_apply, smul_apply, smul_apply, smul_apply, conj_trivial, smul_eq_mul, smul_eq_mul,
    ha u v, conj_trivial]

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-- For a multi-index $\alpha$ of order at most $1$, the form $(u, v) \mapsto \langle
\partial^\alpha u, \partial^\alpha v \rangle_{L^2}$ on $H^1(\Omega)$ is Hermitian. -/
theorem pairing_id_isHermitian (α : MultiIndexLE (Fin N) 1) :
    (pairing Ω (ContinuousLinearMap.id ℝ _) α α).IsHermitian := fun u v ↦ by
  rw [conj_trivial]
  exact pairing_id_comm Ω α α u v

end General

section Remark30

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  {A : Fin (d + 1) → Fin (d + 1) →
    Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))} {α : ℝ}

/-- Remark 30 in Chapter 9 of [brezis2011functional], for a shifted form. Let
$\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a nonempty open set of finite measure, and let
$a_{ij}, a_0 \in L^\infty(\Omega)$. Let $a$ be a bounded form on $H^1(\Omega)$ that is Hermitian
and coercive on $H^1_0(\Omega)$, and let $\mu \in \mathbb{R}$ with
$$a(u, v) = \sum_{i,j} \int_\Omega a_{ij} \, \partial_i u \, \partial_j v + \int_\Omega a_0 u
  v + \mu \int_\Omega u v \qquad \text{for all } u, v \in H^1(\Omega).$$
Then there are a Hilbert basis $(e_n)$ of $L^2(\Omega)$ and real numbers $\lambda_n \to +\infty$
such that each $e_n$ is the function of some $u_n \in H^1_0(\Omega)$ with
$$\sum_{i,j} \int_\Omega a_{ij} \, \partial_i u_n \, \partial_j \varphi + \int_\Omega a_0 u_n
  \varphi = \lambda_n \int_\Omega e_n \varphi \qquad \text{for all } \varphi \in
  H^1_0(\Omega).$$

This is the spectral decomposition (84). The basis is the eigenbasis of $a$, and $\lambda_n$ is
the eigenvalue of $a$ minus $\mu$. The form with coefficients $a_{ij}$ and $a_0$ is
`Elliptic.generalForm Ω A 0 a₀`, without first-order terms. -/
theorem exists_hilbertBasis_eigen_of_shift
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    (a : SesqForm ℝ (SobolevEuclidean (d + 1) 1 2 Ω)) (hherm : a.IsHermitian)
    (hcoer : (a.restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)).IsCoercive) (μ : ℝ)
    (hkey : ∀ u v : SobolevEuclidean (d + 1) 1 2 Ω, a u v = generalForm Ω A 0 a₀ u v
      + μ * ⟪SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume u,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume v⟫_ℝ) :
    ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))))
      (lam : ℕ → ℝ), Tendsto lam atTop atTop ∧
      ∀ n, ∃ u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u
          = e n ∧
        ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, generalForm Ω A 0 a₀ u φ
          = lam n * ⟪e n, SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
            1 2 Ω volume φ⟫_ℝ := by
  refine ⟨eigenbasis Ω hΩ hne a hherm hcoer, fun n ↦ eigenvalue Ω hΩ a hherm hcoer n - μ,
    (tendsto_atTop_add_const_right _ (-μ) (tendsto_eigenvalue_atTop Ω hΩ hne a hherm hcoer)).congr
      fun n ↦ (sub_eq_add_neg _ _).symm, fun n ↦ ?_⟩
  refine ⟨eigenfunction Ω hΩ hne a hherm hcoer n, (eigenfunction Ω hΩ hne a hherm hcoer n).2,
    fnL_eigenfunction Ω hΩ hne a hherm hcoer n, fun φ hφ ↦ ?_⟩
  have h1 : a (eigenfunction Ω hΩ hne a hherm hcoer n) φ = eigenvalue Ω hΩ a hherm hcoer n
      * ⟪eigenbasis Ω hΩ hne a hherm hcoer n,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume φ⟫_ℝ :=
    form_eigenfunction Ω hΩ hne a hherm hcoer n ⟨φ, hφ⟩
  have h2 := hkey (eigenfunction Ω hΩ hne a hherm hcoer n) φ
  have h3 : ⟪SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
        volume (eigenfunction Ω hΩ hne a hherm hcoer n),
      SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ
      = ⟪eigenbasis Ω hΩ hne a hherm hcoer n,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume φ⟫_ℝ :=
    congrArg (fun y ↦ ⟪y, SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      1 2 Ω volume φ⟫_ℝ) (fnL_eigenfunction Ω hΩ hne a hherm hcoer n)
  rw [h3] at h2
  change _ = (eigenvalue Ω hΩ a hherm hcoer n - μ) * _
  linear_combination h1 - h2

/-- Remark 30 in Chapter 9 of [brezis2011functional]. Let $\Omega \subseteq \mathbb{R}^N$,
$N = d + 1$, be a nonempty open set of finite measure. Let $a_{ij} \in L^\infty(\Omega)$ be
symmetric, $a_{ij} = a_{ji}$, and satisfy the ellipticity condition (36) with a constant
$\alpha > 0$. Let $a_0 \in L^\infty(\Omega)$. Then there are a Hilbert basis $(e_n)$ of
$L^2(\Omega)$ and real numbers $\lambda_n \to +\infty$ such that each $e_n$ is the function of
some $u_n \in H^1_0(\Omega)$ with the spectral decomposition (84)
$$\sum_{i,j} \int_\Omega a_{ij} \, \partial_i u_n \, \partial_j \varphi + \int_\Omega a_0 u_n
  \varphi = \lambda_n \int_\Omega e_n \varphi \qquad \text{for all } \varphi \in
  H^1_0(\Omega).$$

[brezis2011functional] omits the symmetry hypothesis $a_{ij} = a_{ji}$. Without it the solution
operator is not self-adjoint. The numbers $\lambda_n$ need not be positive.

The proof applies `Elliptic.eigenbasis` to the shifted form, the sum of
`Elliptic.generalForm Ω A 0 a₀` and $\lambda_0 \langle \cdot, \cdot \rangle_{L^2}$. This form is
Hermitian (`Elliptic.generalForm_isHermitian_of_symm`), and coercive on $H^1_0(\Omega)$ for the
$\lambda_0$ of Gårding's inequality (`Elliptic.generalForm_garding_restrict_isCoercive`). Its
eigenvalues $\lambda'_n \to +\infty$ give $\lambda_n = \lambda'_n - \lambda_0$. The ellipticity
condition is `Elliptic.IsUniformlyElliptic`. -/
theorem exists_hilbertBasis_eigen_general
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    (hA : IsUniformlyElliptic Ω A α) (hsymm : ∀ i j, A i j = A j i) :
    ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))))
      (lam : ℕ → ℝ), Tendsto lam atTop atTop ∧
      ∀ n, ∃ u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u
          = e n ∧
        ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, generalForm Ω A 0 a₀ u φ
          = lam n * ⟪e n, SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
            1 2 Ω volume φ⟫_ℝ :=
  exists_hilbertBasis_eigen_of_shift Ω hΩ hne
    (generalForm Ω A 0 a₀ + ((∑ i : Fin (d + 1),
      ‖(0 : Fin (d + 1) → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) i‖)
        ^ 2 / (2 * α) + ‖a₀‖ + α / 2) • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0)
    ((generalForm_isHermitian_of_symm Ω A a₀ hsymm).add ((pairing_id_isHermitian Ω 0).smul_real _))
    (generalForm_garding_restrict_isCoercive Ω hA) _ (add_smul_pairing_apply Ω _ _)

end Remark30

/-! ### Theorem 9.31: the classical equation for a smooth representative of $e_n$ -/

section DirichletClassical

open Laplacian

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded nonempty open set, and let $u$ be
a function of class $C^2$ on $\Omega$ that agrees almost everywhere on $\Omega$ with the
Dirichlet eigenfunction $e_n$. Then $-\Delta u(x) = \lambda_n u(x)$ at every point
$x \in \Omega$.

This is the equation "$-\Delta e_n = \lambda_n e_n$ in $\Omega$" of Theorem 9.31 of
[brezis2011functional]. The proof is `Elliptic.laplacian_eq_of_eigenfunction` with the weak
equation (83). Interior regularity (Remark 25) gives the $C^\infty$ representative
(`Elliptic.dirichletEigenbasis_exists_contDiffOn`). -/
theorem laplacian_eq_dirichletEigenfunction (n : ℕ) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω)
    (hU : (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u) :
    ∀ x ∈ Ω, -Δ u x = dirichletEigenvalue Ω hΩ n * u x :=
  laplacian_eq_of_eigenfunction Ω (U := dirichletEigenfunction Ω hΩ hne n)
    (lam := dirichletEigenvalue Ω hΩ n)
    (fun V hV ↦ (dirichletForm_dirichletEigenfunction Ω hΩ hne n
      ⟨V, SobolevMultiIndexZero.testFunctions_le hV⟩).trans
      (congrArg (fun y ↦ dirichletEigenvalue Ω hΩ n * ⟪y, SobolevMultiIndex.fnL ℝ
        (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
        (fnL_dirichletEigenfunction Ω hΩ hne n).symm))
    hu ((fn_dirichletEigenfunction Ω hΩ hne n).trans hU)

end DirichletClassical


/-! ### Smoothness of the eigenfunctions: interior regularity and regularity up to the boundary -/

section Smoothness

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

open SobolevMultiIndex

/-- The weak eigenvalue equation against a test function, in terms of functions. Let
$U \in H^1(\Omega)$ and $\lambda \in \mathbb{R}$ satisfy $\int_\Omega \nabla U \cdot \nabla V =
\lambda \int_\Omega U V$ for every element $V \in H^1(\Omega)$ whose function agrees almost
everywhere on $\Omega$ with a test function. Then for every test function $\varphi$ on $\Omega$
$$\int_\Omega \sum_i \partial_i U \, \partial_i \varphi = \int_\Omega (\lambda U) \varphi.$$

This is the form of the hypothesis of the interior regularity theorem
`Elliptic.regularity_interior_higher`. -/
theorem integral_sum_weakDeriv_mul_fderiv_eq_of_eigenfunction {U : SobolevEuclidean N 1 2 Ω}
    {lam : ℝ}
    (hUw : ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω U V
        = lam * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
          fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, weakDeriv U (MultiIndexLE.single i) x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (lam • fn U) x * φ x := by
  obtain ⟨V, hV, hVφ⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
  have h1 := hUw V hV
  rw [dirichletForm_apply, L2.inner_eq_integral_mul, ← integral_const_mul] at h1
  have hVi : ∀ i, (weakDeriv V (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) := fun i ↦
    weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω (φ.contDiff.contDiffOn.of_le (by simp)) hVφ i
  have hL : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, weakDeriv U (MultiIndexLE.single i) x * weakDeriv V (MultiIndexLE.single i) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ∑ i, weakDeriv U (MultiIndexLE.single i) x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hVi] with x hx
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hx i]
  have hR : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      lam * (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U x
        * fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (lam • fn U) x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hVφ] with x hx
    rw [fnL_apply, fnL_apply, hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← hL, h1, hR]

/-- Let $U \in H^1(\Omega)$ and $\lambda \in \mathbb{R}$ satisfy $\int_\Omega \nabla U \cdot \nabla
V = \lambda \int_\Omega U V$ for every element $V \in H^1(\Omega)$ whose function agrees almost
everywhere on $\Omega$ with a test function. If the function of $U$ lies in
$H^m_{\mathrm{loc}}(\Omega)$, then it lies in $H^{m+2}_{\mathrm{loc}}(\Omega)$.

The datum $\lambda U$ of the equation $-\Delta U = \lambda U$ lies in
$H^m_{\mathrm{loc}}(\Omega)$, and `Elliptic.regularity_interior_higher` applies. -/
theorem memSobolevMultiIndexLoc_add_two_of_eigenfunction {U : SobolevEuclidean N 1 2 Ω}
    {lam : ℝ}
    (hUw : ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω U V
        = lam * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
          fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
    {m : ℕ}
    (hm : MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) m 2 Ω
      volume) :
    MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) (m + 2) 2 Ω
      volume :=
  regularity_interior_higher m (memSobolevMultiIndex U).memSobolevMultiIndexLoc
    (fun i ↦ weakDeriv_hasWeakIteratedLineDerivOn_single U i)
    (fun V hVc hVΩ ↦ (hm V hVc hVΩ).const_smul lam)
    (integral_sum_weakDeriv_mul_fderiv_eq_of_eigenfunction Ω hUw)

/-- A weak Dirichlet eigenfunction of $-\Delta$ lies in $H^m_{\mathrm{loc}}(\Omega)$ for every $m$.
Let $U \in H^1(\Omega)$ and $\lambda \in \mathbb{R}$ satisfy $\int_\Omega \nabla U \cdot \nabla
V = \lambda \int_\Omega U V$ for every element $V \in H^1(\Omega)$ whose function agrees almost
everywhere on $\Omega$ with a test function. Then the function of $U$ lies in
$H^m_{\mathrm{loc}}(\Omega)$ for every $m \in \mathbb{N}$.

This is the claim "$e_n \in \bigcap_m H^m(\omega)$ for all $\omega \subset\subset \Omega$" in
the proof of Theorem 9.31 of [brezis2011functional]. The proof is an induction on $m$ in steps
of two. The function of $U$ lies in $H^1_{\mathrm{loc}}(\Omega)$. If it lies in
$H^m_{\mathrm{loc}}(\Omega)$, interior regularity (Remark 25,
`Elliptic.regularity_interior_higher`) applied to $-\Delta U = \lambda U$ puts it in
$H^{m+2}_{\mathrm{loc}}(\Omega)$. The local space is `MemSobolevMultiIndexLoc`. -/
theorem eigenfunction_memSobolevMultiIndexLoc {U : SobolevEuclidean N 1 2 Ω} {lam : ℝ}
    (hUw : ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω U V
        = lam * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
          fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
    (m : ℕ) :
    MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) m 2 Ω volume := by
  have h1 : MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) 1 2 Ω
      volume := (memSobolevMultiIndex U).memSobolevMultiIndexLoc
  have key : ∀ m : ℕ,
      MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) m 2 Ω volume ∧
      MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn U) (m + 1) 2 Ω
        volume := by
    intro m
    induction m with
    | zero => exact ⟨h1.mono_order zero_le_one, h1⟩
    | succ m ih => exact ⟨ih.2, memSobolevMultiIndexLoc_add_two_of_eigenfunction Ω hUw ih.1⟩
  exact (key m).1

/-- A weak Dirichlet eigenfunction of $-\Delta$ has a $C^\infty$ representative on $\Omega$. Let
$U \in H^1(\Omega)$ and $\lambda \in \mathbb{R}$ satisfy $\int_\Omega \nabla U \cdot \nabla V =
\lambda \int_\Omega U V$ for every element $V \in H^1(\Omega)$ whose function agrees almost
everywhere on $\Omega$ with a test function. Then the function of $U$ agrees almost everywhere
on $\Omega$ with a function $\tilde u$ of class $C^\infty$ on $\Omega$.

The proof is `Elliptic.eigenfunction_memSobolevMultiIndexLoc` and
`MemSobolevMultiIndexLoc.exists_contDiffOn`. -/
theorem eigenfunction_exists_contDiffOn {U : SobolevEuclidean N 1 2 Ω} {lam : ℝ}
    (hUw : ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω U V
        = lam * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
          fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ ∞ ũ Ω ∧
      fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ :=
  MemSobolevMultiIndexLoc.exists_contDiffOn (eigenfunction_memSobolevMultiIndexLoc Ω hUw)

end Smoothness

section DirichletSmooth

open Laplacian SobolevMultiIndex

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- Let $\Omega$ be bounded and nonempty. Then the Dirichlet eigenfunction $u_n$ satisfies
$\int_\Omega \nabla u_n \cdot \nabla V = \lambda_n \int_\Omega u_n V$ for every element
$V \in H^1(\Omega)$ whose function agrees almost everywhere on $\Omega$ with a test function.

This is the weak equation (83) in the form of the hypothesis of
`Elliptic.eigenfunction_memSobolevMultiIndexLoc`. -/
theorem dirichletForm_dirichletEigenfunction_testFunctions (n : ℕ) :
    ∀ V ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n) V
        = dirichletEigenvalue Ω hΩ n
          * ⟪fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
              (dirichletEigenfunction Ω hΩ hne n),
            fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume V⟫_ℝ :=
  fun V hV ↦ (dirichletForm_dirichletEigenfunction Ω hΩ hne n
    ⟨V, SobolevMultiIndexZero.testFunctions_le hV⟩).trans
    (congrArg (fun y ↦ dirichletEigenvalue Ω hΩ n * ⟪y, fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume V⟫_ℝ)
      (fnL_dirichletEigenfunction Ω hΩ hne n).symm)

/-- The smoothness clauses of Theorem 9.31 of [brezis2011functional]. Let
$\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded nonempty open set. For every $n$
there is a function $\tilde u : \mathbb{R}^N \to \mathbb{R}$ of class $C^\infty$ on $\Omega$
that agrees almost everywhere on $\Omega$ with the Dirichlet eigenfunction $e_n$ and satisfies
$-\Delta \tilde u(x) = \lambda_n \tilde u(x)$ at every point $x \in \Omega$.

The book states these clauses as $e_n \in C^\infty(\Omega)$ and $-\Delta e_n = \lambda_n e_n$ in
$\Omega$. Together with `Elliptic.dirichletEigenbasis`, `Elliptic.dirichletEigenvalue_pos`,
`Elliptic.tendsto_dirichletEigenvalue_atTop` and `Elliptic.dirichletEigenfunction`, this is the
whole of Theorem 9.31.

The representative comes from interior regularity (Remark 25,
`Elliptic.eigenfunction_exists_contDiffOn`), and the pointwise equation from
`Elliptic.laplacian_eq_dirichletEigenfunction`. -/
theorem dirichletEigenbasis_exists_contDiffOn (n : ℕ) :
    ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, ContDiffOn ℝ ∞ ũ Ω ∧
      (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ ∧
      ∀ x ∈ Ω, -Δ ũ x = dirichletEigenvalue Ω hΩ n * ũ x := by
  obtain ⟨ũ, hũ, hae⟩ := eigenfunction_exists_contDiffOn Ω
    (dirichletForm_dirichletEigenfunction_testFunctions Ω hΩ hne n)
  have hae' : (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ :=
    (fn_dirichletEigenfunction Ω hΩ hne n).symm.trans hae
  exact ⟨ũ, hũ, hae', laplacian_eq_dirichletEigenfunction Ω hΩ hne n
    (hũ.of_le (by simp)) hae'⟩

/-- Let $\Omega$ be bounded and nonempty. Then the Dirichlet eigenfunction $u_n \in H^1_0(\Omega)$
solves $-\Delta u + u = (\lambda_n + 1) e_n$ weakly:
$$\int_\Omega (\nabla u_n \cdot \nabla v + u_n v) = (\lambda_n + 1) \int_\Omega e_n v \qquad
  \text{for all } v \in H^1_0(\Omega).$$

The statement is `IsGalerkinSolution` for the form `Elliptic.laplaceForm` of $-\Delta + 1$ and
the load of $(\lambda_n + 1) e_n$ on $H^1_0(\Omega)$. The proof uses
`Elliptic.laplaceForm_apply_eq_dirichletForm_add` and the weak equation (83). -/
theorem dirichletEigenfunction_isGalerkinSolution_laplace (n : ℕ) :
    IsGalerkinSolution (laplaceForm Ω)
      (load Ω ((dirichletEigenvalue Ω hΩ n + 1) • dirichletEigenbasis Ω hΩ hne n))
      (SobolevEuclideanZero (d + 1) 1 2 Ω)
      (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω) := by
  refine ⟨(dirichletEigenfunction Ω hΩ hne n).2, fun φ hφ ↦ ?_⟩
  have h1 := laplaceForm_apply_eq_dirichletForm_add Ω
    (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω) φ
  have h2 : dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      φ = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ :=
    dirichletForm_dirichletEigenfunction Ω hΩ hne n ⟨φ, hφ⟩
  have h3 : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      = dirichletEigenbasis Ω hΩ hne n := fnL_dirichletEigenfunction Ω hΩ hne n
  have h4 : load Ω ((dirichletEigenvalue Ω hΩ n + 1) • dirichletEigenbasis Ω hΩ hne n) φ
      = (dirichletEigenvalue Ω hΩ n + 1) * ⟪dirichletEigenbasis Ω hΩ hne n,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ := by
    rw [load_apply_inner, real_inner_smul_left]
    rfl
  have h5 : dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      φ + ⟪fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω),
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ
      = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ
        + ⟪dirichletEigenbasis Ω hΩ hne n,
          fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ :=
    congrArg₂ (· + ·) h2 (congrArg (fun y ↦ ⟪y,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ) h3)
  refine h1.trans (h5.trans (Eq.trans ?_ h4.symm))
  ring

/-- Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded nonempty open set of class
$C^\infty$. Then every Dirichlet eigenfunction $e_n$ lies in $H^m(\Omega)$ for every
$m \in \mathbb{N}$.

The eigenfunction $u_n$ solves $-\Delta u + u = (\lambda_n + 1) e_n$ weakly. If
$e_n \in H^m(\Omega)$, the datum $(\lambda_n + 1) e_n$ lies in $H^m(\Omega)$, so
$e_n \in H^{m+2}(\Omega)$ by Theorem 9.25 of [brezis2011functional]
(`Elliptic.regularity_dirichlet_higher_mem_laplace`). The proof is an induction on $m$. The
boundedness of $\Omega$ is needed for the eigenbasis to exist. Class $C^\infty$ is
`IsContDiffChartDomain ∞`. -/
theorem dirichletEigenfunction_memSobolevMultiIndex
    (hΩ' : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (n : ℕ) (m : ℕ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑(dirichletEigenbasis Ω hΩ hne n)) m 2 Ω volume := by
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hΩ.closure.subset frontier_subset_closure
  have hfn : (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fn (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω) :=
    (fn_dirichletEigenfunction Ω hΩ hne n).symm
  -- the datum is in `H^m` whenever the eigenfunction is
  have hdat : ∀ j : ℕ, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑(dirichletEigenbasis Ω hΩ hne n)) j 2 Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (⇑((dirichletEigenvalue Ω hΩ n + 1) • dirichletEigenbasis Ω hΩ hne n)) j 2 Ω volume :=
    fun j hj ↦ (hj.const_smul (dirichletEigenvalue Ω hΩ n + 1)).congr_ae
      (Lp.coeFn_smul _ _).symm
  have key : ∀ m : ℕ,
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (⇑(dirichletEigenbasis Ω hΩ hne n)) m 2 Ω volume ∧
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (⇑(dirichletEigenbasis Ω hΩ hne n)) (m + 1) 2 Ω volume := by
    intro m
    induction m with
    | zero =>
      have h1 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
          (⇑(dirichletEigenbasis Ω hΩ hne n)) 1 2 Ω volume :=
        (memSobolevMultiIndex (dirichletEigenfunction Ω hΩ hne n :
          SobolevEuclidean (d + 1) 1 2 Ω)).congr_ae hfn.symm
      exact ⟨h1.mono_order zero_le_one, h1⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have := regularity_dirichlet_higher_mem_laplace m (hΩ'.of_le (by simp)) hΓ (hdat m ih.1)
        (dirichletEigenfunction_isGalerkinSolution_laplace Ω hΩ hne n)
      exact this.congr_ae hfn.symm
  exact (key m).1

/-- The second clause of Remark 29 in Chapter 9 of [brezis2011functional]. Let
$\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded nonempty open set of class
$C^\infty$. Then every Dirichlet eigenfunction $e_n$ agrees almost everywhere on $\Omega$ with a
function $\tilde u : \mathbb{R}^N \to \mathbb{R}$ that is continuous on $\mathbb{R}^N$ and of
class $C^\infty$ on $\Omega$, and such that for every $j$ the $j$-th derivative $D^j \tilde u$
agrees on $\Omega$ with a continuous function on $\mathbb{R}^N$.

This is $e_n \in C^\infty(\overline{\Omega})$ in the sense of footnote 16 of Chapter 9 of
[brezis2011functional]. The eigenfunction solves $-\Delta u + u = (\lambda_n + 1) e_n$ weakly,
with a datum in every $H^m(\Omega)$ (`Elliptic.dirichletEigenfunction_memSobolevMultiIndex`),
and the $C^\infty(\overline{\Omega})$ clause of Theorem 9.25
(`Elliptic.regularity_dirichlet_smooth`) applies. -/
theorem exists_contDiffOn_closure_eigenfunction
    (hΩ' : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (n : ℕ) :
    ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous ũ ∧ ContDiffOn ℝ ∞ ũ Ω ∧
      (dirichletEigenbasis Ω hΩ hne n : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ ∧
      ∀ j : ℕ, ∃ G : EuclideanSpace ℝ (Fin (d + 1)) →
        (EuclideanSpace ℝ (Fin (d + 1)) [×j]→L[ℝ] ℝ), Continuous G ∧
        EqOn (iteratedFDeriv ℝ j ũ) G Ω := by
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hΩ.closure.subset frontier_subset_closure
  have hf : ∀ m : ℕ, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑((dirichletEigenvalue Ω hΩ n + 1) • dirichletEigenbasis Ω hΩ hne n)) m 2 Ω volume :=
    fun m ↦ ((dirichletEigenfunction_memSobolevMultiIndex Ω hΩ hne hΩ' n m).const_smul
      (dirichletEigenvalue Ω hΩ n + 1)).congr_ae (Lp.coeFn_smul _ _).symm
  obtain ⟨ũ, hc, hk, hae, hG⟩ := regularity_dirichlet_smooth hΩ' hΓ hf
    (dirichletEigenfunction_isGalerkinSolution_laplace Ω hΩ hne n)
  exact ⟨ũ, hc, hk, (fn_dirichletEigenfunction Ω hΩ hne n).symm.trans hae, hG⟩

end DirichletSmooth

end Elliptic
