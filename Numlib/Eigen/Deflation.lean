/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Numlib.LinearAlgebra.Matrix.Companion
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Wielandt deflation of a computed eigenpair

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with the inner
product $\langle \cdot, \cdot \rangle$ conjugate-linear in the first argument, and let $A : E \to E$
be linear. Once an eigenpair $(l, u)$ of $A$ is computed, a **deflation** modifies $A$ by a rank-one
operator so that $l$ moves to $l - \sigma$ and every other eigenvalue stays where it was. The same
eigenvalue algorithm, run on the modified operator, then produces the next eigenpair. Wielandt's
choice is
$$A_1 = A - \sigma\, u v^H, \qquad A_1 x = A x - \sigma \langle v, x \rangle u,$$
for any vector $v$ with $\langle v, u \rangle = 1$. The presentation follows [saad2011numerical],
§4.2.1. This file proves Wielandt's theorem with multiplicities, $\chi_{A_1}(X)\,(X - l) =
\chi_A(X)\,(X - (l - \sigma))$, where $\chi$ is the characteristic polynomial. The multiset of
eigenvalues of $A_1$ is therefore that of $A$ with one copy of $l$ replaced by $l - \sigma$.

The choice $v = u$ for a unit eigenvector $u$ is the Schur–Wielandt deflation. The reason for the
name Schur–Wielandt deflation for Algorithm 4.4 of [saad2011numerical] is that this choice preserves
the Schur vectors of $A$. The file also treats the Householder deflation of
[quarteroni2000numerical] (Remark 5.3, §5.12.2). It removes the eigenvalue instead of moving it: a
Householder reflector $H$ that maps the eigenvector $x$ to a multiple of $e_0$ makes the first
column of $HAH$ equal to $l e_0$, and the trailing $N \times N$ block of $HAH$ carries the remaining
eigenvalues with their multiplicities.

## Main definitions

* `LinearMap.wielandtDeflate`: the Wielandt deflation $A - \sigma u v^H$ of $A$ at $u$ with the
  shift $\sigma$.

## Main results

* `LinearMap.charpoly_wielandtDeflate`: Wielandt's theorem with multiplicities, $\chi_{A_1}(X)(X -
  l) = \chi_A(X)(X - (l - \sigma))$ when $Au = lu$ and $\langle v, u \rangle = 1$.
* `LinearMap.hasEigenvalue_wielandtDeflate`: $l - \sigma$ is an eigenvalue of $A_1$, with the
  eigenvector $u$.
* `LinearMap.hasEigenvalue_wielandtDeflate_iff`: a scalar $\mu \notin \{l, l - \sigma\}$ is an
  eigenvalue of $A_1$ if and only if it is an eigenvalue of $A$.
* `LinearMap.wielandtDeflate_adjoint_apply_of_ne`: a left eigenvector of $A$ for an eigenvalue
  $\mu \neq l$ is orthogonal to $u$ and is a left eigenvector of $A_1$ for $\mu$ (Proposition 4.1 of
  [saad2011numerical]).
* `LinearMap.schurWielandtDeflate_invtSubmodule`: an $A$-invariant subspace that contains $u$ is
  $A_1$-invariant.
* `Matrix.householder_conj_eigenvector_col`: if $Ax = lx$ with $x \neq 0$, the column $i_0$ of $HAH$
  is $l e_{i_0}$.
* `Matrix.charpoly_householder_conj_eigenvector`: $\chi_A(X) = (X - l)\,\chi_{A_2}(X)$ for the
  trailing $N \times N$ block $A_2$ of $HAH$.

## Proof outline

The proof of Wielandt's theorem is not the one of [saad2011numerical]. The operators $A$ and $A_1$
differ by an operator with range in the line $\mathbb{K} u$. So they induce the same map on the
quotient $E / \mathbb{K} u$, and the line is invariant for both, with $A$ acting on it as $l$ and
$A_1$ as $l - \sigma$. Hence $\det(t - A)$ and $\det(t - A_1)$ factor through the same determinant
on the quotient (`LinearMap.det_eq_det_mul_det`), with cofactors $t - l$ and $t - l + \sigma$. The
identity of polynomials follows because a field of characteristic zero is infinite
(`Polynomial.funext`). No basis adapted to $u$ and no block matrix is constructed.

The argument of [saad2011numerical] is `LinearMap.wielandtDeflate_adjoint_apply_of_ne`: a left
eigenvector of $A$ for an eigenvalue $\mu \neq l$ is orthogonal to $u$ and is therefore not changed
by the deflation. This file proves that statement as well, because it says that the deflation leaves
the left eigenvectors alone. It is not strong enough to give the multiplicities.

The Householder result follows from Laplace expansion of the characteristic polynomial along the
first column of $HAH$.

## Implementation notes

* A Schur factorization is a complete flag of invariant subspaces, and each subspace of the flag
  contains $u$. Preserving the Schur vectors amounts to
  `LinearMap.schurWielandtDeflate_invtSubmodule`. Mathlib has no Schur form, and none is needed to
  state or to use this theorem: the flag is the data that the statement quantifies over.
* `LinearMap.schurWielandtDeflate_invtSubmodule` uses only $u \in S$, not $v = u$ nor the
  normalization $\langle v, u \rangle = 1$. The block deflation $A - Q \Sigma Q^H$ of Proposition
  4.2 of [saad2011numerical] is `LinearMap.wielandtDeflate` iterated over the columns of $Q$
  (`LinearMap.wielandtDeflate_wielandtDeflate` composes two steps into one rank-two modification),
  and the same theorem applies at each step.
-/

open Polynomial

open scoped ComplexConjugate

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Wielandt's deflation** of $A : E \to E$ at the vector $u$ with the shift $\sigma$: for
$u, v \in E$ and $\sigma \in \mathbb{K}$, it is the rank-one modification
$$A - \sigma\, u v^H : x \mapsto A x - \sigma \langle v, x \rangle u$$
of (4.6) of [saad2011numerical].

The vector $v$ is arbitrary in the definition. Every statement about the spectrum assumes the
normalization $\langle v, u \rangle = 1$, and the choice $v = u$ for a unit eigenvector $u$ is
the Schur–Wielandt deflation. The rank-one operator is
`LinearMap.toSpanSingleton 𝕜 E u ∘ₗ innerₛₗ 𝕜 v`. -/
noncomputable def wielandtDeflate (A : E →ₗ[𝕜] E) (u v : E) (σ : 𝕜) : E →ₗ[𝕜] E :=
  A - σ • (toSpanSingleton 𝕜 E u ∘ₗ innerₛₗ 𝕜 v)

/-- The deflated operator maps $x$ to $A x - \sigma \langle v, x \rangle u$. -/
@[simp]
theorem wielandtDeflate_apply (A : E →ₗ[𝕜] E) (u v : E) (σ : 𝕜) (x : E) :
    wielandtDeflate A u v σ x = A x - (σ * inner 𝕜 v x) • u := by
  simp [wielandtDeflate, mul_smul]

/-- For every $x \in E$, the difference $A x - A_1 x$ of $A$ and its Wielandt deflation $A_1$ lies
in the line $\mathbb{K} u$. -/
theorem sub_wielandtDeflate_mem_span (A : E →ₗ[𝕜] E) (u v : E) (σ : 𝕜) (x : E) :
    A x - wielandtDeflate A u v σ x ∈ 𝕜 ∙ u := by
  simp only [wielandtDeflate_apply, sub_sub_cancel]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)

/-- If $\langle v, x \rangle = 0$, the Wielandt deflation $A_1 = A - \sigma u v^H$ satisfies
$A_1 x = A x$. -/
theorem wielandtDeflate_apply_of_inner_eq_zero {A : E →ₗ[𝕜] E} {u v x : E} {σ : 𝕜}
    (hx : (inner 𝕜 v x : 𝕜) = 0) : wielandtDeflate A u v σ x = A x := by
  simp [hx]

/-- **The computed eigenvalue moves by the shift.** Let $A : E \to E$ be linear, let $u, v \in E$
with $\langle v, u \rangle = 1$, and let $A u = l u$. Then for every $\sigma \in \mathbb{K}$ the
Wielandt deflation $A_1 = A - \sigma u v^H$ satisfies
$$A_1 u = (l - \sigma) u.$$
-/
theorem wielandtDeflate_apply_self {A : E →ₗ[𝕜] E} {u v : E} {l : 𝕜}
    (hv : (inner 𝕜 v u : 𝕜) = 1) (hu : A u = l • u) (σ : 𝕜) :
    wielandtDeflate A u v σ u = (l - σ) • u := by
  simp [hu, hv, sub_smul]

/-- Two Wielandt deflations compose into a rank-two modification: for all $u, v, u', v' \in E$,
$\sigma, \sigma' \in \mathbb{K}$ and $x \in E$,
$$(A - \sigma u v^H - \sigma' u' v'^H)\, x = A x - \sigma \langle v, x \rangle u - \sigma'
  \langle v', x \rangle u',$$
where the left side is the deflation at $u'$, $v'$, $\sigma'$ of the deflation at $u$, $v$,
$\sigma$. The block deflation $A - Q \Sigma Q^H$ of Proposition 4.2 of [saad2011numerical]
arises in this way. -/
theorem wielandtDeflate_wielandtDeflate (A : E →ₗ[𝕜] E) (u v u' v' : E) (σ σ' : 𝕜) (x : E) :
    wielandtDeflate (wielandtDeflate A u v σ) u' v' σ' x
      = A x - (σ * inner 𝕜 v x) • u - (σ' * inner 𝕜 v' x) • u' := by
  simp

section Line

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If $Bu = mu$, then for every scalar $t$ the operator $t - B$ maps the line $K u$ into itself. -/
private theorem span_le_comap_of_apply_eq_smul {B : V →ₗ[K] V} {u : V} {m : K}
    (hu : B u = m • u) (t : K) :
    (K ∙ u) ≤ (K ∙ u).comap (algebraMap K (V →ₗ[K] V) t - B) := by
  rintro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  refine Submodule.mem_span_singleton.2 ⟨c * t - c * m, ?_⟩
  simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, map_smul, hu, sub_smul]
  module

/-- If $Bu = mu$ with $u \neq 0$, the restriction of $t - B$ to the line $K u$ has determinant
$t - m$. -/
private theorem det_restrict_span {B : V →ₗ[K] V} {u : V} {m : K} (hu : B u = m • u)
    (hu0 : u ≠ 0) (t : K)
    (h : ∀ x ∈ (K ∙ u), (algebraMap K (V →ₗ[K] V) t - B) x ∈ (K ∙ u)) :
    ((algebraMap K (V →ₗ[K] V) t - B).restrict h).det = t - m := by
  have hrestrict : (algebraMap K (V →ₗ[K] V) t - B).restrict h = (t - m) • LinearMap.id := by
    ext x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
    have hx : (x : V) = c • u := hc.symm
    simp only [coe_restrict_apply, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, hx,
      map_smul, hu, id_coe, _root_.id, Submodule.coe_smul]
    module
  rw [hrestrict, LinearMap.det_smul, LinearMap.det_id, mul_one,
    finrank_span_singleton hu0, pow_one]

variable [FiniteDimensional K V] in
/-- Let $V$ be a finite-dimensional vector space over a field $K$, and let $A, B : V \to V$ be
linear. Let $u \neq 0$ with $A u = l u$ and $B u = m u$, and let $A x - B x \in K u$ for every
$x \in V$. Then for every $t \in K$ the characteristic polynomials satisfy
$$\chi_A(t)\,(t - m) = \chi_B(t)\,(t - l).$$

This is the core of Wielandt's theorem `LinearMap.charpoly_wielandtDeflate`. The statement is an
identity of values at each $t \in K$, not an identity of polynomials. -/
theorem eval_charpoly_mul_of_sub_mem_span {A B : V →ₗ[K] V} {u : V} {l m : K}
    (hA : A u = l • u) (hB : B u = m • u) (hu0 : u ≠ 0)
    (hAB : ∀ x, A x - B x ∈ K ∙ u) (t : K) :
    A.charpoly.eval t * (t - m) = B.charpoly.eval t * (t - l) := by
  have hqA := span_le_comap_of_apply_eq_smul hA t
  have hqB := span_le_comap_of_apply_eq_smul hB t
  have hquot : (K ∙ u).mapQ (K ∙ u) (algebraMap K (V →ₗ[K] V) t - A) hqA
      = (K ∙ u).mapQ (K ∙ u) (algebraMap K (V →ₗ[K] V) t - B) hqB := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp only [comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simpa using Submodule.neg_mem _ (hAB x)
  rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly,
    LinearMap.det_eq_det_mul_det _ _ hqA, LinearMap.det_eq_det_mul_det _ _ hqB,
    det_restrict_span hA hu0, det_restrict_span hB hu0, hquot]
  ring

end Line

section Spectrum

variable [FiniteDimensional 𝕜 E]

/-- **Wielandt's theorem**, with multiplicities (Theorem 4.2 of [saad2011numerical]). Let $E$ be a
finite-dimensional inner product space over $\mathbb{K}$, let $A : E \to E$ be linear, and let
$u, v \in E$ with $\langle v, u \rangle = 1$ and $A u = l u$. Then for every
$\sigma \in \mathbb{K}$ the Wielandt deflation $A_1 = A - \sigma u v^H$ satisfies
$$\chi_{A_1}(X)\,(X - l) = \chi_A(X)\,(X - (l - \sigma)).$$
So deflation replaces one copy of $l$ among the roots of the characteristic polynomial by
$l - \sigma$, and changes nothing else.

The normalization $\langle v, u \rangle = 1$ is the hypothesis of the source. It implies
$u \neq 0$, so that hypothesis is not stated. The proof applies
`LinearMap.eval_charpoly_mul_of_sub_mem_span` at every $t$ and uses that $\mathbb{K}$ is
infinite. -/
theorem charpoly_wielandtDeflate {A : E →ₗ[𝕜] E} {u v : E} {l : 𝕜}
    (hv : (inner 𝕜 v u : 𝕜) = 1) (hu : A u = l • u) (σ : 𝕜) :
    (wielandtDeflate A u v σ).charpoly * (X - C l) = A.charpoly * (X - C (l - σ)) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hv
  refine Polynomial.funext fun t => ?_
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  exact eval_charpoly_mul_of_sub_mem_span (wielandtDeflate_apply_self hv hu σ) hu hu0
    (fun x => by
      simpa using Submodule.neg_mem _ (sub_wielandtDeflate_mem_span A u v σ x)) t

omit [FiniteDimensional 𝕜 E] in
/-- Let $A : E \to E$ be linear, and let $u, v \in E$ with $\langle v, u \rangle = 1$ and
$A u = l u$. Then for every $\sigma \in \mathbb{K}$, the scalar $l - \sigma$ is an eigenvalue of
the Wielandt deflation $A - \sigma u v^H$, with the eigenvector $u$. The space $E$ need not be
finite-dimensional. -/
theorem hasEigenvalue_wielandtDeflate {A : E →ₗ[𝕜] E} {u v : E} {l : 𝕜}
    (hv : (inner 𝕜 v u : 𝕜) = 1) (hu : A u = l • u) (σ : 𝕜) :
    Module.End.HasEigenvalue (wielandtDeflate A u v σ) (l - σ) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hv
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 (wielandtDeflate_apply_self hv hu σ), hu0⟩

/-- **The spectrum away from the two moved points does not change** (Theorem 4.2 of
[saad2011numerical]). Let $E$ be a finite-dimensional inner product space over $\mathbb{K}$, let
$A : E \to E$ be linear, and let $u, v \in E$ with $\langle v, u \rangle = 1$ and $A u = l u$.
Let $\sigma \in \mathbb{K}$, and let $\mu \in \mathbb{K}$ with $\mu \neq l$ and
$\mu \neq l - \sigma$. Then $\mu$ is an eigenvalue of the Wielandt deflation $A - \sigma u v^H$
if and only if $\mu$ is an eigenvalue of $A$. -/
theorem hasEigenvalue_wielandtDeflate_iff {A : E →ₗ[𝕜] E} {u v : E} {l μ : 𝕜}
    (hv : (inner 𝕜 v u : 𝕜) = 1) (hu : A u = l • u) (σ : 𝕜) (hμ : μ ≠ l) (hμ' : μ ≠ l - σ) :
    Module.End.HasEigenvalue (wielandtDeflate A u v σ) μ ↔ Module.End.HasEigenvalue A μ := by
  have key := congrArg (Polynomial.eval μ) (charpoly_wielandtDeflate hv hu σ)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at key
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    IsRoot.def, IsRoot.def]
  constructor
  · intro h
    rw [h, zero_mul] at key
    exact (mul_eq_zero.1 key.symm).resolve_right (sub_ne_zero.2 hμ')
  · intro h
    rw [h, zero_mul] at key
    exact (mul_eq_zero.1 key).resolve_right (sub_ne_zero.2 hμ)

/-- **Left eigenvectors survive the deflation** (Proposition 4.1 of [saad2011numerical], and the
mechanism of its proof of Theorem 4.2). Let $E$ be a finite-dimensional inner product space over
$\mathbb{K}$, let $A : E \to E$ be linear, let $A u = l u$, and let $w \in E$ satisfy
$A^* w = \bar{\mu} w$ with $\mu \neq l$, so that $w$ is a left eigenvector of $A$ for $\mu$ when
$w \neq 0$. Then for all $v \in E$ and $\sigma \in \mathbb{K}$,
$$\langle w, u \rangle = 0 \quad\text{and}\quad (A - \sigma u v^H)^* w = \bar{\mu} w.$$

The orthogonality is the classical argument: $\langle w, A u \rangle$ equals
$l \langle w, u \rangle$ and also $\mu \langle w, u \rangle$, and $\mu \neq l$. No normalization
of $v$ is needed. The adjoint is `LinearMap.adjoint`. -/
theorem wielandtDeflate_adjoint_apply_of_ne {A : E →ₗ[𝕜] E} {u v w : E} {l μ : 𝕜}
    (hu : A u = l • u) (hw : A.adjoint w = conj μ • w) (hne : μ ≠ l) (σ : 𝕜) :
    (inner 𝕜 w u : 𝕜) = 0 ∧
      (wielandtDeflate A u v σ).adjoint w = conj μ • w := by
  have horth : (inner 𝕜 w u : 𝕜) = 0 := by
    have h1 : (inner 𝕜 w (A u) : 𝕜) = l * inner 𝕜 w u := by
      rw [hu, inner_smul_right]
    have h2 : (inner 𝕜 w (A u) : 𝕜) = μ * inner 𝕜 w u := by
      rw [← LinearMap.adjoint_inner_left, hw, inner_smul_left]
      simp
    have : (l - μ) * inner 𝕜 w u = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  refine ⟨horth, ?_⟩
  refine ext_inner_right 𝕜 fun x => ?_
  rw [LinearMap.adjoint_inner_left, wielandtDeflate_apply, inner_sub_right, inner_smul_right,
    horth, mul_zero, sub_zero, ← LinearMap.adjoint_inner_left, hw]

end Spectrum

/-! ### The Schur–Wielandt choice -/

/-- **Schur–Wielandt deflation preserves the invariant flag** (Proposition 4.1 of
[saad2011numerical]). Let $A : E \to E$ be linear, and let $S \subseteq E$ be an $A$-invariant
subspace that contains $u$. Then for all $v \in E$ and $\sigma \in \mathbb{K}$, the subspace $S$
is invariant for the Wielandt deflation $A - \sigma u v^H$.

The Schur vectors of $A$ are determined, up to phase, by the complete flag of invariant
subspaces that they span. Each subspace of the flag of a Schur factorization whose first vector
is $u$ contains $u$. So this theorem is the coordinate-free content of "the Schur vectors do not
change". It needs no Schur factorization, which Mathlib does not have, and it needs neither the
choice $v = u$ nor a normalization. The several-vector deflation $A - Q \Sigma Q^H$ of
Proposition 4.2 of [saad2011numerical] is this theorem applied once for each column of $Q$,
through `LinearMap.wielandtDeflate_wielandtDeflate`. -/
theorem schurWielandtDeflate_invtSubmodule {A : E →ₗ[𝕜] E} {u : E} {S : Submodule 𝕜 E}
    (hS : S ∈ Module.End.invtSubmodule A) (hu : u ∈ S) (v : E) (σ : 𝕜) :
    S ∈ Module.End.invtSubmodule (wielandtDeflate A u v σ) := by
  refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun x hx => ?_
  rw [wielandtDeflate_apply]
  exact Submodule.sub_mem _
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hS x hx)
    (Submodule.smul_mem _ _ hu)

end LinearMap

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Householder deflation -/

section Householder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Householder deflation** (Remark 5.3 of [quarteroni2000numerical]). Let
$A \in \mathbb{K}^{n \times n}$, let $x \in \mathbb{K}^n$ with $x \neq 0$ and $A x = l x$, let
$i_0$ be an index, and let $H = I - 2 w w^H$ be the Householder reflector with $w$ =
`Matrix.householderVec x i₀`, which maps $x$ to a multiple of $e_{i_0}$. Then the column $i_0$
of $HAH$ is $l e_{i_0}$.

The reason is that $HAH(Hx) = HAx = l\,Hx$ and $Hx$ is a nonzero multiple of $e_{i_0}$
(`Matrix.householder_mulVec_eq_smul_single`). The reflector is `Matrix.householder
(Matrix.householderVec x i₀)`. -/
theorem householder_conj_eigenvector_col (A : Matrix n n 𝕜) {x : n → 𝕜} {l : 𝕜}
    (hx : A *ᵥ x = l • x) (hx0 : x ≠ 0) (i₀ : n) :
    (householder (householderVec x i₀) * A * householder (householderVec x i₀)).col i₀
      = Pi.single i₀ l := by
  set H := householder (householderVec x i₀) with hH
  have hHH : H * H = 1 := householder_mul_self (star_dotProduct_householderVec_self hx0 i₀)
  have hHx := householder_mulVec_eq_smul_single hx0 i₀
  rw [← hH] at hHx
  set α : 𝕜 := -(phase (x i₀) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜))) with hα
  have hα0 : α ≠ 0 := by
    rw [hα, neg_ne_zero]
    refine mul_ne_zero (norm_ne_zero_iff.mp (by rw [norm_phase]; exact one_ne_zero)) ?_
    have : (WithLp.toLp 2 x : EuclideanSpace 𝕜 n) ≠ 0 := by simpa using hx0
    simpa using norm_ne_zero_iff.mpr this
  have key : (H * A * H) *ᵥ (H *ᵥ x) = l • (H *ᵥ x) := by
    rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hHH, Matrix.mul_one, ← mulVec_mulVec,
      hx, mulVec_smul]
  rw [hHx, mulVec_smul, smul_smul, mul_comm, ← smul_smul] at key
  have key' := smul_right_injective (n → 𝕜) hα0 key
  rw [mulVec_single_one] at key'
  rw [key', ← Pi.single_smul, smul_eq_mul, mul_one]

/-- **Householder deflation**, entrywise (Remark 5.3 of [quarteroni2000numerical]). Under the
hypotheses of `Matrix.householder_conj_eigenvector_col`, the entries of the column $i_0$ of
$HAH$ are $(HAH)_{i_0 i_0} = l$ and $(HAH)_{i i_0} = 0$ for $i \neq i_0$. -/
theorem householder_conj_eigenvector_apply (A : Matrix n n 𝕜) {x : n → 𝕜} {l : 𝕜}
    (hx : A *ᵥ x = l • x) (hx0 : x ≠ 0) (i₀ i : n) :
    (householder (householderVec x i₀) * A * householder (householderVec x i₀)) i i₀
      = if i = i₀ then l else 0 := by
  have h := congrFun (householder_conj_eigenvector_col A hx hx0 i₀) i
  rw [col_apply] at h
  rw [h, Pi.single_apply]

end Householder

section Charpoly

variable {N : ℕ}

/-- Let $M \in \mathbb{K}^{(N+1) \times (N+1)}$, with indices $0, \dots, N$, have first column
$l e_0$. Then
$$\chi_M(X) = (X - l)\,\chi_{M'}(X),$$
where $M'$ is the trailing $N \times N$ principal submatrix of $M$, obtained by deleting row $0$
and column $0$. The proof is Laplace expansion along the first column. -/
theorem charpoly_eq_mul_charpoly_submatrix_succ_of_col_zero
    {M : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜} {l : 𝕜} (hM : M.col 0 = Pi.single 0 l) :
    M.charpoly = (X - C l) * (M.submatrix Fin.succ Fin.succ).charpoly := by
  have hcol : ∀ i, M i 0 = (Pi.single (0 : Fin (N + 1)) l : Fin (N + 1) → 𝕜) i := fun i =>
    congrFun hM i
  rw [charpoly, det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · rw [charmatrix_apply_eq, hcol, Pi.single_eq_same, Fin.succAbove_zero,
      ← charmatrix_submatrix _ (Fin.succ_injective _)]
    simp [charpoly]
  · intro i _
    rw [charmatrix_apply, hcol, Pi.single_eq_of_ne (Fin.succ_ne_zero i), map_zero, sub_zero,
      diagonal_apply_ne _ (Fin.succ_ne_zero i)]
    simp

/-- **Householder deflation removes one copy of the eigenvalue** (Remark 5.3 and §5.12.2 of
[quarteroni2000numerical]). Let $A \in \mathbb{K}^{(N+1) \times (N+1)}$, with indices
$0, \dots, N$, and let $x \neq 0$ with $A x = l x$. Let $H$ be the Householder reflector that
maps $x$ to a multiple of $e_0$, as in `Matrix.householder_conj_eigenvector_col`, and let $A_2$
be the trailing $N \times N$ block of $A_1 = HAH$. Then
$$\chi_A(X) = (X - l)\,\chi_{A_2}(X),$$
so the eigenvalues of $A_2$ are those of $A$ with one copy of $l$ removed, with multiplicities.

The block $A_2$ is `A₁.submatrix Fin.succ Fin.succ`. Wielandt deflation
(`LinearMap.charpoly_wielandtDeflate`) moves $l$ to $l - \sigma$ instead, and keeps the size of
the matrix. -/
theorem charpoly_householder_conj_eigenvector (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜)
    {x : Fin (N + 1) → 𝕜} {l : 𝕜} (hx : A *ᵥ x = l • x) (hx0 : x ≠ 0) :
    A.charpoly = (X - C l) *
      ((householder (householderVec x 0) * A * householder (householderVec x 0)).submatrix
        Fin.succ Fin.succ).charpoly := by
  set H := householder (householderVec x 0) with hH
  have hHH : H * H = 1 := householder_mul_self (star_dotProduct_householderVec_self hx0 0)
  have hsim : A.charpoly = (H * A * H).charpoly := by
    rw [charpoly_mul_comm, ← Matrix.mul_assoc, hHH, Matrix.one_mul]
  rw [hsim]
  exact charpoly_eq_mul_charpoly_submatrix_succ_of_col_zero
    (householder_conj_eigenvector_col A hx hx0 0)

end Charpoly

end Matrix
