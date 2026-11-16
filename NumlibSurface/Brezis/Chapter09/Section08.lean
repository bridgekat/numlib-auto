/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Elliptic.Spectral
import NumlibSurface.Brezis.Chapter09.Section06
import NumlibSurface.Brezis.Chapter09.Section07

/-!
# Brezis, Section 9.8: Eigenfunctions and spectral decomposition

This module formalizes Section 9.8 of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be a
bounded open set with Lebesgue measure. Theorem 9.31 states that there are a Hilbert basis $(e_n)$
of $L^2(\Omega)$ and real numbers $\lambda_n > 0$ with $\lambda_n \to +\infty$ such that
$e_n \in H^1_0(\Omega) \cap C^\infty(\Omega)$ and $-\Delta e_n = \lambda_n e_n$ in $\Omega$. The
weak form of the eigenvalue equation is (83), $\int_\Omega \nabla e_n \cdot \nabla \varphi =
\lambda_n \int_\Omega e_n \varphi$ for all $\varphi \in H^1_0(\Omega)$. Remark 28 gives the
corresponding Hilbert bases of $H^1_0(\Omega)$ for its two scalar products, Remark 29 gives
smoothness up to the boundary on a smooth domain, and Remark 30 extends the theorem to symmetric
elliptic operators with $L^\infty$ coefficients.

The proofs specialize the backbone module `Numlib.Analysis.PDE.Elliptic.Spectral`, which proves the
theorem for an arbitrary symmetric coercive form on $H^1_0(\Omega)$ and names the Dirichlet data
`Elliptic.dirichletEigenbasis`, `Elliptic.dirichletEigenvalue` and
`Elliptic.dirichletEigenfunction`.

## Main results

* Theorem 9.31, `Brezis.Chapter09.theorem_9_31_weak`: the backbone Dirichlet eigenbasis satisfies
  the weak eigenvalue equation (83).
* Theorem 9.31, `Brezis.Chapter09.theorem_9_31`: there are a Hilbert basis $(e_n)$ of $L^2(\Omega)$
  and an increasing sequence $\lambda_n > 0$ with $\lambda_n \to +\infty$ such that
  $e_n \in H^1_0(\Omega)$ satisfies (83).
* Theorem 9.31, `Brezis.Chapter09.theorem_9_31_laplacian`: a $C^2$ representative of a weak
  eigenfunction satisfies $-\Delta e = \lambda e$ at every point of $\Omega$.
* Theorem 9.31, `Brezis.Chapter09.theorem_9_31_smooth`: the complete theorem, with
  $e_n \in C^\infty(\Omega)$ and $-\Delta e_n = \lambda_n e_n$ pointwise in $\Omega$.
* Remark 28, `Brezis.Chapter09.remark_9_28`: $(e_n / \sqrt{\lambda_n})$ is a Hilbert basis of
  $H^1_0(\Omega)$ for the scalar product $\int_\Omega \nabla u \cdot \nabla v$.
* Remark 28, `Brezis.Chapter09.remark_9_28_h1`: $(e_n / \sqrt{\lambda_n + 1})$ is a Hilbert basis of
  $H^1_0(\Omega)$ for the scalar product $\int_\Omega (\nabla u \cdot \nabla v + uv)$.
* Remark 29, `Brezis.Chapter09.remark_9_29`: if $\Omega$ is of class $C^\infty$, then
  $e_n \in C^\infty(\overline{\Omega})$.
* Remark 30, `Brezis.Chapter09.remark_9_30`: for symmetric uniformly elliptic coefficients $a_{ij}$
  and $a_0$ in $L^\infty(\Omega)$, $L^2(\Omega)$ has a Hilbert basis of weak eigenfunctions with
  eigenvalues $\lambda_n \to +\infty$.

## Conventions

* $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin (d + 1))`, so that $N = d + 1 \ge 1$, and $\Omega$ is an
  open set `Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))`. "$\Omega$ is bounded" is
  `Bornology.IsBounded Ω`.
* $H^1(\Omega)$ is `Brezis.Chapter09.hSpace N Ω` (Section 9.1) and $H^1_0(\Omega)$ is
  `Brezis.Chapter09.hZeroSpace N Ω` (Section 9.4). "$e_n \in H^1_0(\Omega)$" means that there is
  $u_n \in H^1_0(\Omega)$ whose function agrees almost everywhere on $\Omega$ with $e_n$.
* The weak eigenvalue equation (83) is written with the integrals of the source, $\int_\Omega \nabla
  u_n \cdot \nabla \varphi = \lambda_n \int_\Omega e_n \varphi$ for all $\varphi \in H^1_0(\Omega)$.
  The classical equation uses Mathlib's Laplacian $\Delta$.
* Sequences are indexed by `ℕ` and start at $0$; the source starts at $1$.

## Implementation notes

* Theorem 9.31 is stated as the existential statement of the source in
  `Brezis.Chapter09.theorem_9_31` (the Hilbert-space clauses) and
  `Brezis.Chapter09.theorem_9_31_smooth` (the complete theorem). The witnesses are the named
  backbone data. The weak equation (83) for these data is `Brezis.Chapter09.theorem_9_31_weak`, and
  the classical equation for any $C^2$ representative is `Brezis.Chapter09.theorem_9_31_laplacian`.
* Remark 28 is stated for the data of Theorem 9.31. The scalar product
  $\int_\Omega \nabla u \cdot \nabla v$ is that of the energy space `WithEnergy` of the operator of
  the Dirichlet form on $H^1_0(\Omega)$. The scalar product
  $\int_\Omega (\nabla u \cdot \nabla v + uv)$ is the one that the type of $H^1_0(\Omega)$ carries.
  Both identifications are part of the statements.
* In Remark 30 the ellipticity condition (36) on the $L^\infty$ classes is the almost-everywhere
  condition `Elliptic.IsUniformlyElliptic`, as in Section 9.5.
* In Remark 29, $C^\infty(\overline{\Omega})$ is understood in the sense of footnote 16 of Section
  9.3, as `ContDiffOnClosure`, as in Section 9.6.

## Deviations from the source

* **Standing assumption on $\Omega$** (reading). The source leaves $\Omega \neq \emptyset$ and
  $N \ge 1$ implicit. All results assume them, because for an empty $\Omega$ or $N = 0$ the space
  $L^2(\Omega)$ is finite-dimensional and has no Hilbert basis indexed by `ℕ`. See
  `Brezis.Chapter09.theorem_9_31`.
* **Remark 30** (correction). The source omits the symmetry $a_{ij} = a_{ji}$, without which there
  is no orthonormal basis of eigenfunctions. The library assumes it. The eigenvalues $\lambda_n$
  need not be positive. See `Brezis.Chapter09.remark_9_30`.

## Not formalized

* **Remark 29, first clause.** The statement $e_n \in L^\infty(\Omega)$ for a general bounded
  $\Omega$ is given in the source without proof.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal InnerProductSpace

namespace Brezis.Chapter09

section Spectral

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-! ### Theorem 9.31 -/

/-- **Theorem 9.31** of [brezis2011functional], equation (83) for the backbone eigenbasis. Let
$\Omega \subset \mathbb{R}^N$ be a bounded nonempty open set, with $N = d + 1$. Let $e_n$ be
`Elliptic.dirichletEigenbasis Ω hb hne n` and let $\lambda_n$ be
`Elliptic.dirichletEigenvalue Ω hb n`. Then for every $n$ there is $u_n \in H^1_0(\Omega)$ whose
function agrees almost everywhere on $\Omega$ with $e_n$ and that satisfies
$$\int_\Omega \nabla u_n \cdot \nabla \varphi = \lambda_n \int_\Omega e_n \varphi \qquad
  \text{for all } \varphi \in H^1_0(\Omega).$$

This is the clause of Theorem 9.31 that `Brezis.Chapter09.theorem_9_31` and
`Brezis.Chapter09.theorem_9_31_smooth` share. The element $u_n$ is
`Elliptic.dirichletEigenfunction`. Here $u_n$ is an element of `Brezis.Chapter09.hSpace` that
lies in `Brezis.Chapter09.hZeroSpace`, and $\nabla u_n \cdot \nabla \varphi$ is the sum of the
products of the weak partial derivatives `Brezis.Chapter09.partialDeriv`. -/
theorem theorem_9_31_weak (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty)
    (n : ℕ) :
    ∃ u : hSpace (d + 1) Ω, u ∈ hZeroSpace (d + 1) Ω ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)]
        Elliptic.dirichletEigenbasis Ω hb hne n ∧
      ∀ φ ∈ hZeroSpace (d + 1) Ω,
        ∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x
          = Elliptic.dirichletEigenvalue Ω hb n
            * ∫ x in (Ω : Set 𝔼), Elliptic.dirichletEigenbasis Ω hb hne n x
              * SobolevMultiIndex.fn φ x := by
  refine ⟨Elliptic.dirichletEigenfunction Ω hb hne n,
    (Elliptic.dirichletEigenfunction Ω hb hne n).2, Elliptic.fn_dirichletEigenfunction Ω hb hne n,
    fun φ hφ ↦ ?_⟩
  have h := Elliptic.dirichletForm_dirichletEigenfunction Ω hb hne n ⟨φ, hφ⟩
  refine (Elliptic.dirichletForm_apply Ω _ _).symm.trans (h.trans ?_)
  exact congrArg (fun y ↦ Elliptic.dirichletEigenvalue Ω hb n * y)
    (MeasureTheory.L2.inner_eq_integral_mul _ _)

/-- **Theorem 9.31** of [brezis2011functional], the Hilbert-space clauses. Let
$\Omega \subset \mathbb{R}^N$ be a bounded nonempty open set, with $N = d + 1$. There exist a
Hilbert basis $(e_n)$ of $L^2(\Omega)$ and real numbers $(\lambda_n)$ such that $\lambda_n > 0$
for all $n$, the sequence $(\lambda_n)$ is increasing and $\lambda_n \to +\infty$, and each
$e_n$ lies in $H^1_0(\Omega)$ and satisfies $-\Delta e_n = \lambda_n e_n$ in the weak sense
(83): there is $u_n \in H^1_0(\Omega)$ whose function agrees almost everywhere on $\Omega$ with
$e_n$ and that satisfies
$$\int_\Omega \nabla u_n \cdot \nabla \varphi = \lambda_n \int_\Omega e_n \varphi \qquad
  \text{for all } \varphi \in H^1_0(\Omega).$$

The witnesses are `Elliptic.dirichletEigenbasis`, `Elliptic.dirichletEigenvalue` and
`Elliptic.dirichletEigenfunction`. The solution operator $T$ of the problem $\int_\Omega \nabla
u \cdot \nabla \varphi = \int_\Omega f \varphi$ on $H^1_0(\Omega)$ is self-adjoint, compact (the
injection $H^1_0(\Omega) \subset L^2(\Omega)$ is compact, Remark 20), positive and injective.
The spectral theorem for compact self-adjoint operators (Theorem 6.11) gives the basis, with
$\lambda_n = 1/\mu_n$ for the eigenvalues $\mu_n$ of $T$. The proof in the source says "repeat
the proof of Theorem 8.21"; the one-dimensional Sturm–Liouville theorem that it refers to is
Theorem 8.22. The clause "$e_n \in C^\infty(\Omega)$ and $-\Delta e_n = \lambda_n e_n$ pointwise
in $\Omega$" is `Brezis.Chapter09.theorem_9_31_smooth`. -/
theorem theorem_9_31 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty) :
    ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))) (lam : ℕ → ℝ),
      (∀ n, 0 < lam n) ∧ Monotone lam ∧ Tendsto lam atTop atTop ∧
      ∀ n, ∃ u : hSpace (d + 1) Ω, u ∈ hZeroSpace (d + 1) Ω ∧
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] e n ∧
        ∀ φ ∈ hZeroSpace (d + 1) Ω,
          ∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x
            = lam n * ∫ x in (Ω : Set 𝔼), e n x * SobolevMultiIndex.fn φ x :=
  ⟨Elliptic.dirichletEigenbasis Ω hb hne, Elliptic.dirichletEigenvalue Ω hb,
    Elliptic.dirichletEigenvalue_pos Ω hb hne, Elliptic.monotone_dirichletEigenvalue Ω hb hne,
    Elliptic.tendsto_dirichletEigenvalue_atTop Ω hb hne, theorem_9_31_weak hb hne⟩

/-- **Theorem 9.31** of [brezis2011functional], complete. Let $\Omega \subset \mathbb{R}^N$ be a
bounded nonempty open set, with $N = d + 1$. There exist a Hilbert basis $(e_n)$ of
$L^2(\Omega)$ and real numbers $(\lambda_n)$ such that $\lambda_n > 0$ for all $n$, the sequence
$(\lambda_n)$ is increasing and $\lambda_n \to +\infty$, and the following holds for every $n$.

* $e_n \in H^1_0(\Omega)$ and $e_n$ satisfies the weak equation (83): there is
  $u_n \in H^1_0(\Omega)$ whose function agrees almost everywhere on $\Omega$ with $e_n$ and
  $\int_\Omega \nabla u_n \cdot \nabla \varphi = \lambda_n \int_\Omega e_n \varphi$ for all
  $\varphi \in H^1_0(\Omega)$.
* $e_n \in C^\infty(\Omega)$ and $-\Delta e_n = \lambda_n e_n$ in $\Omega$: $e_n$ agrees almost
  everywhere on $\Omega$ with a function $\tilde e_n$ of class $C^\infty$ on $\Omega$ such that
  $-\Delta \tilde e_n(x) = \lambda_n \tilde e_n(x)$ at every $x \in \Omega$.

The Laplacian $\Delta$ is Mathlib's. The source derives the regularity from Section 9.6 (Remark
25): $e_n \in H^2(\omega)$, hence $e_n \in H^4(\omega)$, and so on for every
$\omega \subset\subset \Omega$, so $e_n \in C^\infty(\Omega)$. This is the backbone theorem
`Elliptic.dirichletEigenbasis_exists_contDiffOn`, which also gives the pointwise equation
(`Brezis.Chapter09.theorem_9_31_laplacian` for the $C^\infty$ representative). -/
theorem theorem_9_31_smooth (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty) :
    ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))) (lam : ℕ → ℝ),
      (∀ n, 0 < lam n) ∧ Monotone lam ∧ Tendsto lam atTop atTop ∧
      (∀ n, ∃ u : hSpace (d + 1) Ω, u ∈ hZeroSpace (d + 1) Ω ∧
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] e n ∧
        ∀ φ ∈ hZeroSpace (d + 1) Ω,
          ∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x
            = lam n * ∫ x in (Ω : Set 𝔼), e n x * SobolevMultiIndex.fn φ x) ∧
      ∀ n, ∃ e₀ : 𝔼 → ℝ, ContDiffOn ℝ ∞ e₀ Ω ∧
        (e n : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] e₀ ∧ ∀ x ∈ Ω, -Δ e₀ x = lam n * e₀ x :=
  ⟨Elliptic.dirichletEigenbasis Ω hb hne, Elliptic.dirichletEigenvalue Ω hb,
    Elliptic.dirichletEigenvalue_pos Ω hb hne, Elliptic.monotone_dirichletEigenvalue Ω hb hne,
    Elliptic.tendsto_dirichletEigenvalue_atTop Ω hb hne, theorem_9_31_weak hb hne,
    Elliptic.dirichletEigenbasis_exists_contDiffOn Ω hb hne⟩

/-- **Theorem 9.31** of [brezis2011functional], the classical equation for a $C^2$ representative.
Let $\Omega \subset \mathbb{R}^N$ be open, with $N = d + 1$, let $e \in L^2(\Omega)$ and
$\lambda \in \mathbb{R}$, and let $u \in H^1(\Omega)$ have a function that agrees almost
everywhere on $\Omega$ with $e$ and satisfy
$$\int_\Omega \nabla u \cdot \nabla \varphi = \lambda \int_\Omega e \varphi \qquad \text{for all
  } \varphi \in H^1_0(\Omega).$$
If $e$ agrees almost everywhere on $\Omega$ with a function $\tilde e$ of class $C^2$ on
$\Omega$, then $-\Delta \tilde e(x) = \lambda \tilde e(x)$ at every $x \in \Omega$.

The Laplacian $\Delta$ is Mathlib's. The proof specializes the backbone theorem
`Elliptic.laplacian_eq_of_eigenfunction`: Step D of Section 9.5, Example 1, for the equation
$-\Delta u + u = (\lambda + 1) u$, and the continuity of both sides on the open set $\Omega$. -/
theorem theorem_9_31_laplacian {e : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {lam : ℝ}
    {u : hSpace (d + 1) Ω} (hue : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] e)
    (heq : ∀ φ ∈ hZeroSpace (d + 1) Ω,
      ∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x
        = lam * ∫ x in (Ω : Set 𝔼), e x * SobolevMultiIndex.fn φ x)
    {e₀ : 𝔼 → ℝ} (hc : ContDiffOn ℝ 2 e₀ Ω)
    (he₀ : (e : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] e₀) :
    ∀ x ∈ Ω, -Δ e₀ x = lam * e₀ x := by
  refine Elliptic.laplacian_eq_of_eigenfunction Ω (U := u) (lam := lam) (fun V hV ↦ ?_) hc
    (hue.trans he₀)
  have h := heq V (SobolevMultiIndexZero.testFunctions_le hV)
  refine (Elliptic.dirichletForm_apply Ω _ _).trans (h.trans ?_)
  rw [MeasureTheory.L2.inner_eq_integral_mul]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hue] with x hx
  rw [SobolevMultiIndex.fnL_apply, hx]
  rfl

/-! ### Remark 28: the bases of $H^1_0(\Omega)$ -/

/-- **Remark 28** in Chapter 9 of [brezis2011functional], first clause. Let
$\Omega \subset \mathbb{R}^N$ be a bounded nonempty open set, with $N = d + 1$, and let $(e_n)$,
$(\lambda_n)$ be the data of Theorem 9.31. Then $(e_n / \sqrt{\lambda_n})$ is a Hilbert basis of
$H^1_0(\Omega)$ equipped with the scalar product $\int_\Omega \nabla u \cdot \nabla v$.
Precisely:

* the scalar product of the energy space of the operator $A$ of the Dirichlet form on
  $H^1_0(\Omega)$ is $\int_\Omega \nabla u \cdot \nabla v$, and
* this energy space has a Hilbert basis whose $n$-th vector is $u_n / \sqrt{\lambda_n}$, where
  $u_n \in H^1_0(\Omega)$ is the $n$-th eigenfunction of Theorem 9.31, with function $e_n$.

The operator $A$ is `Elliptic.dirichletOperator`, with $\langle Au, v \rangle_{H^1} =
\int_\Omega \nabla u \cdot \nabla v$, and the energy space is `WithEnergy`. The element $u_n$ is
`Elliptic.dirichletEigenfunction`. The proof specializes `Elliptic.hilbertBasis_energy`: the
orthonormality is (83), and the completeness follows from the basis property in $L^2(\Omega)$,
since $f \perp e_n$ in $H^1_0(\Omega)$ for all $n$ gives $\lambda_n \int_\Omega e_n f = 0$,
hence $f = 0$. -/
theorem remark_9_28 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty) :
    (∀ u v : hZeroSpace (d + 1) Ω,
      ⟪WithEnergy.equiv _ (Elliptic.dirichletOperator_isSymmetricCoercive Ω hb) u,
        WithEnergy.equiv _ (Elliptic.dirichletOperator_isSymmetricCoercive Ω hb) v⟫_ℝ
        = ∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv (u : hSpace (d + 1) Ω) i x
          * partialDeriv (v : hSpace (d + 1) Ω) i x) ∧
    ∃ b : HilbertBasis ℕ ℝ (WithEnergy (Elliptic.dirichletOperator Ω).toLinearMap
      (Elliptic.dirichletOperator_isSymmetricCoercive Ω hb)),
      ∀ n, b n = (√(Elliptic.dirichletEigenvalue Ω hb n))⁻¹
        • WithEnergy.equiv _ _ (Elliptic.dirichletEigenfunction Ω hb hne n) := by
  refine ⟨fun u v ↦ ?_, Elliptic.hilbertBasis_energy Ω hb hne⟩
  rw [WithEnergy.inner_equiv]
  exact (Elliptic.inner_dirichletOperator Ω u v).trans (Elliptic.dirichletForm_apply Ω _ _)

/-- **Remark 28** in Chapter 9 of [brezis2011functional], second clause. Let
$\Omega \subset \mathbb{R}^N$ be a bounded nonempty open set, with $N = d + 1$, and let $(e_n)$,
$(\lambda_n)$ be the data of Theorem 9.31. Then $(e_n / \sqrt{\lambda_n + 1})$ is a Hilbert
basis of $H^1_0(\Omega)$ equipped with the scalar product
$\int_\Omega (\nabla u \cdot \nabla v + uv)$. Precisely:

* the scalar product of $H^1_0(\Omega)$ is $\int_\Omega (\nabla u \cdot \nabla v + uv)$, the
  scalar product of $H^1(\Omega)$ restricted to $H^1_0(\Omega)$, and
* $H^1_0(\Omega)$ has a Hilbert basis whose $n$-th vector is $u_n / \sqrt{\lambda_n + 1}$, where
  $u_n \in H^1_0(\Omega)$ is the $n$-th eigenfunction of Theorem 9.31.

The element $u_n$ is `Elliptic.dirichletEigenfunction`. The proof specializes
`Elliptic.hilbertBasis_sobolevZero`: by (83), $\langle u_n, x \rangle_{H^1} = (\lambda_n + 1)
\langle e_n, x \rangle_{L^2}$, and the completeness follows from the basis property in
$L^2(\Omega)$. -/
theorem remark_9_28_h1 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty) :
    (∀ u v : hZeroSpace (d + 1) Ω, ⟪u, v⟫_ℝ
        = ∫ x in (Ω : Set 𝔼), ((∑ i, partialDeriv (u : hSpace (d + 1) Ω) i x
          * partialDeriv (v : hSpace (d + 1) Ω) i x)
          + SobolevMultiIndex.fn (u : hSpace (d + 1) Ω) x
            * SobolevMultiIndex.fn (v : hSpace (d + 1) Ω) x)) ∧
    ∃ b : HilbertBasis ℕ ℝ (hZeroSpace (d + 1) Ω),
      ∀ n, b n = (√(Elliptic.dirichletEigenvalue Ω hb n + 1))⁻¹
        • Elliptic.dirichletEigenfunction Ω hb hne n := by
  refine ⟨fun u v ↦ ?_, Elliptic.hilbertBasis_sobolevZero Ω hb hne⟩
  rw [Submodule.coe_inner, ← Elliptic.laplaceForm_apply_eq_inner, Elliptic.laplaceForm_apply]
  rfl

/-! ### Remark 29: smoothness up to the boundary -/

/-- **Remark 29** in Chapter 9 of [brezis2011functional], second clause. Let
$\Omega \subset \mathbb{R}^N$ be a bounded nonempty open set of class $C^\infty$, with
$N = d + 1$. Then $e_n \in C^\infty(\overline{\Omega})$ for every $n$: the $n$-th eigenfunction
$e_n$ of Theorem 9.31 agrees almost everywhere on $\Omega$ with a function $\tilde e_n$ that is
continuous on $\overline{\Omega}$ and is of class $C^\infty(\overline{\Omega})$, that is, of
class $C^\infty$ on $\Omega$ with every derivative extending continuously to
$\overline{\Omega}$.

Here $e_n$ is `Elliptic.dirichletEigenbasis Ω hb hne n`, and $C^\infty(\overline{\Omega})$ is
`ContDiffOnClosure`, the class of footnote 16 of Section 9.3. The source says that the result
follows easily from Theorem 9.25, applied to $-\Delta e_n + e_n = (\lambda_n + 1) e_n$ and
iterated (`Brezis.Chapter09.theorem_9_25_smooth`). The proof specializes
`Elliptic.exists_contDiffOn_closure_eigenfunction`. The first clause of the Remark,
$e_n \in L^\infty(\Omega)$ for a general bounded $\Omega$, is given in the source without proof
and is not formalized. -/
theorem remark_9_29 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hne : (Ω : Set 𝔼).Nonempty) (n : ℕ) :
    ∃ e₀ : 𝔼 → ℝ, ContDiffOnClosure ℝ ∞ e₀ Ω ∧ ContinuousOn e₀ (closure (Ω : Set 𝔼)) ∧
      (Elliptic.dirichletEigenbasis Ω hb hne n : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] e₀ := by
  obtain ⟨e₀, hc, h2, hae, hG⟩ := Elliptic.exists_contDiffOn_closure_eigenfunction Ω hb hne hΩ n
  refine ⟨e₀, ⟨h2, fun j _ ↦ ?_⟩, hc.continuousOn, hae⟩
  obtain ⟨G, hGc, hGe⟩ := hG j
  exact ⟨G, hGc.continuousOn, hGe.symm⟩

/-! ### Remark 30: general symmetric elliptic operators -/

/-- **Remark 30** in Chapter 9 of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be a
bounded nonempty open set, with $N = d + 1$. Let $a_{ij} \in L^\infty(\Omega)$ satisfy the
ellipticity condition (36) with a constant $\alpha > 0$,
$$\sum_{i,j} a_{ij}(x) \xi_i \xi_j \ge \alpha |\xi|^2 \qquad \text{for all } \xi \in
  \mathbb{R}^N \text{ and a.e. } x \in \Omega,$$
and the symmetry condition $a_{ij} = a_{ji}$, and let $a_0 \in L^\infty(\Omega)$. Then there
exist a Hilbert basis $(e_n)$ of $L^2(\Omega)$ and real numbers $(\lambda_n)$ with
$\lambda_n \to +\infty$ such that each $e_n$ lies in $H^1_0(\Omega)$ and satisfies (84): there
is $u_n \in H^1_0(\Omega)$ whose function agrees almost everywhere on $\Omega$ with $e_n$ and
that satisfies
$$\int_\Omega \sum_{i,j} a_{ij} \frac{\partial u_n}{\partial x_i} \frac{\partial
  \varphi}{\partial x_j} + \int_\Omega a_0 u_n \varphi = \lambda_n \int_\Omega e_n \varphi
  \qquad \text{for all } \varphi \in H^1_0(\Omega).$$

**Correction.** The source does not assume $a_{ij} = a_{ji}$. Without the symmetry the solution
operator is not self-adjoint, and there is in general no orthonormal basis of eigenfunctions.
The statement assumes it.

The ellipticity condition is `Elliptic.IsUniformlyElliptic`. The eigenvalues $\lambda_n$ need
not be positive. The proof specializes `Elliptic.exists_hilbertBasis_eigen_general`: the
construction of Theorem 9.31 applies to the form shifted by Gårding's constant $\lambda_0$,
which is Hermitian by the symmetry and coercive on $H^1_0(\Omega)$ by Gårding's inequality. Its
eigenvalues $\lambda'_n \to +\infty$ give $\lambda_n = \lambda'_n - \lambda_0$. -/
theorem remark_9_30 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty)
    {A : Fin (d + 1) → Fin (d + 1) → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))}
    {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))} {α : ℝ}
    (hA : Elliptic.IsUniformlyElliptic Ω A α) (hsymm : ∀ i j, A i j = A j i) :
    ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))) (lam : ℕ → ℝ),
      Tendsto lam atTop atTop ∧
      ∀ n, ∃ u : hSpace (d + 1) Ω, u ∈ hZeroSpace (d + 1) Ω ∧
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] e n ∧
        ∀ φ ∈ hZeroSpace (d + 1) Ω,
          (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
            + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
            = lam n * ∫ x in (Ω : Set 𝔼), e n x * SobolevMultiIndex.fn φ x := by
  obtain ⟨e, lam, hlam, h⟩ :=
    Elliptic.exists_hilbertBasis_eigen_general Ω hb.measure_lt_top.ne hne hA hsymm
  refine ⟨e, lam, hlam, fun n ↦ ?_⟩
  obtain ⟨u, hu0, hue, heq⟩ := h n
  refine ⟨u, hu0, EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) ↦
    (z : 𝔼 → ℝ)) hue), fun φ hφ ↦ ?_⟩
  rw [← generalForm_zero_drift_apply, heq φ hφ, MeasureTheory.L2.inner_eq_integral_mul]
  rfl

end Spectral

end Brezis.Chapter09
