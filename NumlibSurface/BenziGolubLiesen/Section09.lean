/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Iterate
import Numlib.Krylov.ToEuclideanLin

/-!
# Benzi, Golub and Liesen, Section 9: Krylov subspace methods

This module formalizes the projection framework for Krylov subspace methods in Section 9 of
[benzi2005numerical]. Let $A \in \mathbb{R}^{N \times N}$, $b, u_0 \in \mathbb{R}^N$, and
$r_0 = b - Au_0$. The Krylov space of order $k$ is
$$\mathcal{K}_k(A, r_0) = \operatorname{span}\{r_0, Ar_0, \dots, A^{k - 1}r_0\}.$$
A projection iterate for a constraint space $\mathcal{C}_k$ is a vector $u_k$ with
$u_k \in u_0 + \mathcal{K}_k(A, r_0)$ and $b - Au_k \perp \mathcal{C}_k$. For
$\mathcal{C}_k = \mathcal{K}_k(A, r_0)$ with $A$ symmetric positive definite (case (C)) and for
$\mathcal{C}_k = A\mathcal{K}_k(A, r_0)$ with $A$ nonsingular (case (M)), the iterate exists and is
unique (Theorem 9.1). It minimizes the energy norm of the error in case (C), and the Euclidean norm
of the residual in case (M), over the affine Krylov space and over the residual polynomials (Theorem
9.3). The best approximation theorem in Hilbert spaces (Theorem 9.2) underlies these minimality
properties. The proofs specialize results in `Numlib.Krylov.Iterate` and `Numlib.Projection.Basic`.

## Main definitions

* Equation (9.2), `BenziGolubLiesen.krylovSubspace`: the Krylov space $\mathcal{K}_k(A, r_0)$.
* Equations (9.1) and (9.3), `BenziGolubLiesen.IsProjectionIterate`:
  $u_k \in u_0 + \mathcal{K}_k(A, r_0)$ and $b - Au_k \perp \mathcal{C}_k$.
* Equation (9.4), `BenziGolubLiesen.IsSYMMLQIterate`: $u_k \in u_0 + A\mathcal{K}_k(A, r_0)$ and
  $b - Au_k \perp \mathcal{K}_k(A, r_0)$.
* Theorem 9.3, `BenziGolubLiesen.residualPolynomials`: the set $\Pi_k$ of real polynomials $p$ of
  degree at most $k$ with $p(0) = 1$.

## Main results

* Equation (9.2), `BenziGolubLiesen.krylovSubspace_eq_span`: $\mathcal{K}_k(A, r_0)$ is spanned by
  $A^j r_0$ for $j < k$.
* Equations (9.1) and (9.3), `BenziGolubLiesen.isProjectionIterate_iff`: a projection iterate also
  satisfies $r_k \in r_0 + A\mathcal{K}_k(A, r_0)$.
* Theorem 9.1, `BenziGolubLiesen.theorem_9_1`: in case (C) and in case (M), the projection iterate
  exists and is unique.
* Equation (9.4), `BenziGolubLiesen.isSYMMLQIterate_iff`: an iterate of the form (9.4) also
  satisfies $r_k \in r_0 + A\mathcal{K}_k(A, Ar_0)$.
* Equation (9.4), `BenziGolubLiesen.existsUnique_isSYMMLQIterate`: for symmetric nonsingular $A$,
  the iterate of the form (9.4) exists and is unique.
* Theorem 9.2, `BenziGolubLiesen.theorem_9_2`: a closed subspace of a Hilbert space has a unique
  best approximation to each point, characterized by orthogonality of the error.
* Theorem 9.3(C), `BenziGolubLiesen.theorem_9_3_c`: in case (C), $\|u - u_k\|_A$ is the minimum of
  the energy norm of the error, equation (9.5).
* Theorem 9.3(M), `BenziGolubLiesen.theorem_9_3_m`: in case (M), $\|b - Au_k\|$ is the minimum of
  the residual norm, equation (9.6).

## Implementation notes

* Vectors are elements of `EuclideanSpace ℝ ι` for a finite index type `ι`, and the matrix $A$ acts
  on them through `Matrix.toEuclideanLin`.
* A projection iterate is the backbone predicate `IsPetrovGalerkin` with search space
  $\mathcal{K}_k(A, r_0)$.
* Theorems 9.1, 9.3(C) and 9.3(M) carry the hypothesis $\dim \mathcal{K}_k(A, r_0) = k$. Their
  proofs do not use it, and Theorem 9.3(M) also does not use the nonsingularity of $A$.
-/

noncomputable section

open Polynomial

namespace BenziGolubLiesen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Equation (9.2)** of [benzi2005numerical]. For $A \in \mathbb{R}^{N \times N}$,
$r_0 \in \mathbb{R}^N$ and $k \in \mathbb{N}$, the **Krylov space** of order $k$ is
$$\mathcal{K}_k(A, r_0) = \operatorname{span}\{r_0, Ar_0, \dots, A^{k - 1}r_0\}.$$

The definition is `Krylov.subspace` for the linear map `Matrix.toEuclideanLin A`. For $k = 0$
the space is $\{0\}$. -/
abbrev krylovSubspace (A : Matrix ι ι ℝ) (r₀ : EuclideanSpace ℝ ι) (k : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ ι) :=
  Krylov.subspace A.toEuclideanLin r₀ k

/-- **Equation (9.2)** of [benzi2005numerical], spanning set. For $A \in \mathbb{R}^{N \times N}$,
$r_0 \in \mathbb{R}^N$ and $k \in \mathbb{N}$,
$$\mathcal{K}_k(A, r_0) = \operatorname{span}\{A^j r_0 : 0 \le j < k\}.$$
-/
theorem krylovSubspace_eq_span (A : Matrix ι ι ℝ) (r₀ : EuclideanSpace ℝ ι) (k : ℕ) :
    krylovSubspace A r₀ k =
      Submodule.span ℝ (Set.range fun j : Fin k => (A ^ (j : ℕ)).toEuclideanLin r₀) :=
  A.krylov_subspace_toEuclideanLin r₀ k

/-- **Equations (9.1) and (9.3)** of [benzi2005numerical]. Let $A \in \mathbb{R}^{N \times N}$,
$b, u_0 \in \mathbb{R}^N$, $r_0 = b - Au_0$, $k \in \mathbb{N}$, and let
$\mathcal{C}_k \subseteq \mathbb{R}^N$ be a subspace. A vector $u_k$ is a **projection iterate**
if
$$u_k \in u_0 + \mathcal{K}_k(A, r_0) \quad \text{and} \quad b - Au_k \perp \mathcal{C}_k.$$

The definition is `IsPetrovGalerkin` for `Matrix.toEuclideanLin A`, with search space
`BenziGolubLiesen.krylovSubspace A r₀ k` and constraint space $\mathcal{C}_k$. -/
abbrev IsProjectionIterate (A : Matrix ι ι ℝ) (b u₀ : EuclideanSpace ℝ ι) (k : ℕ)
    (C : Submodule ℝ (EuclideanSpace ℝ ι)) (uₖ : EuclideanSpace ℝ ι) : Prop :=
  IsPetrovGalerkin A.toEuclideanLin b u₀ (krylovSubspace A (b - A.toEuclideanLin u₀) k) C uₖ

/-- **Equations (9.1) and (9.3)** of [benzi2005numerical], residual form. Let
$A \in \mathbb{R}^{N \times N}$, $b, u_0, u_k \in \mathbb{R}^N$, $r_0 = b - Au_0$,
$r_k = b - Au_k$, and let $\mathcal{C}_k$ be a subspace. Then $u_k$ is a projection iterate for
$\mathcal{C}_k$ if and only if
$$u_k \in u_0 + \mathcal{K}_k(A, r_0), \quad r_k \in r_0 + A\mathcal{K}_k(A, r_0) \quad
  \text{and} \quad r_k \perp \mathcal{C}_k.$$
The condition on the residual follows from the condition on the iterate, since
$r_k - r_0 = -A(u_k - u_0)$. -/
theorem isProjectionIterate_iff (A : Matrix ι ι ℝ) (b u₀ : EuclideanSpace ℝ ι) (k : ℕ)
    (C : Submodule ℝ (EuclideanSpace ℝ ι)) (uₖ : EuclideanSpace ℝ ι) :
    IsProjectionIterate A b u₀ k C uₖ ↔
      uₖ - u₀ ∈ krylovSubspace A (b - A.toEuclideanLin u₀) k ∧
      (b - A.toEuclideanLin uₖ) - (b - A.toEuclideanLin u₀) ∈
        (krylovSubspace A (b - A.toEuclideanLin u₀) k).map A.toEuclideanLin ∧
      b - A.toEuclideanLin uₖ ∈ Cᗮ := by
  constructor
  · intro h
    refine ⟨h.mem, ?_, h.orth⟩
    rw [residual_eq_sub_apply_sub A.toEuclideanLin b u₀ uₖ, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.mem_map_of_mem h.mem)
  · rintro ⟨hmem, -, horth⟩
    exact ⟨hmem, horth⟩

/-- **Theorem 9.1** of [benzi2005numerical]. Let $A \in \mathbb{R}^{N \times N}$,
$b, u_0 \in \mathbb{R}^N$, $r_0 = b - Au_0$, and $k \in \mathbb{N}$ with
$\dim \mathcal{K}_k(A, r_0) = k$. Let $\mathcal{C}_k$ be a subspace, and assume one of the two
cases:

* (C) $A$ is symmetric positive definite and $\mathcal{C}_k = \mathcal{K}_k(A, r_0)$;
* (M) $A$ is nonsingular and $\mathcal{C}_k = A\mathcal{K}_k(A, r_0)$.

Then there is exactly one projection iterate $u_k$, that is, exactly one
$u_k \in u_0 + \mathcal{K}_k(A, r_0)$ with $b - Au_k \perp \mathcal{C}_k$.

The proof does not use the hypothesis $\dim \mathcal{K}_k(A, r_0) = k$. Case (C) is a Galerkin
projection and specializes `Krylov.existsUnique_isGalerkinIterate_of_isCoercive`. Case (M) is a
minimal residual projection and specializes
`Krylov.existsUnique_isMinResidualIterate_of_injective`. -/
theorem theorem_9_1 (A : Matrix ι ι ℝ) (b u₀ : EuclideanSpace ℝ ι) (k : ℕ)
    (C : Submodule ℝ (EuclideanSpace ℝ ι))
    (_hdim : Module.finrank ℝ (krylovSubspace A (b - A.toEuclideanLin u₀) k) = k)
    (hC : (A.PosDef ∧ C = krylovSubspace A (b - A.toEuclideanLin u₀) k) ∨
      (IsUnit A ∧ C = (krylovSubspace A (b - A.toEuclideanLin u₀) k).map A.toEuclideanLin)) :
    ∃! uₖ, IsProjectionIterate A b u₀ k C uₖ := by
  rcases hC with ⟨hA, rfl⟩ | ⟨hA, rfl⟩
  · exact Krylov.existsUnique_isGalerkinIterate_of_isCoercive
      hA.isSymmetricCoercive_toEuclideanLin.isCoercive b u₀ k
  · have hinj : Function.Injective A.toEuclideanLin :=
      Function.LeftInverse.injective (A.toEuclideanLin_nonsing_inv_mul_apply hA)
    simp_rw [IsProjectionIterate, ← IsMinResidual.iff_isPetrovGalerkin]
    exact Krylov.existsUnique_isMinResidualIterate_of_injective hinj b u₀ k

/-- **Equation (9.4)** of [benzi2005numerical]. Let $A \in \mathbb{R}^{N \times N}$,
$b, u_0 \in \mathbb{R}^N$, $r_0 = b - Au_0$ and $k \in \mathbb{N}$. A vector $u_k$ is an
**iterate of the form (9.4)**, the form of the SYMMLQ method, if
$$u_k \in u_0 + A\mathcal{K}_k(A, r_0) \quad \text{and} \quad b - Au_k \perp \mathcal{K}_k(A,
  r_0).$$
Here the search space is the image of the Krylov space under $A$, and the constraint space is
the Krylov space itself.

The definition is `IsPetrovGalerkin` for `Matrix.toEuclideanLin A`, with search space the image
of `BenziGolubLiesen.krylovSubspace A r₀ k` under this map. -/
abbrev IsSYMMLQIterate (A : Matrix ι ι ℝ) (b u₀ : EuclideanSpace ℝ ι) (k : ℕ)
    (uₖ : EuclideanSpace ℝ ι) : Prop :=
  let K := krylovSubspace A (b - A.toEuclideanLin u₀) k
  IsPetrovGalerkin A.toEuclideanLin b u₀ (K.map A.toEuclideanLin) K uₖ

/-- **Equation (9.4)** of [benzi2005numerical], residual form. Let $A \in \mathbb{R}^{N \times N}$,
$b, u_0, u_k \in \mathbb{R}^N$, $r_0 = b - Au_0$ and $r_k = b - Au_k$. Then $u_k$ is an iterate
of the form (9.4) if and only if
$$u_k \in u_0 + A\mathcal{K}_k(A, r_0), \quad r_k \in r_0 + A\mathcal{K}_k(A, Ar_0) \quad
  \text{and} \quad r_k \perp \mathcal{K}_k(A, r_0).$$
The condition on the residual follows from the condition on the iterate, since
$A\mathcal{K}_k(A, r_0) = \mathcal{K}_k(A, Ar_0)$. -/
theorem isSYMMLQIterate_iff (A : Matrix ι ι ℝ) (b u₀ : EuclideanSpace ℝ ι) (k : ℕ)
    (uₖ : EuclideanSpace ℝ ι) :
    let T := A.toEuclideanLin
    let r₀ := b - T u₀
    IsSYMMLQIterate A b u₀ k uₖ ↔
      uₖ - u₀ ∈ (krylovSubspace A r₀ k).map T ∧
      (b - T uₖ) - r₀ ∈ (krylovSubspace A (T r₀) k).map T ∧
      b - T uₖ ∈ (krylovSubspace A r₀ k)ᗮ := by
  intro T r₀
  have hmap : (krylovSubspace A r₀ k).map T = krylovSubspace A (T r₀) k :=
    Krylov.map_subspace_of_semiconj (N := T) (B := T) (C := T) (fun _ => rfl) r₀ k
  constructor
  · intro h
    refine ⟨h.mem, ?_, h.orth⟩
    rw [residual_eq_sub_apply_sub T b u₀ uₖ, show b - T u₀ = r₀ from rfl, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.mem_map_of_mem (hmap ▸ h.mem))
  · rintro ⟨hmem, -, horth⟩
    exact ⟨hmem, horth⟩

/-- **Equation (9.4)** of [benzi2005numerical], existence and uniqueness. Let
$A \in \mathbb{R}^{N \times N}$ be symmetric and nonsingular, let $b, u_0 \in \mathbb{R}^N$ and
$k \in \mathbb{N}$. Then there is exactly one iterate $u_k$ of the form (9.4).

This is stated in the text after equation (9.4). No condition on $\dim \mathcal{K}_k(A, r_0)$ is
needed. -/
theorem existsUnique_isSYMMLQIterate (A : Matrix ι ι ℝ) (b u₀ : EuclideanSpace ℝ ι) (k : ℕ)
    (hA : IsUnit A) (hs : A.IsSymm) : ∃! uₖ, IsSYMMLQIterate A b u₀ k uₖ := by
  let T := A.toEuclideanLin
  let K := krylovSubspace A (b - T u₀) k
  have hinj : Function.Injective T :=
    Function.LeftInverse.injective (A.toEuclideanLin_nonsing_inv_mul_apply hA)
  change ∃! uₖ, IsPetrovGalerkin T b u₀ (K.map T) K uₖ
  refine existsUnique_isPetrovGalerkin_of_finrank_eq b u₀ (K.map T) K
    (Submodule.equivMapOfInjective T hinj K).finrank_eq.symm ?_
  rintro _ ⟨z, hz, rfl⟩ hort
  have hzero : inner ℝ (T z) (T z) = 0 := by
    rw [hs.isSymmetric_toEuclideanLin z (T z)]
    exact (Submodule.mem_orthogonal K _).1 hort z hz
  exact inner_self_eq_zero.mp hzero

/-- **Theorem 9.2** of [benzi2005numerical] (best approximation in Hilbert space). Let $H$ be a real
or complex Hilbert space, let $M \subseteq H$ be a closed subspace, and let $h \in H$. Then:

* there is exactly one $m_0 \in M$ with $\|h - m_0\| = \inf_{m \in M} \|h - m\|$;
* an element $m_0 \in M$ attains this infimum if and only if $h - m_0 \perp M$.

The scalar field is any `RCLike` field, and completeness of $H$ is `CompleteSpace H`. -/
theorem theorem_9_2 {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : Submodule 𝕜 H)
    (hM : IsClosed (M : Set H)) (h : H) :
    (∃! m₀ : M, ‖h - (m₀ : H)‖ = ⨅ m : M, ‖h - (m : H)‖) ∧
      ∀ m₀ : M, (‖h - (m₀ : H)‖ = ⨅ m : M, ‖h - (m : H)‖) ↔ h - (m₀ : H) ∈ Mᗮ := by
  let : CompleteSpace M := completeSpace_coe_iff_isComplete.mpr hM.isComplete
  have hiff (m₀ : M) :
      (‖h - (m₀ : H)‖ = ⨅ m : M, ‖h - (m : H)‖) ↔ h - (m₀ : H) ∈ Mᗮ :=
    (M.norm_eq_iInf_iff_inner_eq_zero m₀.property).trans (Submodule.mem_orthogonal' _ _).symm
  refine ⟨⟨M.orthogonalProjectionOnto h, ?_, ?_⟩, hiff⟩
  · exact (hiff _).2 (M.sub_starProjection_mem_orthogonal h)
  · intro m₀ hm₀
    exact Subtype.ext (M.eq_starProjection_of_mem_orthogonal m₀.property ((hiff _).1 hm₀)).symm

/-- **Theorem 9.3** of [benzi2005numerical], the polynomial set. For $k \in \mathbb{N}$, $\Pi_k$ is
the set of real polynomials $p$ with $\deg p \le k$ and $p(0) = 1$. -/
def residualPolynomials (k : ℕ) : Set ℝ[X] :=
  {p | p.degree ≤ k ∧ p.eval 0 = 1}

/-- A real polynomial $p$ lies in $\Pi_k$ if and only if $\deg p \le k$ and $p(0) = 1$. -/
@[simp]
theorem mem_residualPolynomials {k : ℕ} {p : ℝ[X]} :
    p ∈ residualPolynomials k ↔ p.degree ≤ k ∧ p.eval 0 = 1 :=
  Iff.rfl

/-- **Theorem 9.3(C)** of [benzi2005numerical], equation (9.5). Let $A \in \mathbb{R}^{N \times N}$
be symmetric positive definite, let $u, b, u_0 \in \mathbb{R}^N$ with $Au = b$, let
$r_0 = b - Au_0$, and let $k \in \mathbb{N}$ with $\dim \mathcal{K}_k(A, r_0) = k$. Let $u_k$ be
the projection iterate for $\mathcal{C}_k = \mathcal{K}_k(A, r_0)$. Then
$$\|u - u_k\|_A = \min_{z \in u_0 + \mathcal{K}_k(A, r_0)} \|u - z\|_A = \min_{p \in \Pi_k}
  \|p(A)(u - u_0)\|_A,$$
where $\|x\|_A = (x^T A x)^{1/2}$ is the energy norm. Both minima are attained, the first at
$z = u_k$.

Each minimum is stated with `IsLeast` on the set of values. The energy norm is `energyNorm` for
`Matrix.toEuclideanLin A`, and $p(A)$ is `Polynomial.aeval`. The proof does not use the
hypothesis $\dim \mathcal{K}_k(A, r_0) = k$. -/
theorem theorem_9_3_c (A : Matrix ι ι ℝ) (b u₀ u uₖ : EuclideanSpace ℝ ι) (k : ℕ)
    (_hdim : Module.finrank ℝ (krylovSubspace A (b - A.toEuclideanLin u₀) k) = k)
    (hA : A.PosDef) (hu : A.toEuclideanLin u = b)
    (hiter : IsProjectionIterate A b u₀ k (krylovSubspace A (b - A.toEuclideanLin u₀) k) uₖ) :
    IsLeast
        ((fun z => energyNorm A.toEuclideanLin (u - z)) ''
          {z | z - u₀ ∈ krylovSubspace A (b - A.toEuclideanLin u₀) k})
        (energyNorm A.toEuclideanLin (u - uₖ)) ∧
      IsLeast
        ((fun p => energyNorm A.toEuclideanLin (aeval A.toEuclideanLin p (u - u₀))) ''
          residualPolynomials k)
        (energyNorm A.toEuclideanLin (u - uₖ)) := by
  have hc := hA.isSymmetricCoercive_toEuclideanLin
  have hg : Krylov.IsGalerkinIterate A.toEuclideanLin b u₀ k uₖ := hiter
  refine ⟨⟨⟨uₖ, hg.mem, rfl⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact IsGalerkin.energyNorm_le hc hg hu hz
  · obtain ⟨p, hp, hp₀, hres⟩ := Krylov.exists_residual_poly hg.mem
    exact ⟨p, ⟨hp, hp₀⟩, congrArg (energyNorm A.toEuclideanLin)
      (Krylov.error_eq_aeval_of_injective hc.isCoercive.injective hu hres).symm⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hpdeg, hp₀⟩ := mem_residualPolynomials.mp hp
    exact hg.energyNorm_error_le_energyNorm_aeval hc hu p hpdeg hp₀

/-- **Theorem 9.3(M)** of [benzi2005numerical], equation (9.6). Let $A \in \mathbb{R}^{N \times N}$
be nonsingular, let $b, u_0 \in \mathbb{R}^N$, let $r_0 = b - Au_0$, and let $k \in \mathbb{N}$
with $\dim \mathcal{K}_k(A, r_0) = k$. Let $u_k$ be the projection iterate for
$\mathcal{C}_k = A\mathcal{K}_k(A, r_0)$. Then
$$\|b - Au_k\| = \min_{z \in u_0 + \mathcal{K}_k(A, r_0)} \|b - Az\| = \min_{p \in \Pi_k} \|p(A)
  r_0\|,$$
where $\|\cdot\|$ is the Euclidean norm. Both minima are attained, the first at $z = u_k$.

Each minimum is stated with `IsLeast` on the set of values, and $p(A)$ is `Polynomial.aeval`.
The proof uses neither the nonsingularity of $A$ nor the hypothesis
$\dim \mathcal{K}_k(A, r_0) = k$. -/
theorem theorem_9_3_m (A : Matrix ι ι ℝ) (b u₀ uₖ : EuclideanSpace ℝ ι) (k : ℕ)
    (_hdim : Module.finrank ℝ (krylovSubspace A (b - A.toEuclideanLin u₀) k) = k)
    (_hA : IsUnit A)
    (hiter : IsProjectionIterate A b u₀ k
      ((krylovSubspace A (b - A.toEuclideanLin u₀) k).map A.toEuclideanLin) uₖ) :
    IsLeast
        ((fun z => ‖b - A.toEuclideanLin z‖) ''
          {z | z - u₀ ∈ krylovSubspace A (b - A.toEuclideanLin u₀) k})
        ‖b - A.toEuclideanLin uₖ‖ ∧
      IsLeast
        ((fun p => ‖aeval A.toEuclideanLin p (b - A.toEuclideanLin u₀)‖) ''
          residualPolynomials k)
        ‖b - A.toEuclideanLin uₖ‖ := by
  have hm : Krylov.IsMinResidualIterate A.toEuclideanLin b u₀ k uₖ :=
    IsMinResidual.iff_isPetrovGalerkin.mpr hiter
  refine ⟨⟨⟨uₖ, hm.mem, rfl⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hm.min z hz
  · obtain ⟨p, hp, hp₀, hres⟩ := Krylov.exists_residual_poly hm.mem
    exact ⟨p, ⟨hp, hp₀⟩, congrArg norm hres.symm⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hpdeg, hp₀⟩ := mem_residualPolynomials.mp hp
    exact hm.norm_residual_le_norm_aeval p hpdeg hp₀

end BenziGolubLiesen
