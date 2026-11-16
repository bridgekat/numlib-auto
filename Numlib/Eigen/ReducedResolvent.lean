/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.Normal
import Numlib.Eigen.Perturbation
import Numlib.Eigen.PowerMethod

/-!
# The reduced resolvent and the condition number of an eigenvector

Let $E$ be a finite-dimensional normed space over an algebraically closed field $\mathbb{K}$ (in
practice $\mathbb{C}$), let $A$ be a linear operator on $E$, and let $l \in \mathbb{K}$. Let $P$ be
the spectral projector of $l$: the projection onto the generalized eigenspace of $l$ along the sum
of the generalized eigenspaces of the other eigenvalues. The resolvent $(A - z)^{-1}$ blows up at an
eigenvalue $l$, but only in the direction of the generalized eigenspace of $l$. On the complementary
invariant subspace $\ker P$ the operator $A - l$ is still invertible, and its inverse there is the
**reduced resolvent** $S(l)$ of [saad2011numerical], §3.3.2. This module defines the operator
$S(l)(I - P)$, the reduced resolvent extended by zero across the generalized eigenspace. It is
characterized by the identity (3.40) of the source,
$$S(l)(I - P)(A - l) x = x - Px,$$
and its operator norm is the condition number $\operatorname{Cond}(u)$ of an eigenvector $u$ for $l$
(Definition 3.2 of [saad2011numerical]).

The name is justified by (3.43) of the source: along a differentiable branch of eigenpairs of
$A + tB$ normalized by $P u(t) = u$, the eigenvector moves at the rate $u'(0) = -S(l)(I - P) B u$,
so $\|u'(0)\| \le \operatorname{Cond}(u) \, \|B\| \, \|u\|$. This is the first-order term of
Property 5.5 of [quarteroni2000numerical], whose constant
$1 / \min_{j \neq k} |\lambda_k - \lambda_j|$ is the condition number only for a normal $A$. For a
normal operator the condition number is computed: $\operatorname{Cond}(u) = 1 /
\operatorname{dist}(l, \sigma(A) \setminus \{l\})$, which for a Hermitian operator is (3.45) of
[saad2011numerical]. At an algebraically simple eigenvalue the projector is $Px = (\langle w, x
\rangle / \langle w, u \rangle) \, u$ for a left eigenvector $w$, (3.42) of the source.

## Main definitions

* `Module.End.reducedResolventEquiv`: the operator $A - l$ as an automorphism of the complementary
  invariant subspace $\ker P$; its inverse is $S(l)$.
* `Module.End.reducedResolvent`: the operator $S(l)(I - P)$ on $E$.
* `Module.End.eigenvectorCondNumber`: the condition number
  $\operatorname{Cond}(u) = \|S(l)(I - P)\|$.

## Main results

* `Module.End.reducedResolvent_apply_sub_smul`: $S(l)(I - P)(A - l) x = x - Px$ for every $x$.
* `Module.End.reducedResolvent_apply_of_mem_eigenspace`: on the eigenspace of $\mu \neq l$, the
  reduced resolvent is multiplication by $(\mu - l)^{-1}$.
* `Module.End.eigenvectorCondNumber_eq_inv_infDist_of_isStarNormal`: for a normal $A$,
  $\operatorname{Cond}(u) = 1 / \operatorname{dist}(l, \sigma(A) \setminus \{l\})$.
* `Module.End.deriv_eigenvector_perturbation`: along a branch of eigenpairs of $A + tB$ normalized
  by $P u(t) = u(0)$, $u'(0) = -S(l)(I - P) B u(0)$.
* `Module.End.norm_deriv_eigenvector_perturbation_le`: under the same hypotheses, $\|u'(0)\| \le
  \operatorname{Cond}(u) \, \|B\| \, \|u(0)\|$.
* `Module.End.spectralProjector_apply_of_finrank_eq_one`: at an algebraically simple eigenvalue,
  $Px = (\langle w, x \rangle / \langle w, u \rangle) \, u$.

## Implementation notes

* Every result rests on the splitting `Krylov.isCompl_maxGenEigenspace` of
  `Numlib.Eigen.PowerMethod`, which is why this module imports that one. The projector $P$ is the
  oblique `Module.End.spectralProjector A (· = l)`, not an orthogonal projection, so no inner
  product is used and the space is only a normed space. The hypotheses that $\mathbb{K}$ is
  algebraically closed and $E$ is finite-dimensional make the generalized eigenspaces span $E$, and
  make the restricted $A - l$ surjective because it is injective.
* `Module.End.reducedResolvent` is $S(l)(I - P)$ and not $S(l)$, because every statement uses the
  composite: $S(l)$ alone is a map $\ker P \to \ker P$. If $l$ is not an eigenvalue, then $P = 0$
  and the reduced resolvent is the resolvent $(A - l)^{-1}$.
* The complementary invariant subspace $\ker P$ is `A.spectralSubspace (· ≠ l)`, the sum of the
  generalized eigenspaces of the eigenvalues other than $l$.
* The condition number of a normal operator is evaluated in a section that gives $E$ an inner
  product. It needs no identification of `Module.End.spectralProjector` with an orthogonal
  projection, only that the projector vanishes on the complementary invariant subspace.
* The normalization $\langle w, u(t) \rangle = \langle w, u \rangle$ of the branch built in
  `Numlib.Eigen.Perturbation` is the normalization $P u(t) = u$ used here, by
  `Module.End.spectralProjector_apply_of_finrank_eq_one`.
-/

open Krylov

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] (A : Module.End 𝕜 E) (l : 𝕜)

omit [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] in
/-- Let $A$ be a linear operator on $E$ and $l \in \mathbb{K}$. The sum $\ker P$ of the generalized
eigenspaces of the eigenvalues other than $l$ is invariant under $A - l$, because it is
invariant under $A$. -/
theorem mapsTo_sub_smul_one : ∀ w ∈ A.spectralSubspace (· ≠ l),
    (A - l • (1 : Module.End 𝕜 E)) w ∈ A.spectralSubspace (· ≠ l) := fun w hw => by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  exact Submodule.sub_mem _ (apply_mem_spectralSubspace hw) (Submodule.smul_mem _ _ hw)

/-- The restriction of $A - l$ to the complementary invariant subspace $\ker P$ is injective.

A vector that $A - l$ maps to $0$ is an eigenvector for $l$, so it lies in the generalized
eigenspace of $l$. That eigenspace meets $\ker P$ only in $0$. -/
theorem injective_restrict_sub_smul_one :
    Function.Injective ((A - l • (1 : Module.End 𝕜 E)).restrict (mapsTo_sub_smul_one A l)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨w, hw⟩ h0
  have h1 : (A - l • (1 : Module.End 𝕜 E)) w = 0 := congrArg Subtype.val h0
  have heig : w ∈ A.eigenspace l := by
    rw [Module.End.mem_eigenspace_iff]
    simpa using sub_eq_zero.1 h1
  have hmem : w ∈ (A.maxGenEigenspace l) ⊓ A.spectralSubspace (· ≠ l) :=
    ⟨Module.End.eigenspace_le_maxGenEigenspace heig, hw⟩
  simpa using (disjoint_iff_inf_le.1 (Krylov.isCompl_maxGenEigenspace A l).disjoint) hmem

/-- The operator $A - l$ as a linear automorphism of the complementary invariant subspace $\ker P$,
the sum of the generalized eigenspaces of the eigenvalues other than $l$. Its inverse is the
**reduced resolvent** $S(l)$ of [saad2011numerical], §3.3.2.

The restriction is injective by `Module.End.injective_restrict_sub_smul_one`, so it is bijective
because $E$ is finite-dimensional. -/
noncomputable def reducedResolventEquiv :
    A.spectralSubspace (· ≠ l) ≃ₗ[𝕜] A.spectralSubspace (· ≠ l) :=
  LinearEquiv.ofBijective ((A - l • (1 : Module.End 𝕜 E)).restrict (mapsTo_sub_smul_one A l))
    ⟨injective_restrict_sub_smul_one A l,
      LinearMap.injective_iff_surjective.1 (injective_restrict_sub_smul_one A l)⟩

/-- For every $x \in E$, the vector $x - Px$ lies in the complementary invariant subspace $\ker P$.
-/
theorem sub_spectralProjector_mem_iSup (x : E) :
    (1 - A.spectralProjector (· = l)) x ∈ A.spectralSubspace (· ≠ l) :=
  sub_spectralProjector_mem (A := A) (p := (· = l)) x

/-- The **reduced resolvent** of $A$ at $l$, extended by zero ([saad2011numerical], §3.3.2): the
linear operator $S(l)(I - P)$ on $E$. It sends $x$ to the unique $y \in \ker P$ with
$$(A - l) y = x - Px.$$
Here $P$ is the spectral projector of $l$ and $\ker P$ is the sum of the generalized eigenspaces
of the eigenvalues other than $l$.

$S(l)$ alone is defined only on $\ker P$. The composite with $I - P$ is defined on $E$, and
Definition 3.2 and the eigenvector expansion (3.43) of the source use it.
`Module.End.reducedResolvent_apply_sub_smul` is the identity (3.40) of the source, which
characterizes it. If $l$ is not an eigenvalue of $A$, then $P = 0$ and this is the resolvent
$(A - l)^{-1}$. -/
noncomputable def reducedResolvent : E →ₗ[𝕜] E :=
  (A.spectralSubspace (· ≠ l)).subtype ∘ₗ
    ((reducedResolventEquiv A l).symm.toLinearMap ∘ₗ
      LinearMap.codRestrict _ (1 - A.spectralProjector (· = l))
        (sub_spectralProjector_mem_iSup A l))

/-- The value of the reduced resolvent at $x$ is $S(l)$ applied to $x - Px$. -/
theorem reducedResolvent_apply (x : E) :
    reducedResolvent A l x =
      ((reducedResolventEquiv A l).symm
        ⟨(1 - A.spectralProjector (· = l)) x, sub_spectralProjector_mem_iSup A l x⟩ : E) :=
  rfl

/-- The reduced resolvent takes its values in the complementary invariant subspace $\ker P$. -/
theorem reducedResolvent_apply_mem (x : E) :
    reducedResolvent A l x ∈ A.spectralSubspace (· ≠ l) :=
  ((reducedResolventEquiv A l).symm
    ⟨_, sub_spectralProjector_mem_iSup A l x⟩ :
      A.spectralSubspace (· ≠ l)).2

/-- The spectral projector $P$ of $l$ takes its values in the generalized eigenspace of $l$. -/
theorem spectralProjector_apply_mem_maxGenEigenspace (x : E) :
    A.spectralProjector (· = l) x ∈ A.maxGenEigenspace l := by
  have h := spectralProjector_apply_mem (A := A) (p := (· = l)) x
  rwa [spectralSubspace_eq] at h

omit [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] in
/-- The generalized eigenspace of $l$ is invariant under $A - l$. -/
theorem sub_smul_one_apply_mem_maxGenEigenspace {y : E} (hy : y ∈ A.maxGenEigenspace l) :
    (A - l • (1 : Module.End 𝕜 E)) y ∈ A.maxGenEigenspace l := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  exact Submodule.sub_mem _ (A.mapsTo_maxGenEigenspace_of_comm (Commute.refl A) l hy)
    (Submodule.smul_mem _ _ hy)

/-- The spectral projector $P$ of $l$ fixes every vector of the generalized eigenspace of $l$. -/
theorem spectralProjector_apply_of_mem_maxGenEigenspace {y : E} (hy : y ∈ A.maxGenEigenspace l) :
    A.spectralProjector (· = l) y = y := by
  refine spectralProjector_apply_of_mem ?_
  rwa [spectralSubspace_eq]

/-- **The defining identity of the reduced resolvent.** For every $x \in E$,
$$S(l)(I - P)(A - l) x = x - Px.$$
This is (3.40) of [saad2011numerical].

Split $x = Px + (x - Px)$. Both summands lie in subspaces invariant under $A - l$, so $I - P$
removes the image of the first and fixes the image of the second. What is left is
$(A - l)(x - Px)$, and the inverse of $A - l$ on $\ker P$ returns $x - Px$. -/
theorem reducedResolvent_apply_sub_smul (x : E) :
    reducedResolvent A l ((A - l • (1 : Module.End 𝕜 E)) x)
      = x - A.spectralProjector (· = l) x := by
  set P := A.spectralProjector (· = l) with hP
  set T := A - l • (1 : Module.End 𝕜 E) with hT
  have hw : x - P x ∈ A.spectralSubspace (· ≠ l) :=
    sub_spectralProjector_mem (A := A) (p := (· = l)) x
  have hTPx : T (P x) ∈ A.maxGenEigenspace l :=
    sub_smul_one_apply_mem_maxGenEigenspace A l (spectralProjector_apply_mem_maxGenEigenspace A l x)
  have hkey : (1 - P) (T x) = T (x - P x) := by
    have h1 : P (T (P x)) = T (P x) := spectralProjector_apply_of_mem_maxGenEigenspace A l hTPx
    have h2 : P (T (x - P x)) = 0 :=
      spectralProjector_apply_eq_zero_iff.2 (mapsTo_sub_smul_one A l _ hw)
    have h3 : T x = T (P x) + T (x - P x) := by rw [← map_add]; congr 1; abel
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [h3, map_add, h1, h2]
    abel
  have hval : ((reducedResolventEquiv A l) ⟨x - P x, hw⟩ : E) = T (x - P x) := rfl
  rw [reducedResolvent_apply]
  have hmk : (⟨(1 - P) (T x), sub_spectralProjector_mem_iSup A l (T x)⟩ :
      A.spectralSubspace (· ≠ l)) =
        (reducedResolventEquiv A l) ⟨x - P x, hw⟩ :=
    Subtype.ext (hkey.trans hval.symm)
  rw [hmk, LinearEquiv.symm_apply_apply]

/-- The reduced resolvent vanishes on the generalized eigenspace of $l$: $S(l)(I - P) y = 0$ for
every $y$ in it. This is where the resolvent itself is singular. -/
@[simp]
theorem reducedResolvent_apply_of_mem_maxGenEigenspace {y : E} (hy : y ∈ A.maxGenEigenspace l) :
    reducedResolvent A l y = 0 := by
  have h : (1 - A.spectralProjector (· = l)) y = 0 := by
    simp [spectralProjector_apply_of_mem_maxGenEigenspace A l hy]
  rw [reducedResolvent_apply]
  simp only [h]
  simp [← Submodule.coe_zero]

/-- **The condition number of an eigenvector** ([saad2011numerical], Definition 3.2): the operator
norm
$$\operatorname{Cond}(u) = \|S(l)(I - P)\|$$
of the reduced resolvent of $A$ at $l$.

It measures how far the eigenvector of a simple eigenvalue $l$ moves under a perturbation of
$A$. By (3.43) of the source, $u'(0) = -S(l)(I - P) B u$ for the branch normalized by
$P u(t) = u$, so the first-order displacement is at most
$\operatorname{Cond}(u) \, \|B\| \, \|u\|$. For a Hermitian $A$ it is $1 /
\operatorname{dist}(l, \sigma(A) \setminus \{l\})$, the $1 / \delta$ of
`LinearMap.IsSymmetric.sin_angle_le_norm_residual_div`. In general the spectrum alone does not
control it. The definition takes the norm of `LinearMap.toContinuousLinearMap` of the reduced
resolvent, and it is defined for every $l$, also when $l$ is not an eigenvalue. -/
noncomputable def eigenvectorCondNumber : ℝ :=
  ‖LinearMap.toContinuousLinearMap (reducedResolvent A l)‖

/-- The condition number of an eigenvector is nonnegative. -/
theorem eigenvectorCondNumber_nonneg : 0 ≤ eigenvectorCondNumber A l := norm_nonneg _

/-- For every $x \in E$,
$$\|S(l)(I - P) x\| \le \operatorname{Cond}(u) \, \|x\|.$$
This is the bound for which the condition number is defined. -/
theorem norm_reducedResolvent_apply_le (x : E) :
    ‖reducedResolvent A l x‖ ≤ eigenvectorCondNumber A l * ‖x‖ :=
  (LinearMap.toContinuousLinearMap (reducedResolvent A l)).le_opNorm x

/-! ### The condition number of an eigenvector of a normal operator -/

section Normal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] {A : Module.End 𝕜 E} {l : 𝕜}

/-- Let $E$ be a finite-dimensional inner product space over an algebraically closed $\mathbb{K}$,
let $A$ be a linear operator on $E$, and let $\mu \neq l$. For every $x$ in the eigenspace of
$\mu$,
$$S(l)(I - P) x = (\mu - l)^{-1} x.$$

On this eigenspace $A - l$ is multiplication by $\mu - l$, and the spectral projector of $l$
vanishes. No normality is needed. -/
theorem reducedResolvent_apply_of_mem_eigenspace {μ : 𝕜} (hμ : μ ≠ l) {x : E}
    (hx : x ∈ A.eigenspace μ) : reducedResolvent A l x = (μ - l)⁻¹ • x := by
  have hμl : μ - l ≠ 0 := sub_ne_zero.2 hμ
  have hAx : A x = μ • x := Module.End.mem_eigenspace_iff.1 hx
  have hmem : (μ - l)⁻¹ • x ∈ A.spectralSubspace (· ≠ l) :=
    maxGenEigenspace_le_spectralSubspace (A := A) (p := (· ≠ l)) hμ
      (Submodule.smul_mem _ _ (Module.End.eigenspace_le_maxGenEigenspace hx))
  have hAy : (A - l • (1 : Module.End 𝕜 E)) ((μ - l)⁻¹ • x) = x := by
    have hstep : (A - l • (1 : Module.End 𝕜 E)) x = (μ - l) • x := by
      simp [hAx, sub_smul]
    rw [map_smul, hstep, smul_smul, inv_mul_cancel₀ hμl, one_smul]
  have hP : A.spectralProjector (· = l) ((μ - l)⁻¹ • x) = 0 :=
    spectralProjector_apply_eq_zero_iff.2 hmem
  have h := reducedResolvent_apply_sub_smul A l ((μ - l)⁻¹ • x)
  rwa [hAy, hP, sub_zero] at h

/-- Let $A$ be a normal operator on a finite-dimensional inner product space $E$ of dimension $n$
over an algebraically closed $\mathbb{K}$, with orthonormal eigenvector basis
$e_0, \dots, e_{n-1}$ and eigenvalues $\lambda_0, \dots, \lambda_{n-1}$. Then for each $j$,
$$S(l)(I - P) e_j = \begin{cases} 0 & \text{if } \lambda_j = l, \\ (\lambda_j - l)^{-1} e_j &
  \text{if } \lambda_j \neq l. \end{cases}$$

The basis and the eigenvalues are `LinearMap.IsStarNormal.eigenvectorBasis` and
`LinearMap.IsStarNormal.eigenvalues`. -/
theorem reducedResolvent_apply_eigenvectorBasis (hA : IsStarNormal A) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (l : 𝕜) (j : Fin n) :
    reducedResolvent A l (LinearMap.IsStarNormal.eigenvectorBasis hA hn j)
      = (if LinearMap.IsStarNormal.eigenvalues hA hn j = l then 0
          else (LinearMap.IsStarNormal.eigenvalues hA hn j - l)⁻¹) •
        LinearMap.IsStarNormal.eigenvectorBasis hA hn j := by
  have hmem : LinearMap.IsStarNormal.eigenvectorBasis hA hn j
      ∈ A.eigenspace (LinearMap.IsStarNormal.eigenvalues hA hn j) :=
    Module.End.mem_eigenspace_iff.2 (LinearMap.IsStarNormal.apply_eigenvectorBasis hA hn j)
  by_cases h : LinearMap.IsStarNormal.eigenvalues hA hn j = l
  · rw [ite_eq_left h, zero_smul]
    refine reducedResolvent_apply_of_mem_maxGenEigenspace A l ?_
    rw [← h]
    exact Module.End.eigenspace_le_maxGenEigenspace hmem
  · rw [ite_eq_right h]
    exact reducedResolvent_apply_of_mem_eigenspace h hmem

/-- Each eigenvalue in the eigenvector basis of a normal operator lies in the spectrum of the
operator. -/
private theorem eigenvalues_mem_spectrum (hA : IsStarNormal A) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (j : Fin n) :
    LinearMap.IsStarNormal.eigenvalues hA hn j ∈ spectrum 𝕜 A := by
  refine Module.End.hasEigenvalue_iff_mem_spectrum.1 (Module.End.hasEigenvalue_of_hasEigenvector
    (x := LinearMap.IsStarNormal.eigenvectorBasis hA hn j) ⟨?_, ?_⟩)
  · exact Module.End.mem_eigenspace_iff.2 (LinearMap.IsStarNormal.apply_eigenvectorBasis hA hn j)
  · exact (LinearMap.IsStarNormal.eigenvectorBasis hA hn).toBasis.ne_zero j

/-- Let $A$ be a normal operator on a finite-dimensional inner product space $E$ over an
algebraically closed $\mathbb{K}$. For every $l \in \mathbb{K}$ and $x \in E$,
$$\|S(l)(I - P) x\| \le \frac{\|x\|}{\operatorname{dist}(l, \sigma(A) \setminus \{l\})}.$$

In the orthonormal eigenvector basis the reduced resolvent is diagonal, with the entries
$(\mu - l)^{-1}$ for the eigenvalues $\mu \neq l$ and $0$ for $\mu = l$. The distance is
`Metric.infDist`, which is $0$ to the empty set, and the inverse of $0$ is $0$. -/
theorem norm_reducedResolvent_apply_le_inv_infDist (hA : IsStarNormal A) (l : 𝕜) (x : E) :
    ‖reducedResolvent A l x‖ ≤ (Metric.infDist l (spectrum 𝕜 A \ {l}))⁻¹ * ‖x‖ := by
  classical
  set n := Module.finrank 𝕜 E with hnn
  have hn : Module.finrank 𝕜 E = n := rfl
  set b := LinearMap.IsStarNormal.eigenvectorBasis hA hn with hb
  set lam := LinearMap.IsStarNormal.eigenvalues hA hn with hlam
  set δ := Metric.infDist l (spectrum 𝕜 A \ {l}) with hδ
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg
  set c : Fin n → 𝕜 := fun j => if lam j = l then 0 else (lam j - l)⁻¹ with hc
  -- every diagonal entry is at most `δ⁻¹` in modulus
  have hcbound : ∀ j, ‖c j‖ ≤ δ⁻¹ := by
    intro j
    by_cases h : lam j = l
    · have hcj : c j = 0 := by
        simp only [hc]
        exact ite_eq_left h
      rw [hcj, norm_zero]
      exact inv_nonneg.2 hδ0
    · have hmem : lam j ∈ spectrum 𝕜 A \ {l} :=
        ⟨eigenvalues_mem_spectrum hA hn j, by simpa using h⟩
      have hfin : (spectrum 𝕜 A \ {l}).Finite :=
        (Module.End.finite_spectrum A).subset Set.sdiff_subset
      have hne : (spectrum 𝕜 A \ {l}).Nonempty := ⟨lam j, hmem⟩
      have hlnot : l ∉ spectrum 𝕜 A \ {l} := fun hcon => hcon.2 rfl
      have hδpos : 0 < δ := (hfin.isClosed.notMem_iff_infDist_pos hne).1 hlnot
      have hle : δ ≤ ‖lam j - l‖ := by
        have h2 := Metric.infDist_le_dist_of_mem (x := l) hmem
        rw [dist_eq_norm, norm_sub_rev] at h2
        rw [hδ]
        exact h2
      have hcj : c j = (lam j - l)⁻¹ := by
        simp only [hc]
        exact ite_eq_right h
      rw [hcj, norm_inv]
      exact inv_anti₀ hδpos hle
  -- the reduced resolvent is diagonal in the eigenvector basis
  have hSx : reducedResolvent A l x
      = b.repr.symm (WithLp.toLp 2 fun j => b.repr x j * c j) := by
    rw [← OrthonormalBasis.sum_repr_symm]
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hb, reducedResolvent_apply_eigenvectorBasis hA hn l j, smul_smul]
  have hnormS : ‖reducedResolvent A l x‖ = √(∑ j, ‖b.repr x j * c j‖ ^ 2) := by
    rw [hSx, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  have hnormx : ‖x‖ = √(∑ j, ‖b.repr x j‖ ^ 2) := by
    conv_lhs => rw [← b.repr.norm_map x]
    rw [EuclideanSpace.norm_eq]
  rw [hnormS, hnormx]
  have hsum : ∑ j, ‖b.repr x j * c j‖ ^ 2 ≤ (δ⁻¹) ^ 2 * ∑ j, ‖b.repr x j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, mul_pow]
    calc ‖b.repr x j‖ ^ 2 * ‖c j‖ ^ 2 ≤ ‖b.repr x j‖ ^ 2 * (δ⁻¹) ^ 2 := by
          gcongr
          exact hcbound j
      _ = (δ⁻¹) ^ 2 * ‖b.repr x j‖ ^ 2 := by ring
  calc √(∑ j, ‖b.repr x j * c j‖ ^ 2) ≤ √((δ⁻¹) ^ 2 * ∑ j, ‖b.repr x j‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = δ⁻¹ * √(∑ j, ‖b.repr x j‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (inv_nonneg.2 hδ0)]

/-- **The condition number of an eigenvector of a normal operator.** Let $A$ be a normal operator on
a finite-dimensional inner product space $E$ over an algebraically closed $\mathbb{K}$, and let
$l \in \mathbb{K}$. Then
$$\operatorname{Cond}(u) = \frac{1}{\operatorname{dist}(l, \sigma(A) \setminus \{l\})}.$$
For a Hermitian operator this is (3.45) of [saad2011numerical].

On the eigenspace of $\mu$ the reduced resolvent is multiplication by $(\mu - l)^{-1}$, and the
eigenspaces of a normal operator are orthogonal and span $E$. So the operator norm is the
largest of the $|\mu - l|^{-1}$ over the eigenvalues $\mu \neq l$, and the largest is attained
because the spectrum is finite. Both sides are $0$ when $l$ is the only eigenvalue, because
`Metric.infDist` to the empty set is $0$ and the inverse of $0$ is $0$. -/
theorem eigenvectorCondNumber_eq_inv_infDist_of_isStarNormal (hA : IsStarNormal A) (l : 𝕜) :
    eigenvectorCondNumber A l = (Metric.infDist l (spectrum 𝕜 A \ {l}))⁻¹ := by
  set δ := Metric.infDist l (spectrum 𝕜 A \ {l}) with hδ
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hδ0) fun x => ?_) ?_
  · exact norm_reducedResolvent_apply_le_inv_infDist hA l x
  · rcases Set.eq_empty_or_nonempty (spectrum 𝕜 A \ {l}) with hemp | hne
    · rw [hδ, hemp, Metric.infDist_empty, inv_zero]
      exact eigenvectorCondNumber_nonneg A l
    · have hfin : (spectrum 𝕜 A \ {l}).Finite :=
        (Module.End.finite_spectrum A).subset Set.sdiff_subset
      obtain ⟨μ, hμ, hdist⟩ := hfin.isCompact.exists_infDist_eq_dist hne l
      have hμl : μ ≠ l := fun h => hμ.2 (by simpa using h)
      obtain ⟨x, hxmem, hx0⟩ :=
        (Module.End.hasEigenvalue_iff_mem_spectrum.2 hμ.1).exists_hasEigenvector
      have hxnorm : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hval : reducedResolvent A l x = (μ - l)⁻¹ • x :=
        reducedResolvent_apply_of_mem_eigenspace hμl hxmem
      have hdelta : δ = ‖μ - l‖ := by
        rw [hδ, hdist, dist_eq_norm, norm_sub_rev]
      have hnorm : ‖reducedResolvent A l x‖ = δ⁻¹ * ‖x‖ := by
        rw [hval, norm_smul, norm_inv, hdelta]
      have hle := norm_reducedResolvent_apply_le A l x
      rw [hnorm] at hle
      exact le_of_mul_le_mul_right (by linarith) hxnorm

/-- **The condition number of an eigenvector of a Hermitian operator.** Let $A$ be a symmetric
operator on a finite-dimensional inner product space $E$ over an algebraically closed
$\mathbb{K}$, and let $l \in \mathbb{K}$. Then
$$\operatorname{Cond}(u) = \frac{1}{\operatorname{dist}(l, \sigma(A) \setminus \{l\})}.$$
This is (3.45) of [saad2011numerical].

It is the case of `Module.End.eigenvectorCondNumber_eq_inv_infDist_of_isStarNormal` that the
source states. The value is the $1 / \delta$ of
`LinearMap.IsSymmetric.sin_angle_le_norm_residual_div`. As in the normal case, both sides are
$0$ when $l$ is the only eigenvalue. -/
theorem eigenvectorCondNumber_eq_inv_dist_of_isSymmetric (hA : A.IsSymmetric) (l : 𝕜) :
    eigenvectorCondNumber A l = (Metric.infDist l (spectrum 𝕜 A \ {l}))⁻¹ :=
  eigenvectorCondNumber_eq_inv_infDist_of_isStarNormal
    ((LinearMap.isSymmetric_iff_isSelfAdjoint A).1 hA).isStarNormal l

end Normal

section Deriv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E]

/-- **The derivative of an eigenvector.** Let $E$ be a finite-dimensional normed space over an
algebraically closed $\mathbb{K}$, let $A, B$ be linear operators on $E$, and let $P$ be the
spectral projector of $l$ for $A$. Let $t \mapsto (\mu(t), u(t))$ satisfy
$$A u(t) + t B u(t) = \mu(t) \, u(t) \quad \text{and} \quad P u(t) = u(0) \qquad \text{for all }
  t \in \mathbb{K},$$
with $\mu(0) = l$, and let $u$ and $\mu$ be differentiable at $0$ with derivatives $u'$ and
$\mu'$. Then
$$u' = -S(l)(I - P) B u(0).$$
This is (3.43) of [saad2011numerical], and the first-order term of Property 5.5 of
[quarteroni2000numerical].

The derivative of the eigenvalue equation at $0$ is $(A - l) u' = \mu' u(0) - B u(0)$, and the
derivative of the normalization is $P u' = 0$. So $u' = (I - P) u' = S(l)(I - P)(A - l) u'$ by
`Module.End.reducedResolvent_apply_sub_smul`, and $S(l)(I - P)$ vanishes at $u(0)$, which lies
in the generalized eigenspace of $l$. -/
theorem deriv_eigenvector_perturbation {A B : Module.End 𝕜 E} {u : 𝕜 → E} {mu : 𝕜 → 𝕜} {u' : E}
    {mu' l : 𝕜} (hu : HasDerivAt u u' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ t, A (u t) + t • B (u t) = mu t • u t) (hlam : mu 0 = l)
    (hnorm : ∀ t, A.spectralProjector (· = l) (u t) = u 0) :
    u' = -(reducedResolvent A l (B (u 0))) := by
  set P := A.spectralProjector (· = l) with hP
  have hA : HasDerivAt (fun t : 𝕜 => A (u t)) (A u') 0 := by
    simpa [Function.comp_def] using
      (LinearMap.toContinuousLinearMap A).hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hu
  have hB : HasDerivAt (fun t : 𝕜 => B (u t)) (B u') 0 := by
    simpa [Function.comp_def] using
      (LinearMap.toContinuousLinearMap B).hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hu
  have hPd : HasDerivAt (fun t : 𝕜 => P (u t)) (P u') 0 := by
    simpa [Function.comp_def] using
      (LinearMap.toContinuousLinearMap P).hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hu
  -- differentiate the eigen-equation
  have htB : HasDerivAt (fun t : 𝕜 => t • B (u t)) (B (u 0)) 0 := by
    have hid : HasDerivAt (fun t : 𝕜 => t) 1 0 := hasDerivAt_id 0
    have h := HasDerivAt.smul hid hB
    rw [zero_smul, one_smul, zero_add] at h
    exact h
  have hf : HasDerivAt (fun t : 𝕜 => mu t • u t) (A u' + B (u 0)) 0 :=
    HasDerivAt.congr_of_eventuallyEq (hA.add htB)
      (Filter.Eventually.of_forall fun t => (heig t).symm)
  have hderiv : A u' + B (u 0) = mu 0 • u' + mu' • u 0 := hf.unique (HasDerivAt.smul hmu hu)
  rw [hlam] at hderiv
  -- differentiate the normalization
  have hPu' : P u' = 0 := by
    have hconst : HasDerivAt (fun t : 𝕜 => P (u t)) 0 0 :=
      (hasDerivAt_const (0 : 𝕜) (u 0)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => hnorm t)
    exact hPd.unique hconst
  -- assemble
  have hsub : (A - l • (1 : Module.End 𝕜 E)) u' = mu' • u 0 - B (u 0) := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    have : A u' = l • u' + mu' • u 0 - B (u 0) := by rw [← hderiv]; abel
    rw [this]
    abel
  have hkey := reducedResolvent_apply_sub_smul A l u'
  rw [hsub, ← hP, hPu', sub_zero, map_sub, map_smul] at hkey
  have hu0 : u 0 ∈ A.maxGenEigenspace l := by
    rw [← hnorm 0]
    exact spectralProjector_apply_mem_maxGenEigenspace A l (u 0)
  rw [reducedResolvent_apply_of_mem_maxGenEigenspace A l hu0, smul_zero, zero_sub] at hkey
  exact hkey.symm

/-- **The condition number of an eigenvector bounds its first-order motion.** Let $A, B$ be bounded
operators on a finite-dimensional normed space $E$ over an algebraically closed $\mathbb{K}$,
and let $\mu$, $u$, $\mu'$, $u'$ satisfy the hypotheses of
`Module.End.deriv_eigenvector_perturbation`. Then
$$\|u'\| \le \operatorname{Cond}(u) \, \|B\| \, \|u(0)\|.$$
This follows [saad2011numerical], §3.3.2, and corrects Property 5.5 of
[quarteroni2000numerical].

With `Module.End.eigenvectorCondNumber_eq_inv_dist_of_isSymmetric`, this is the bound
$\|x_k(\varepsilon) - x_k\| \le \varepsilon \|E\| / \min_{j \neq k} |\lambda_k - \lambda_j| +
o(\varepsilon)$ of [quarteroni2000numerical] for a Hermitian $A$. For a non-normal $A$ the
constant is the condition number of the eigenvector, not the reciprocal gap. -/
theorem norm_deriv_eigenvector_perturbation_le {A B : E →L[𝕜] E} {u : 𝕜 → E} {mu : 𝕜 → 𝕜}
    {u' : E} {mu' l : 𝕜} (hu : HasDerivAt u u' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ t, A (u t) + t • B (u t) = mu t • u t) (hlam : mu 0 = l)
    (hnorm : ∀ t, Module.End.spectralProjector (A : E →ₗ[𝕜] E) (· = l) (u t) = u 0) :
    ‖u'‖ ≤ eigenvectorCondNumber (A : E →ₗ[𝕜] E) l * ‖B‖ * ‖u 0‖ := by
  rw [deriv_eigenvector_perturbation (A := (A : E →ₗ[𝕜] E)) (B := (B : E →ₗ[𝕜] E)) hu hmu heig
    hlam hnorm, norm_neg]
  calc ‖reducedResolvent (A : E →ₗ[𝕜] E) l ((B : E →ₗ[𝕜] E) (u 0))‖
      ≤ eigenvectorCondNumber (A : E →ₗ[𝕜] E) l * ‖(B : E →ₗ[𝕜] E) (u 0)‖ :=
        norm_reducedResolvent_apply_le _ _ _
    _ ≤ eigenvectorCondNumber (A : E →ₗ[𝕜] E) l * (‖B‖ * ‖u 0‖) :=
        mul_le_mul_of_nonneg_left (B.le_opNorm (u 0)) (eigenvectorCondNumber_nonneg _ _)
    _ = _ := by ring

end Deriv

section Simple

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] {A : Module.End 𝕜 E} {l : 𝕜}

omit [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] in
/-- Let $E$ be an inner product space and let $w$ be a left eigenvector of $A$ for $l$:
$\langle w, Ay \rangle = l \langle w, y \rangle$ for all $y$. Then $\langle w, z \rangle = 0$
for every $z$ in the sum of the generalized eigenspaces of the eigenvalues $\mu \neq l$.

For a generalized eigenvector $z$ with $(A - \mu)^k z = 0$, testing against $w$ multiplies
$\langle w, z \rangle$ by $(l - \mu)^k \neq 0$. No finite dimension and no algebraic closedness
are needed. -/
theorem inner_eq_zero_of_mem_iSup_maxGenEigenspace {w : E} (hw : IsLeftEigenvector A l w) {z : E}
    (hz : z ∈ A.spectralSubspace (· ≠ l)) : (inner 𝕜 w z : 𝕜) = 0 := by
  have hpow : ∀ (μ : 𝕜) (k : ℕ) (y : E),
      (inner 𝕜 w (((A - μ • (1 : Module.End 𝕜 E)) ^ k) y) : 𝕜) = (l - μ) ^ k * inner 𝕜 w y := by
    intro μ k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, ih, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, inner_sub_right, inner_smul_right, hw.inner_apply, pow_succ]
      ring
  have hle : A.spectralSubspace (· ≠ l) ≤ (𝕜 ∙ w)ᗮ := by
    refine iSup₂_le fun μ hμ z hz => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace A μ z).mp hz
    have h := hpow μ k z
    rw [hk, inner_zero_right] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hμ.symm))
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hz)

/-- **The spectral projector of a simple eigenvalue.** Let $E$ be a finite-dimensional inner product
space over an algebraically closed $\mathbb{K}$. Let $u \neq 0$ satisfy $Au = lu$, let
$w \neq 0$ be a left eigenvector of $A$ for $l$, and let the generalized eigenspace of $l$ have
dimension $1$. Then for every $x \in E$,
$$Px = \frac{\langle w, x \rangle}{\langle w, u \rangle} \, u.$$
This is (3.42) of [saad2011numerical].

Both sides are multiples of $u$ that agree at $u$ and vanish on the complementary invariant
subspace, on which $w$ vanishes. The denominator is nonzero by
`Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one`. This identifies the normalization
$\langle w, v(t) \rangle = \langle w, u \rangle$ of the branch of
`Module.End.hasDerivAt_eigenvalue_perturbation` with the normalization $P v(t) = u$ of
`Module.End.deriv_eigenvector_perturbation`. -/
theorem spectralProjector_apply_of_finrank_eq_one {u w : E} (hAu : A u = l • u) (hu : u ≠ 0)
    (hw : IsLeftEigenvector A l w) (hw0 : w ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.maxGenEigenspace A l) = 1) (x : E) :
    A.spectralProjector (· = l) x = ((inner 𝕜 w x : 𝕜) / inner 𝕜 w u) • u := by
  have hne := inner_ne_zero_of_finrank_maxGenEigenspace_eq_one hAu hu hw hw0 hsimple
  have hPx : A.spectralProjector (· = l) x ∈ 𝕜 ∙ u := by
    rw [← maxGenEigenspace_eq_span_singleton_of_finrank_eq_one hAu hu hsimple]
    exact spectralProjector_apply_mem_maxGenEigenspace A l x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hPx
  have hwx : (inner 𝕜 w x : 𝕜) = c * inner 𝕜 w u := by
    have h0 := inner_eq_zero_of_mem_iSup_maxGenEigenspace hw
      (sub_spectralProjector_mem (A := A) (p := (· = l)) x)
    rw [inner_sub_right, sub_eq_zero, ← hc, inner_smul_right] at h0
    exact h0
  rw [← hc, hwx, mul_div_assoc, div_self hne, mul_one]

end Simple

end Module.End
