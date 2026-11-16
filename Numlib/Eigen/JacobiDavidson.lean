/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The eigenvalue problem as a nonlinear system: Newton corrections and Jacobi–Davidson

The eigenpairs $(x, \mu)$ of an operator $A$ are the zeros of a residual map
$F(x, \mu) = (A x - \mu x, N(x))$, where $N(x) = 0$ fixes the normalization of $x$. The Jacobi
orthogonal component correction, the Davidson method and the Jacobi–Davidson method are exact or
approximate Newton steps for $F$. The presentation follows [golub2013matrix] §10.6, which builds on
work of Sorensen (2002) and of Stewart; [saad2011numerical], Chapter 8, treats the same methods.
This module proves the statements of that theory that have a precise form: the residual maps and
their derivatives, the closed form of the bordered Newton correction, and the equivalence of the
bordered system with the projected correction equation of Jacobi–Davidson.

Two normalizations are treated: the linear one $\ell(x) = 1$, for a continuous linear functional
$\ell$ on a normed space over any nontrivially normed field, and the spherical one
$(\|x\|^2 - 1)/2 = 0$ on a real inner product space. In both cases the derivative of $F$ at
$(x, \mu)$ is the bordered operator $(\delta x, \delta\mu) \mapsto ((A - \mu) \delta x - \delta\mu
\, x, \ell(\delta x))$ (for the sphere, $\ell(\delta x) = \langle x, \delta x \rangle$). So the
system (10.6.5) of [golub2013matrix] is the Jacobian system of Newton's method.

## Main definitions

* `ContinuousLinearMap.eigenpairResidual`: the residual $F(x, \mu) = (A x - \mu x, \ell(x) - 1)$.
* `ContinuousLinearMap.eigenpairResidualSphere`: the residual
  $F(x, \mu) = (A x - \mu x, (\|x\|^2 - 1)/2)$.

## Main results

* `ContinuousLinearMap.hasFDerivAt_eigenpairResidual`: the Fréchet derivative of the linear residual
  is the bordered operator (10.6.5).
* `ContinuousLinearMap.hasFDerivAt_eigenpairResidualSphere`: the Fréchet derivative of the spherical
  residual.
* `JacobiDavidson.newtonCorrection_eq`: the bordered system
  $(A - \mu) \delta x - \delta\mu \, x = -r$, $\ell(\delta x) = 0$ has the unique solution
  $\delta\mu = \ell(R r) / \ell(R x)$, $\delta x = -R (r - \delta\mu \, x)$ with
  $R = (A - \mu)^{-1}$, as in (10.6.6)–(10.6.7).
* `JacobiDavidson.newtonStep_iff_projected`: for $\|x\| = 1$ and the Rayleigh quotient $\mu$, a
  correction $\delta x \perp x$ solves the bordered Newton system if and only if it solves the
  projected equation $P (A - \mu) P \delta x = -r$, which is (10.6.17) $\Leftrightarrow$ (10.6.18).

## Implementation notes

* The closed form of the Newton correction is stated for an arbitrary endomorphism of a vector space
  over a field. So the same lemma also covers the approximate operator $M$ of (10.6.8)–(10.6.10) of
  [golub2013matrix].
* [golub2013matrix] derives only the implication (10.6.17) $\Rightarrow$ (10.6.18). The statement
  that the correction can be obtained by solving the projected system needs the converse, which
  `JacobiDavidson.newtonStep_iff_projected` also proves.
* The methods themselves are algorithms whose specification is a Ritz–Galerkin condition. No
  convergence theorem is proved here.
* The residual maps are Newton maps for the eigenpairs of any bounded operator, so they are in the
  namespace `ContinuousLinearMap`.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

section Linear

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] (A : E →L[𝕜] E) (ℓ : E →L[𝕜] 𝕜)

/-- The **eigenpair residual with a linear normalization**. Let $A$ be a continuous linear operator
on a normed space $E$ over a nontrivially normed field $\mathbb{K}$, and let $\ell$ be a
continuous linear functional on $E$. The residual is the map
$E \times \mathbb{K} \to E \times \mathbb{K}$,
$$F(x, \mu) = (A x - \mu x, \ \ell(x) - 1).$$

This is the map $F([x; \lambda]) = [A x - \lambda x; w^T x - 1]$ of [golub2013matrix] §10.6.1,
with the functional $\ell$ in place of $x \mapsto w^T x$. Its zeros are the eigenpairs
$(x, \mu)$ with $\ell(x) = 1$ (`ContinuousLinearMap.eigenpairResidual_eq_zero_iff`). -/
def eigenpairResidual (p : E × 𝕜) : E × 𝕜 :=
  (A p.1 - p.2 • p.1, ℓ p.1 - 1)

/-- The eigenpair residual vanishes exactly at the normalized eigenpairs: $F(x, \mu) = 0$ if and
only if $A x = \mu x$ and $\ell(x) = 1$. -/
theorem eigenpairResidual_eq_zero_iff (x : E) (μ : 𝕜) :
    A.eigenpairResidual ℓ (x, μ) = 0 ↔ A x = μ • x ∧ ℓ x = 1 := by
  simp [eigenpairResidual, Prod.ext_iff, sub_eq_zero]

/-- The map $(x, \mu) \mapsto A x - \mu x$, the first component of both eigenpair residuals, has at
$(x, \mu)$ the Fréchet derivative
$$(\delta x, \delta\mu) \mapsto A \delta x - \mu \, \delta x - \delta\mu \, x.$$
-/
theorem hasFDerivAt_apply_sub_smul (x : E) (μ : 𝕜) :
    HasFDerivAt (fun p : E × 𝕜 => A p.1 - p.2 • p.1)
      ((A - μ • ContinuousLinearMap.id 𝕜 E).comp (ContinuousLinearMap.fst 𝕜 E 𝕜) -
        (ContinuousLinearMap.snd 𝕜 E 𝕜).smulRight x) (x, μ) := by
  have hA := (A.comp (ContinuousLinearMap.fst 𝕜 E 𝕜)).hasFDerivAt (x := (x, μ))
  have hs := (hasFDerivAt_snd (𝕜 := 𝕜) (p := (x, μ))).smul
    (hasFDerivAt_fst (𝕜 := 𝕜) (p := (x, μ)))
  refine (hA.sub hs).congr_fderiv ?_
  ext p <;> simp

/-- **The Jacobian of the eigenpair residual.** For the residual
$F(x, \mu) = (A x - \mu x, \ell(x) - 1)$ of `ContinuousLinearMap.eigenpairResidual`, the Fréchet
derivative at $(x, \mu)$ is the bordered operator
$$(\delta x, \delta\mu) \mapsto \bigl( A \delta x - \mu \, \delta x - \delta\mu \, x, \
  \ell(\delta x) \bigr).$$

This is the statement of [golub2013matrix] about (10.6.5): it is "precisely the Jacobian system
that arises if Newton's method is used". -/
theorem hasFDerivAt_eigenpairResidual (x : E) (μ : 𝕜) :
    HasFDerivAt (A.eigenpairResidual ℓ)
      (((A - μ • ContinuousLinearMap.id 𝕜 E).comp (ContinuousLinearMap.fst 𝕜 E 𝕜) -
          (ContinuousLinearMap.snd 𝕜 E 𝕜).smulRight x).prod
        (ℓ.comp (ContinuousLinearMap.fst 𝕜 E 𝕜))) (x, μ) := by
  have h2 : HasFDerivAt (fun p : E × 𝕜 => ℓ p.1 - 1) (ℓ.comp (ContinuousLinearMap.fst 𝕜 E 𝕜))
      (x, μ) :=
    (ℓ.comp (ContinuousLinearMap.fst 𝕜 E 𝕜)).hasFDerivAt.sub_const 1
  exact (A.hasFDerivAt_apply_sub_smul x μ).prodMk h2

end Linear

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →L[ℝ] E)

/-- The **eigenpair residual with the spherical normalization**. Let $A$ be a continuous linear
operator on a real inner product space $E$. The residual is the map
$E \times \mathbb{R} \to E \times \mathbb{R}$,
$$F(x, \mu) = \bigl( A x - \mu x, \ (\|x\|^2 - 1)/2 \bigr).$$

This is the function of (10.6.17) of [golub2013matrix]. Its zeros are the eigenpairs with
$\|x\| = 1$ (`ContinuousLinearMap.eigenpairResidualSphere_eq_zero_iff`). -/
noncomputable def eigenpairResidualSphere (p : E × ℝ) : E × ℝ :=
  (A p.1 - p.2 • p.1, (‖p.1‖ ^ 2 - 1) / 2)

/-- The spherical eigenpair residual vanishes exactly at the unit eigenpairs: $F(x, \mu) = 0$ if and
only if $A x = \mu x$ and $\|x\| = 1$. -/
theorem eigenpairResidualSphere_eq_zero_iff (x : E) (μ : ℝ) :
    A.eigenpairResidualSphere (x, μ) = 0 ↔ A x = μ • x ∧ ‖x‖ = 1 := by
  simp only [eigenpairResidualSphere, Prod.mk_eq_zero, sub_eq_zero, div_eq_zero_iff,
    two_ne_zero, or_false]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith

/-- **The Jacobian of the spherical residual.** For the residual
$F(x, \mu) = (A x - \mu x, (\|x\|^2 - 1)/2)$ of `ContinuousLinearMap.eigenpairResidualSphere`,
the Fréchet derivative at $(x, \mu)$ is
$$(\delta x, \delta\mu) \mapsto \bigl( A \delta x - \mu \, \delta x - \delta\mu \, x, \ \langle
  x, \delta x \rangle \bigr).$$

This is the Jacobian of the system (10.6.17) of [golub2013matrix]. -/
theorem hasFDerivAt_eigenpairResidualSphere (x : E) (μ : ℝ) :
    HasFDerivAt A.eigenpairResidualSphere
      (((A - μ • ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.fst ℝ E ℝ) -
          (ContinuousLinearMap.snd ℝ E ℝ).smulRight x).prod
        ((innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E ℝ))) (x, μ) := by
  have h2 : HasFDerivAt (fun p : E × ℝ => (‖p.1‖ ^ 2 - 1) / 2)
      ((innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, μ) := by
    have hn := (((hasFDerivAt_fst (𝕜 := ℝ) (p := (x, μ))).norm_sq).sub_const 1).const_smul
      (1 / 2 : ℝ)
    have hf : (fun p : E × ℝ => (‖p.1‖ ^ 2 - 1) / 2) =
        fun p => (1 / 2 : ℝ) • (‖p.1‖ ^ 2 - 1) := by
      funext p
      rw [smul_eq_mul]
      ring
    rw [hf]
    refine hn.congr_fderiv ?_
    ext p <;> simp
  exact (A.hasFDerivAt_apply_sub_smul x μ).prodMk h2

end Sphere

end ContinuousLinearMap

namespace JacobiDavidson

section Field

variable {𝕜 : Type*} [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- **The bordered Newton correction in closed form.** Let $A$ be an endomorphism of a vector space
$E$ over a field, let $\mu$ be a scalar such that $A - \mu$ is invertible, and write
$R = (A - \mu)^{-1}$. Let $\ell$ be a linear functional on $E$ and let $x \in E$ satisfy
$\ell(R x) \neq 0$. Then for every right-hand side $r \in E$, a pair $(\delta x, \delta\mu)$
solves the bordered system
$$(A - \mu) \delta x - \delta\mu \, x = -r, \qquad \ell(\delta x) = 0$$
if and only if
$$\delta\mu = \frac{\ell(R r)}{\ell(R x)}, \qquad \delta x = -R (r - \delta\mu \, x).$$

This is (10.6.6)–(10.6.7) of [golub2013matrix]. With $r = A x - \mu x$ and $\ell(x) = 1$, the
solution is the Newton step (10.6.4) for `ContinuousLinearMap.eigenpairResidual`. With an
approximate operator $M$ in place of $A$, it is (10.6.9)–(10.6.10). The inverse $R$ is
`Ring.inverse (A - μ • 1)`. The proof is linear algebra only. -/
theorem newtonCorrection_eq {A : Module.End 𝕜 E} {μ : 𝕜} (hA : IsUnit (A - μ • 1))
    (ℓ : E →ₗ[𝕜] 𝕜) {x : E} (hx : ℓ (Ring.inverse (A - μ • 1) x) ≠ 0) (r δx : E) (δμ : 𝕜) :
    ((A - μ • 1) δx - δμ • x = -r ∧ ℓ δx = 0) ↔
      (δμ = ℓ (Ring.inverse (A - μ • 1) r) / ℓ (Ring.inverse (A - μ • 1) x) ∧
        δx = -Ring.inverse (A - μ • 1) (r - δμ • x)) := by
  set T := A - μ • 1
  set R := Ring.inverse T
  have hTR : ∀ y, T (R y) = y := fun y => by
    rw [← Module.End.mul_apply, Ring.mul_inverse_cancel T hA, Module.End.one_apply]
  have hRT : ∀ y, R (T y) = y := fun y => by
    rw [← Module.End.mul_apply, Ring.inverse_mul_cancel T hA, Module.End.one_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have hT : T δx = δμ • x - r := by
      rw [sub_eq_add_neg, ← h1]
      abel
    have hδx : δx = -R (r - δμ • x) := by
      rw [← hRT δx, hT, ← neg_sub, map_neg]
    refine ⟨?_, hδx⟩
    rw [hδx, map_neg, map_sub, map_smul, map_sub, map_smul, smul_eq_mul, neg_eq_zero,
      sub_eq_zero] at h2
    rw [h2, mul_div_assoc, div_self hx, mul_one]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h2, map_neg, hTR]
      abel
    · rw [h2, map_neg, map_sub, map_smul, map_sub, map_smul, smul_eq_mul, h1, div_mul_cancel₀ _ hx,
        sub_self, neg_zero]

end Field

section InnerProduct

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The Jacobi–Davidson correction equation.** Let $E$ be an inner product space over $\mathbb{R}$
or $\mathbb{C}$, let $A$ be a linear operator on $E$, and let $x \in E$ with $\|x\| = 1$. Let
$\mu = \langle x, A x \rangle$ be the Rayleigh quotient, $r = A x - \mu x$ the residual, and $P$
the orthogonal projection onto the orthogonal complement of $x$. Then for every
$\delta x \in E$, the following are equivalent:
* there is a scalar $\delta\mu$ with $(A - \mu) \delta x - \delta\mu \, x = -r$ and
  $\langle x, \delta x \rangle = 0$;
* $\langle x, \delta x \rangle = 0$ and $P (A - \mu) P \, \delta x = -r$.

The first condition is the bordered Newton system (10.6.17) of [golub2013matrix] and the second
is the projected correction equation (10.6.18). The source derives only the implication from the
first to the second. In the proof, the multiplier is $\delta\mu = \langle x, (A - \mu) \delta x
\rangle$. The projection $P$ is the `Submodule.starProjection` of the orthogonal complement of
the line through $x$. -/
theorem newtonStep_iff_projected (A : E →ₗ[𝕜] E) {x : E} (hx : ‖x‖ = 1) (δx : E) :
    (∃ δμ : 𝕜, (A - ⟪x, A x⟫_𝕜 • 1) δx - δμ • x = -(A x - ⟪x, A x⟫_𝕜 • x) ∧ ⟪x, δx⟫_𝕜 = 0) ↔
      (⟪x, δx⟫_𝕜 = 0 ∧
        (𝕜 ∙ x)ᗮ.starProjection ((A - ⟪x, A x⟫_𝕜 • 1) ((𝕜 ∙ x)ᗮ.starProjection δx)) =
          -(A x - ⟪x, A x⟫_𝕜 • x)) := by
  have hxx : ⟪x, x⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]
    simp
  have hmem : ∀ y, y ∈ (𝕜 ∙ x)ᗮ ↔ ⟪x, y⟫_𝕜 = 0 := fun y =>
    Submodule.mem_orthogonal_singleton_iff_inner_right
  have hr : ⟪x, A x - ⟪x, A x⟫_𝕜 • x⟫_𝕜 = 0 := by
    rw [inner_sub_right, inner_smul_right, hxx, mul_one, sub_self]
  have hPr : (𝕜 ∙ x)ᗮ.starProjection (A x - ⟪x, A x⟫_𝕜 • x) = A x - ⟪x, A x⟫_𝕜 • x :=
    Submodule.starProjection_eq_self_iff.2 ((hmem _).2 hr)
  have hPx : (𝕜 ∙ x)ᗮ.starProjection x = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := (𝕜 ∙ x)ᗮ)).2
      (Submodule.le_orthogonal_orthogonal _ (Submodule.mem_span_singleton_self x))
  constructor
  · rintro ⟨δμ, h1, h2⟩
    refine ⟨h2, ?_⟩
    have hT : (A - ⟪x, A x⟫_𝕜 • 1) δx = -(A x - ⟪x, A x⟫_𝕜 • x) + δμ • x := by
      rw [← h1]
      abel
    rw [Submodule.starProjection_eq_self_iff.2 ((hmem δx).2 h2), hT, map_add, map_neg, map_smul,
      hPr, hPx, smul_zero, add_zero]
  · rintro ⟨h2, h1⟩
    rw [Submodule.starProjection_eq_self_iff.2 ((hmem δx).2 h2)] at h1
    refine ⟨⟪x, (A - ⟪x, A x⟫_𝕜 • 1) δx⟫_𝕜, ?_, h2⟩
    have hz : ⟪x, (A - ⟪x, A x⟫_𝕜 • 1) δx - ⟪x, (A - ⟪x, A x⟫_𝕜 • 1) δx⟫_𝕜 • x +
        (A x - ⟪x, A x⟫_𝕜 • x)⟫_𝕜 = 0 := by
      rw [inner_add_right, inner_sub_right, inner_smul_right, hxx, mul_one, sub_self, zero_add, hr]
    have hz0 := Submodule.starProjection_eq_self_iff.2 ((hmem _).2 hz)
    rw [map_add, map_sub, map_smul, h1, hPx, smul_zero, sub_zero, hPr, neg_add_cancel] at hz0
    rw [← sub_eq_zero, sub_neg_eq_add]
    exact hz0.symm

end InnerProduct

end JacobiDavidson
