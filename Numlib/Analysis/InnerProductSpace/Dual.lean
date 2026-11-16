/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Dual`, beside `InnerProductSpace.toDual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Functionals dominated through an injective map into a Hilbert space

Let $V$ be a real normed space, let $H$ be a real Hilbert space, and let $\iota : V \to H$ be an
injective bounded linear map. A continuous linear functional $T$ on $V$ with
$|Tv| \le C \|\iota v\|$ for all $v$ factors through $\iota$ as an inner product:
$Tv = \langle h, \iota v \rangle$ for some $h \in H$ with $\|h\| \le C$. This is how a functional on
a Sobolev space $H^1_0(\Omega)$ that is bounded by the $L^2$ norm is recognized as
$\Phi \mapsto \int_\Omega h \Phi$ with $h \in L^2(\Omega)$, as in the regularity of the obstacle
problem in `Numlib.Analysis.PDE.Elliptic.Obstacle`. The module also gives the Riesz map of a real
Hilbert space as a real-linear isometry.

## Main definitions

* `InnerProductSpace.toDualReal`: the Riesz map $E \to E^*$ of a real Hilbert space, as a linear
  isometry equivalence.

## Main results

* `exists_inner_of_forall_abs_le`: a functional dominated through an injective map into a Hilbert
  space is an inner product.

## Proof outline

The functional $T \circ \iota^{-1}$ on the range of $\iota$ is bounded by $C$. The Hahn–Banach
theorem extends it to $H$ with the same norm, and the Riesz representation theorem gives $h$.
-/

open scoped InnerProductSpace

/-- **A dominated functional is an inner product.** Let $V$ be a real normed space, let $H$ be a
real Hilbert space, let $\iota : V \to H$ be an injective bounded linear map, and let $T$ be a
continuous linear functional on $V$. Let $C \ge 0$ satisfy $|Tv| \le C \|\iota v\|$ for all
$v \in V$. Then there is $h \in H$ with $\|h\| \le C$ and
$$Tv = \langle h, \iota v \rangle \quad \text{for all } v \in V.$$

The proof extends $T \circ \iota^{-1}$ from the range of $\iota$ by the Hahn–Banach theorem and
applies the Riesz representation theorem. -/
theorem exists_inner_of_forall_abs_le {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (ι : V →L[ℝ] H)
    (hι : Function.Injective ι) (T : V →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ v, |T v| ≤ C * ‖ι v‖) :
    ∃ h : H, ‖h‖ ≤ C ∧ ∀ v, T v = ⟪h, ι v⟫_ℝ := by
  obtain ⟨S, hS⟩ : ∃ S : Submodule ℝ H, S = LinearMap.range (ι : V →ₗ[ℝ] H) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : V ≃ₗ[ℝ] LinearMap.range (ι : V →ₗ[ℝ] H),
      e = LinearEquiv.ofInjective (ι : V →ₗ[ℝ] H) hι := ⟨_, rfl⟩
  have hev : ∀ v, ((e v : LinearMap.range (ι : V →ₗ[ℝ] H)) : H) = ι v := fun v ↦ by
    rw [he]
    exact LinearEquiv.ofInjective_apply _ _
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : LinearMap.range (ι : V →ₗ[ℝ] H) →ₗ[ℝ] ℝ,
      ℓ₀ = (T : V →ₗ[ℝ] ℝ).comp e.symm.toLinearMap := ⟨_, rfl⟩
  have hℓ₀apply : ∀ y, ℓ₀ y = T (e.symm y) := fun y ↦ by rw [hℓ₀]; rfl
  have hbound : ∀ y : LinearMap.range (ι : V →ₗ[ℝ] H), ‖ℓ₀ y‖ ≤ C * ‖y‖ := fun y ↦ by
    have hy : ι (e.symm y) = (y : H) := by
      rw [← hev (e.symm y), e.apply_symm_apply]
    rw [hℓ₀apply, Real.norm_eq_abs, ← Submodule.norm_coe, ← hy]
    exact hT _
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : StrongDual ℝ (LinearMap.range (ι : V →ₗ[ℝ] H)),
      ℓ = LinearMap.mkContinuous ℓ₀ C hbound := ⟨_, rfl⟩
  have hℓapply : ∀ y, ℓ y = ℓ₀ y := fun y ↦ by rw [hℓ]; rfl
  have hℓnorm : ‖ℓ‖ ≤ C := by rw [hℓ]; exact LinearMap.mkContinuous_norm_le _ hC _
  obtain ⟨g, hg, hnorm⟩ := exists_extension_norm_eq (LinearMap.range (ι : V →ₗ[ℝ] H)) ℓ
  refine ⟨(InnerProductSpace.toDual ℝ H).symm g, ?_, fun v ↦ ?_⟩
  · rw [LinearIsometryEquiv.norm_map, hnorm]
    exact hℓnorm
  · rw [InnerProductSpace.toDual_symm_apply, ← hev v, hg (e v), hℓapply, hℓ₀apply,
      e.symm_apply_apply]

/-! ### The Riesz map of a real Hilbert space, real-linearly -/

section ToDualReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The **Riesz isometry** $E \to E^*$ of a real Hilbert space $E$,
$x \mapsto \langle x, \cdot \rangle$, as a real-linear isometry equivalence.

Mathlib's `InnerProductSpace.toDual ℝ E` has the conjugate-linear type `≃ₗᵢ⋆[ℝ]`, which over
$\mathbb{R}$ is the same map. This definition gives that map the linear type, so that the
calculus lemmas stated for `≃ₗᵢ[𝕜]`, such as `LinearIsometryEquiv.comp_fderiv` and the lemmas on
smoothness and differentiability, apply. Its inverse is `(InnerProductSpace.toDual ℝ E).symm`,
so `gradient f x = (InnerProductSpace.toDualReal E).symm (fderiv ℝ f x)` holds by definition
(`gradient_eq_toDualReal_symm` of `Numlib.Analysis.Calculus.Gradient`). -/
noncomputable def InnerProductSpace.toDualReal : E ≃ₗᵢ[ℝ] StrongDual ℝ E where
  toFun := InnerProductSpace.toDual ℝ E
  invFun := (InnerProductSpace.toDual ℝ E).symm
  map_add' := map_add _
  map_smul' c x := by
    rw [LinearIsometryEquiv.map_smulₛₗ]
    rfl
  left_inv := (InnerProductSpace.toDual ℝ E).symm_apply_apply
  right_inv := (InnerProductSpace.toDual ℝ E).apply_symm_apply
  norm_map' := (InnerProductSpace.toDual ℝ E).norm_map

variable {E}

/-- The map `InnerProductSpace.toDualReal E` sends $x$ to the functional
`InnerProductSpace.toDual ℝ E x`, that is, $y \mapsto \langle x, y \rangle$. -/
@[simp]
theorem InnerProductSpace.toDualReal_apply (x : E) :
    InnerProductSpace.toDualReal E x = InnerProductSpace.toDual ℝ E x := rfl

/-- The inverse of `InnerProductSpace.toDualReal E` is the inverse of
`InnerProductSpace.toDual ℝ E`: it sends a functional $\varphi$ to the vector $x$ with
$\varphi = \langle x, \cdot \rangle$. -/
@[simp]
theorem InnerProductSpace.toDualReal_symm_apply (φ : StrongDual ℝ E) :
    (InnerProductSpace.toDualReal E).symm φ = (InnerProductSpace.toDual ℝ E).symm φ := rfl

end ToDualReal
