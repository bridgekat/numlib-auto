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

A continuous linear functional `T` on a normed space `V` that is dominated by the norm of an
injective bounded linear map `ι : V → H` into a real Hilbert space, `|T v| ≤ C ‖ι v‖`, factors
through `ι` as an inner product: `T v = ⟪h, ι v⟫` for some `h ∈ H` with `‖h‖ ≤ C`
(`exists_inner_of_forall_abs_le`). The functional `T ∘ ι⁻¹` on the range of `ι` is bounded by
`C`, the Hahn–Banach theorem extends it to `H` with the same norm, and the Riesz representation
theorem produces `h`.

This is how a functional on a Sobolev space `H¹₀(Ω)` bounded by the `L²` norm is recognized as
`Φ ↦ ∫_Ω h Φ` with `h ∈ L²(Ω)` (the regularity of the obstacle problem,
`Numlib/Analysis/PDE/Elliptic/Obstacle.lean`).
-/

open scoped InnerProductSpace

/-- **A functional dominated by an `L²`-type seminorm through an injective map into a Hilbert
space is an inner product**: if `T : V → ℝ` is continuous linear with `|T v| ≤ C ‖ι v‖` for an
injective `ι : V → H`, `H` a real Hilbert space, then `T v = ⟪h, ι v⟫` for some `h ∈ H` with
`‖h‖ ≤ C` — the Hahn–Banach theorem on the range of `ι` and the Riesz representation. -/
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

/-- **The Riesz isometry of a real Hilbert space as a real-linear isometry equivalence**:
`InnerProductSpace.toDual ℝ E` is typed as conjugate-linear (`≃ₗᵢ⋆[ℝ]`), which over `ℝ` is the
same map; this is that map with the linear type, so that the calculus lemmas stated for
`≃ₗᵢ[𝕜]` (`LinearIsometryEquiv.comp_fderiv`, `contDiff`, `differentiableAt`) apply. Its inverse
is `(toDual ℝ E).symm`, so `gradient f x = (toDualReal E).symm (fderiv ℝ f x)` definitionally
(`gradient_eq_toDualReal_symm` of `Numlib/Analysis/Calculus/Gradient.lean`). -/
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

/-- `toDualReal` is `toDual`. -/
@[simp]
theorem InnerProductSpace.toDualReal_apply (x : E) :
    InnerProductSpace.toDualReal E x = InnerProductSpace.toDual ℝ E x := rfl

/-- The inverse of `toDualReal` is the inverse of `toDual`. -/
@[simp]
theorem InnerProductSpace.toDualReal_symm_apply (φ : StrongDual ℝ E) :
    (InnerProductSpace.toDualReal E).symm φ = (InnerProductSpace.toDual ℝ E).symm φ := rfl

end ToDualReal
