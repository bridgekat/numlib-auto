import Numlib.Eigen.PowerMethod

/-!
# The reduced resolvent and the condition number of an eigenvector

The resolvent `(A - z)⁻¹` blows up at an eigenvalue `l`, but only in the direction of the
generalized eigenspace of `l`: on the complementary invariant subspace `ker P` — `P` the spectral
projector of `l` — the operator `A - l` is still invertible, and its inverse there is the **reduced
resolvent** `S(l)` of [saad2011numerical], §3.3.2.

The object this file defines is `S(l) (1 - P)`, the reduced resolvent extended by zero across the
generalized eigenspace, because that is the operator every statement about it mentions: `S(l)`
alone is a map `ker P → ker P` and cannot be composed with anything in sight. Its defining property
is [saad2011numerical]'s (3.40),

`Module.End.reducedResolvent_apply_sub_smul : S(l) (1 - P) (A - l) x = x - P x`,

which determines it, and its norm is the condition number of the eigenvector,
`Module.End.eigenvectorCondNumber` ([saad2011numerical], Def 3.2). The name is earned by
[saad2011numerical]'s (3.43): along a differentiable branch of eigenpairs of `A + t B` normalized by
`P u(t) = u`, the eigenvector moves at the rate `u'(0) = -S(l)(1 - P) B u`, so
`‖u'(0)‖ ≤ Cond(u) ‖B‖ ‖u‖`.

## Implementation notes

Everything here rests on the splitting `Krylov.isCompl_maxGenEigenspace` of
`Numlib/Eigen/PowerMethod`, which is why this module sits above that one rather than beside
`Numlib/Eigen/Perturbation`: the projector is the *oblique* `Krylov.spectralProjector`, not an
orthogonal one, so no inner product is used and the ambient space is only a normed space.
`IsAlgClosed 𝕜` and `FiniteDimensional 𝕜 E` are what make the generalized eigenspaces span and the
restricted `A - l` surjective from injective; both are the hypotheses of the splitting.

The Hermitian value `Cond(u) = 1 / dist (l, σ(A) \ {l})` ([saad2011numerical]'s (3.45)) is not
proved here; the plan records it.

## References

[saad2011numerical], §3.3.2 and Definition 3.2.
-/

open Krylov

namespace Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] (A : Module.End 𝕜 E) (l : 𝕜)

omit [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] in
/-- The invariant subspace complementary to the generalized eigenspace of `l` is invariant under
`A - l`, since it is invariant under `A`. -/
theorem mapsTo_sub_smul_one : ∀ w ∈ (⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ),
    (A - l • (1 : Module.End 𝕜 E)) w ∈ ⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ := by
  have key : (⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ) ≤
      Submodule.comap (A - l • (1 : Module.End 𝕜 E))
        (⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ) := by
    refine iSup₂_le fun μ hμ v hv => ?_
    have hmem : ∀ y ∈ A.maxGenEigenspace μ, y ∈ (⨆ ν, ⨆ _ : ¬ ν = l, A.maxGenEigenspace ν) :=
      fun y hy => Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ hy)
    simp only [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact Submodule.sub_mem _
      (hmem _ (A.mapsTo_maxGenEigenspace_of_comm (Commute.refl A) μ hv))
      (Submodule.smul_mem _ _ (hmem _ hv))
  exact fun w hw => key hw

/-- **`A - l` is injective on the complementary invariant subspace.** A vector killed by `A - l` is
an eigenvector for `l`, hence lies in the generalized eigenspace of `l`, which meets the complement
only in `0`. -/
theorem injective_restrict_sub_smul_one :
    Function.Injective ((A - l • (1 : Module.End 𝕜 E)).restrict (mapsTo_sub_smul_one A l)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨w, hw⟩ h0
  have h1 : (A - l • (1 : Module.End 𝕜 E)) w = 0 := congrArg Subtype.val h0
  have heig : w ∈ A.eigenspace l := by
    rw [Module.End.mem_eigenspace_iff]
    simpa using sub_eq_zero.1 h1
  have hmem : w ∈ (A.maxGenEigenspace l) ⊓ (⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ) :=
    ⟨Module.End.eigenspace_le_maxGenEigenspace heig, hw⟩
  simpa using (disjoint_iff_inf_le.1 (Krylov.isCompl_maxGenEigenspace A l).disjoint) hmem

/-- `A - l` as an automorphism of the invariant subspace complementary to the generalized
eigenspace of `l`: injective by `Module.End.injective_restrict_sub_smul_one`, hence bijective in
finite dimension. Its inverse is [saad2011numerical]'s reduced resolvent `S(l)`. -/
noncomputable def reducedResolventEquiv :
    ↥(⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ) ≃ₗ[𝕜]
      ↥(⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ) :=
  LinearEquiv.ofBijective ((A - l • (1 : Module.End 𝕜 E)).restrict (mapsTo_sub_smul_one A l))
    ⟨injective_restrict_sub_smul_one A l,
      LinearMap.injective_iff_surjective.1 (injective_restrict_sub_smul_one A l)⟩

/-- The complementary part of any vector lies in the invariant subspace the reduced resolvent acts
on. -/
theorem sub_spectralProjector_mem_iSup (x : E) :
    (1 - Krylov.spectralProjector A (· = l)) x ∈
      ⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ := by
  simpa using Krylov.sub_spectralProjector_mem (B := A) (p := (· = l)) x

/-- **The reduced resolvent of `A` at `l`, extended by zero** ([saad2011numerical], §3.3.2): the
operator `S(l) (1 - P)` sending `x` to the unique `y` of the invariant subspace complementary to
the generalized eigenspace of `l` with `(A - l) y = x - P x`.

`S(l)` alone is defined only on that complement; the composite with `1 - P` is total, and it is
what [saad2011numerical]'s Definition 3.2 and his first-order eigenvector expansion (3.43)
use. `Module.End.reducedResolvent_apply_sub_smul` is his (3.40), the identity that characterizes
it. -/
noncomputable def reducedResolvent : E →ₗ[𝕜] E :=
  (⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ).subtype ∘ₗ
    ((reducedResolventEquiv A l).symm.toLinearMap ∘ₗ
      LinearMap.codRestrict _ (1 - Krylov.spectralProjector A (· = l))
        (sub_spectralProjector_mem_iSup A l))

theorem reducedResolvent_apply (x : E) :
    reducedResolvent A l x =
      ((reducedResolventEquiv A l).symm
        ⟨(1 - Krylov.spectralProjector A (· = l)) x, sub_spectralProjector_mem_iSup A l x⟩ : E) :=
  rfl

/-- The reduced resolvent lands in the invariant subspace it inverts `A - l` on. -/
theorem reducedResolvent_apply_mem (x : E) :
    reducedResolvent A l x ∈ ⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ :=
  ((reducedResolventEquiv A l).symm
    ⟨_, sub_spectralProjector_mem_iSup A l x⟩ :
      ↥(⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ)).2

/-- The spectral projector of a single eigenvalue lands in its generalized eigenspace. -/
theorem spectralProjector_apply_mem_maxGenEigenspace (x : E) :
    Krylov.spectralProjector A (· = l) x ∈ A.maxGenEigenspace l := by
  have h := Krylov.spectralProjector_apply_mem (B := A) (p := (· = l)) x
  rwa [iSup_iSup_eq_left] at h

omit [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] in
/-- The generalized eigenspace of `l` is invariant under `A - l`. -/
theorem sub_smul_one_apply_mem_maxGenEigenspace {y : E} (hy : y ∈ A.maxGenEigenspace l) :
    (A - l • (1 : Module.End 𝕜 E)) y ∈ A.maxGenEigenspace l := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  exact Submodule.sub_mem _ (A.mapsTo_maxGenEigenspace_of_comm (Commute.refl A) l hy)
    (Submodule.smul_mem _ _ hy)

/-- The spectral projector of `l` fixes the generalized eigenspace of `l`. -/
theorem spectralProjector_apply_of_mem_maxGenEigenspace {y : E} (hy : y ∈ A.maxGenEigenspace l) :
    Krylov.spectralProjector A (· = l) y = y := by
  refine Krylov.spectralProjector_apply_of_mem ?_
  rw [iSup_iSup_eq_left]
  exact hy

/-- **The defining identity of the reduced resolvent** ([saad2011numerical], (3.40)): `S(l) (1 - P)
(A - l) x = (1 - P) x` for every `x`.

Split `x = P x + (x - P x)`. Both summands are `(A - l)`-invariant subspaces, so `1 - P` kills the
image of the first and fixes the image of the second, leaving `(A - l) (x - P x)`; applying the
inverse of `A - l` on the complement returns `x - P x`. -/
theorem reducedResolvent_apply_sub_smul (x : E) :
    reducedResolvent A l ((A - l • (1 : Module.End 𝕜 E)) x)
      = x - Krylov.spectralProjector A (· = l) x := by
  set P := Krylov.spectralProjector A (· = l) with hP
  set T := A - l • (1 : Module.End 𝕜 E) with hT
  have hw : x - P x ∈ ⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ :=
    Krylov.sub_spectralProjector_mem (B := A) (p := (· = l)) x
  have hTPx : T (P x) ∈ A.maxGenEigenspace l :=
    sub_smul_one_apply_mem_maxGenEigenspace A l (spectralProjector_apply_mem_maxGenEigenspace A l x)
  have hkey : (1 - P) (T x) = T (x - P x) := by
    have h1 : P (T (P x)) = T (P x) := spectralProjector_apply_of_mem_maxGenEigenspace A l hTPx
    have h2 : P (T (x - P x)) = 0 :=
      Krylov.spectralProjector_apply_eq_zero_iff.2 (mapsTo_sub_smul_one A l _ hw)
    have h3 : T x = T (P x) + T (x - P x) := by rw [← map_add]; congr 1; abel
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [h3, map_add, h1, h2]
    abel
  have hval : ((reducedResolventEquiv A l) ⟨x - P x, hw⟩ : E) = T (x - P x) := rfl
  rw [reducedResolvent_apply]
  have hmk : (⟨(1 - P) (T x), sub_spectralProjector_mem_iSup A l (T x)⟩ :
      ↥(⨆ μ, ⨆ _ : ¬ μ = l, A.maxGenEigenspace μ)) =
        (reducedResolventEquiv A l) ⟨x - P x, hw⟩ :=
    Subtype.ext (hkey.trans hval.symm)
  rw [hmk, LinearEquiv.symm_apply_apply]

/-- The reduced resolvent kills the generalized eigenspace of `l`, which is where the resolvent
itself is singular. -/
@[simp]
theorem reducedResolvent_apply_of_mem_maxGenEigenspace {y : E} (hy : y ∈ A.maxGenEigenspace l) :
    reducedResolvent A l y = 0 := by
  have h : (1 - Krylov.spectralProjector A (· = l)) y = 0 := by
    simp [spectralProjector_apply_of_mem_maxGenEigenspace A l hy]
  rw [reducedResolvent_apply]
  simp only [h]
  simp [← Submodule.coe_zero]

/-- **The condition number of an eigenvector** ([saad2011numerical], Def 3.2): the operator norm of
the reduced resolvent `S(l) (1 - P)`.

It measures how far the eigenvector of a simple eigenvalue `l` moves under a perturbation of `A`:
[saad2011numerical]'s (3.43) gives `u'(0) = -S(l)(1 - P) B u` for the branch normalized by
`P u(t) = u`, so the first-order displacement is at most `Cond(u) ‖B‖ ‖u‖`. For a Hermitian `A` it
is `1 / dist (l, σ(A) \ {l})`, the `1/δ` of
`LinearMap.IsSymmetric.sin_angle_le_norm_residual_div`; in general it is not controlled by the
spectrum alone. -/
noncomputable def eigenvectorCondNumber : ℝ :=
  ‖LinearMap.toContinuousLinearMap (reducedResolvent A l)‖

/-- The condition number of an eigenvector is a norm, hence nonnegative. -/
theorem eigenvectorCondNumber_nonneg : 0 ≤ eigenvectorCondNumber A l := norm_nonneg _

/-- The bound the condition number is for: the reduced resolvent moves no vector by more than
`Cond(u)` times its length. -/
theorem norm_reducedResolvent_apply_le (x : E) :
    ‖reducedResolvent A l x‖ ≤ eigenvectorCondNumber A l * ‖x‖ :=
  (LinearMap.toContinuousLinearMap (reducedResolvent A l)).le_opNorm x

end Module.End
