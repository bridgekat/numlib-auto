import Numlib.Eigen.Normal
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

For a **normal** operator the condition number is computed:
`Module.End.eigenvectorCondNumber_eq_inv_infDist_of_isStarNormal` is
`Cond(u) = 1 / dist (l, σ(A) \ {l})`, with
`Module.End.eigenvectorCondNumber_eq_inv_dist_of_isSymmetric` the Hermitian case
[saad2011numerical] states as (3.45).  On the eigenspace of `μ` the reduced resolvent is
multiplication by `(μ - l)⁻¹` (`Module.End.reducedResolvent_apply_of_mem_eigenspace`, which needs no
normality), and for a normal operator those eigenspaces are orthogonal and span, so the operator
norm is the largest `|μ - l|⁻¹`; the spectrum is finite, so the largest is attained.  Both sides are
`0` when `l` is the only eigenvalue.

## Implementation notes

Everything here rests on the splitting `Krylov.isCompl_maxGenEigenspace` of
`Numlib/Eigen/PowerMethod`, which is why this module sits above that one rather than beside
`Numlib/Eigen/Perturbation`: the projector is the *oblique* `Krylov.spectralProjector`, not an
orthogonal one, so no inner product is used and the ambient space is only a normed space.
`IsAlgClosed 𝕜` and `FiniteDimensional 𝕜 E` are what make the generalized eigenspaces span and the
restricted `A - l` surjective from injective; both are the hypotheses of the splitting.

The condition number of a normal operator is evaluated in a section of its own, which reintroduces
`E` with an inner product; no identification of `Krylov.spectralProjector` with
`Submodule.starProjection` is needed for it, only that the projector kills the complementary
invariant subspace.

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

/-! ### The condition number of an eigenvector of a normal operator -/

section Normal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] {A : Module.End 𝕜 E} {l : 𝕜}

/-- **On the eigenspace of `μ ≠ l` the reduced resolvent is multiplication by `(μ - l)⁻¹`**: there
`A - l` is multiplication by `μ - l`, and the spectral projector of `l` vanishes.  No normality is
needed for this. -/
theorem reducedResolvent_apply_of_mem_eigenspace {μ : 𝕜} (hμ : μ ≠ l) {x : E}
    (hx : x ∈ A.eigenspace μ) : reducedResolvent A l x = (μ - l)⁻¹ • x := by
  have hμl : μ - l ≠ 0 := sub_ne_zero.2 hμ
  have hAx : A x = μ • x := Module.End.mem_eigenspace_iff.1 hx
  have hmem : (μ - l)⁻¹ • x ∈ ⨆ ν, ⨆ _ : ¬ ν = l, A.maxGenEigenspace ν :=
    Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
      (Submodule.smul_mem _ _ (Module.End.eigenspace_le_maxGenEigenspace hx)))
  have hAy : (A - l • (1 : Module.End 𝕜 E)) ((μ - l)⁻¹ • x) = x := by
    have hstep : (A - l • (1 : Module.End 𝕜 E)) x = (μ - l) • x := by
      simp [hAx, sub_smul]
    rw [map_smul, hstep, smul_smul, inv_mul_cancel₀ hμl, one_smul]
  have hP : Krylov.spectralProjector A (· = l) ((μ - l)⁻¹ • x) = 0 :=
    Krylov.spectralProjector_apply_eq_zero_iff.2 hmem
  have h := reducedResolvent_apply_sub_smul A l ((μ - l)⁻¹ • x)
  rwa [hAy, hP, sub_zero] at h

/-- The reduced resolvent on the eigenvector basis of a normal operator: it scales the `j`-th basis
vector by `(λ_j - l)⁻¹`, or kills it when `λ_j = l`. -/
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

/-- Every eigenvalue of the eigenvector basis lies in the spectrum. -/
private theorem eigenvalues_mem_spectrum (hA : IsStarNormal A) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (j : Fin n) :
    LinearMap.IsStarNormal.eigenvalues hA hn j ∈ spectrum 𝕜 A := by
  refine Module.End.hasEigenvalue_iff_mem_spectrum.1 (Module.End.hasEigenvalue_of_hasEigenvector
    (x := LinearMap.IsStarNormal.eigenvectorBasis hA hn j) ⟨?_, ?_⟩)
  · exact Module.End.mem_eigenspace_iff.2 (LinearMap.IsStarNormal.apply_eigenvectorBasis hA hn j)
  · exact (LinearMap.IsStarNormal.eigenvectorBasis hA hn).toBasis.ne_zero j

/-- The reduced resolvent of a normal operator moves no vector by more than
`1 / dist (l, σ(A) \ {l})` times its length: in the orthonormal eigenvector basis it is a diagonal
operator whose entries are the `(μ - l)⁻¹`. -/
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

/-- **The condition number of an eigenvector of a normal operator** ([saad2011numerical], (3.45)):
`Cond(u) = 1 / dist (l, σ(A) \ {l})`.

On the eigenspace of `μ` the reduced resolvent is multiplication by `(μ - l)⁻¹`, and the eigenspaces
of a normal operator are orthogonal and span, so the operator norm is the largest of the `|μ - l|⁻¹`
over the other eigenvalues; the largest is attained because the spectrum is finite.  Both sides are
`0` when `l` is the only eigenvalue, `Metric.infDist` to the empty set being `0`. -/
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

/-- **The condition number of an eigenvector of a Hermitian operator** ([saad2011numerical],
(3.45)), the case of `Module.End.eigenvectorCondNumber_eq_inv_infDist_of_isStarNormal` the source
states: for a symmetric `A` the condition number of the eigenvector of `l` is
`1 / dist (l, σ(A) \ {l})`, the `1 / δ` of
`LinearMap.IsSymmetric.sin_angle_le_norm_residual_div`. -/
theorem eigenvectorCondNumber_eq_inv_dist_of_isSymmetric (hA : A.IsSymmetric) (l : 𝕜) :
    eigenvectorCondNumber A l = (Metric.infDist l (spectrum 𝕜 A \ {l}))⁻¹ :=
  eigenvectorCondNumber_eq_inv_infDist_of_isStarNormal
    ((LinearMap.isSymmetric_iff_isSelfAdjoint A).1 hA).isStarNormal l

end Normal

end Module.End
