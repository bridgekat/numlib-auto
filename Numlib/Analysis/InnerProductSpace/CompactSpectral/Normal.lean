/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Spectrum`, beside
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.LocallyConvex.Separation
import Numlib.Analysis.Convex.Caratheodory
import Numlib.Analysis.InnerProductSpace.CompactSpectral.Basis
import Numlib.Analysis.Normed.Algebra.Spectrum

/-!
# The spectral theorem for compact normal operators

A compact normal operator `T` on a complex Hilbert space has a Hilbert basis of eigenvectors —
[brezis2011functional] Proposition 11.36 — with the closure of its numerical range equal to the
closed convex hull of its spectrum (Remark 2 of §11.4). The proof is Mathlib's proof of the
compact *self-adjoint* case (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`
in `Mathlib.Analysis.InnerProductSpace.Spectrum`) with the normal analogues of its three
ingredients, all over `RCLike 𝕜`:

* the adjoint of a normal operator has the conjugate eigenvalues with the same eigenvectors
  (`ContinuousLinearMap.IsStarNormal.eigenspace_adjoint`, from Mathlib's
  `IsStarNormal.ker_adjoint_eq_ker` applied to `T - μ • 1`);
* the eigenspaces are pairwise orthogonal (`IsStarNormal.orthogonalFamily_eigenspaces`);
* the orthogonal complement of their span is invariant under `T` and `T†`
  (`IsStarNormal.orthogonalComplement_iSup_eigenspaces_invariant`, `…_invariant_adjoint`), and
  the restriction of `T` to it is normal (`IsStarNormal.restrict`, through
  `ContinuousLinearMap.adjoint_restrict`);

and, in place of the self-adjoint spectral radius formula, the C⋆-algebra identity
`IsStarNormal.spectralRadius_eq_nnnorm` on `H →L[ℂ] H` — the one step that needs `ℂ`: on a real
Hilbert space a rotation of the plane is a compact normal operator without eigenvectors, as the
book notes. `IsStarNormal.orthogonalComplement_iSup_eigenspaces_eq_bot` is the core, and the
Hilbert basis is assembled by
`ContinuousLinearMap.exists_hilbertBasis_eigenvectors_of_orthogonalFamily`
(`Numlib.Analysis.InnerProductSpace.CompactSpectral.Basis`), shared with the self-adjoint
Theorem 6.11; as there, no separability is assumed and the index set is a set of vectors.

Remark 2, `closure W(T) = conv σ(T)`, is
`IsStarNormal.closure_numericalRange_eq_convexHull_spectrum`: `σ(T) ⊆ closure W(T)`
holds for every operator (`ContinuousLinearMap.spectrum_subset_closure_numericalRange`) and the
closure of the numerical range is convex (`LinearMap.convex_numericalRange`); conversely
`⟪u, T u⟫ = ∑ λᵢ |⟪eᵢ, u⟫|²` in the eigenbasis is an infinite convex combination of eigenvalues,
and a point outside the closed convex hull is separated from it by a real functional
(`geometric_hahn_banach_closed_point`), which cannot exceed its bound on such a combination.
The closure on the right is dropped because the convex hull of a compact subset of a
finite-dimensional space is compact (`IsCompact.convexHull` of
`Numlib.Analysis.Convex.Caratheodory`; Mathlib has only the finite-set version).
-/

open Module.End Filter Topology RCLike
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ContinuousLinearMap

-- dot notation `hT.foo` on `hT : IsStarNormal T` resolves `IsStarNormal.foo` through the *open*
-- namespaces, not the current one
open ContinuousLinearMap

section RCLike

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {T : H →L[𝕜] H}

/-- A scalar shift of a normal operator is normal: `star (T - μ • 1) = T† - conj μ • 1`, and
scalar multiples of the identity commute with everything. -/
theorem IsStarNormal.sub_smul_one (hT : IsStarNormal T) (μ : 𝕜) :
    IsStarNormal (T - μ • (1 : H →L[𝕜] H)) := by
  have hc : ∀ (c : 𝕜) (X : H →L[𝕜] H), Commute (c • (1 : H →L[𝕜] H)) X := fun c X => by
    have h : Commute (algebraMap 𝕜 (H →L[𝕜] H) c) X := Algebra.commutes c X
    rwa [Algebra.algebraMap_eq_smul_one] at h
  refine ⟨?_⟩
  have hstar : star (T - μ • (1 : H →L[𝕜] H)) = star T - conj μ • (1 : H →L[𝕜] H) := by
    rw [star_sub, star_smul, star_one, starRingEnd_apply]
  rw [hstar]
  exact Commute.sub_left (hT.star_comm_self.sub_right (hc μ (star T)).symm) (hc _ _)

/-- **The adjoint of a normal operator has the conjugate eigenvalues with the same
eigenvectors**: `N(T† - μ̄) = N(T - μ)` ([brezis2011functional] Proposition 11.36, the first
step of the proof). Mathlib's `IsStarNormal.ker_adjoint_eq_ker` applied to the normal operator
`T - μ • 1`, whose adjoint is `T† - μ̄ • 1`. -/
theorem IsStarNormal.eigenspace_adjoint (hT : IsStarNormal T) (μ : 𝕜) :
    eigenspace (adjoint T : Module.End 𝕜 H) (conj μ) = eigenspace (T : Module.End 𝕜 H) μ := by
  ext x
  rw [mem_eigenspace_iff, mem_eigenspace_iff, coe_coe, coe_coe, ← sub_eq_zero,
    ← sub_eq_zero (a := T x)]
  have h := (hT.sub_smul_one μ).adjoint_apply_eq_zero_iff x
  rw [← star_eq_adjoint, star_sub, star_smul, star_one, star_eq_adjoint, ← starRingEnd_apply] at h
  simpa only [sub_apply, smul_apply, one_apply_eq_self] using h

/-- A vector in the `μ`-eigenspace of a normal operator is a `μ̄`-eigenvector of the adjoint. -/
theorem IsStarNormal.adjoint_apply_eq_of_mem_eigenspace (hT : IsStarNormal T) {μ : 𝕜} {x : H}
    (hx : x ∈ eigenspace (T : Module.End 𝕜 H) μ) : adjoint T x = conj μ • x := by
  rw [← hT.eigenspace_adjoint] at hx
  exact mem_eigenspace_iff.1 hx

/-- **The eigenspaces of a normal operator are pairwise orthogonal** ([brezis2011functional]
Proposition 11.36): for `T x = μ x` and `T y = ν y`,
`ν ⟪x, y⟫ = ⟪x, T y⟫ = ⟪T† x, y⟫ = μ ⟪x, y⟫`, so `⟪x, y⟫ = 0` when `μ ≠ ν`. The shape is that
of Mathlib's `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`. -/
theorem IsStarNormal.orthogonalFamily_eigenspaces (hT : IsStarNormal T) :
    OrthogonalFamily 𝕜 (fun μ => eigenspace (T : Module.End 𝕜 H) μ)
      fun μ => (eigenspace (T : Module.End 𝕜 H) μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  have hv' : adjoint T v = conj μ • v := hT.adjoint_apply_eq_of_mem_eigenspace hv
  have hw' : T w = ν • w := mem_eigenspace_iff.1 hw
  change ⟪v, w⟫_𝕜 = 0
  have h : ν * ⟪v, w⟫_𝕜 = μ * ⟪v, w⟫_𝕜 := by
    rw [← inner_smul_right, ← hw', ← adjoint_inner_left, hv', inner_smul_left,
      starRingEnd_self_apply]
  have h' : (ν - μ) * ⟪v, w⟫_𝕜 = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hμν.symm)

/-- If a closed subspace is invariant under the adjoint of `S`, its orthogonal complement is
invariant under `S`: `⟪u, S v⟫ = ⟪S† u, v⟫ = 0` for `u ∈ K`, `v ∈ Kᗮ`. -/
theorem orthogonal_invariant_of_adjoint (S : H →L[𝕜] H) {K : Submodule 𝕜 H}
    (hK : ∀ x ∈ K, adjoint S x ∈ K) : ∀ v ∈ Kᗮ, S v ∈ Kᗮ := fun v hv =>
  (Submodule.mem_orthogonal K _).2 fun u hu => by
    rw [← adjoint_inner_left]
    exact (Submodule.mem_orthogonal K v).1 hv _ (hK u hu)

/-- **The orthogonal complement of the span of the eigenspaces of a normal operator is invariant
under the operator** ([brezis2011functional] Proposition 11.36): each eigenspace is invariant
under `T†` (`IsStarNormal.eigenspace_adjoint`), so each `(N(T - μ))ᗮ` is invariant under `T`,
and their intersection is `(⨆ μ, N(T - μ))ᗮ`. Mathlib's
`LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_invariant` is the self-adjoint
case. -/
theorem IsStarNormal.orthogonalComplement_iSup_eigenspaces_invariant (hT : IsStarNormal T) :
    ∀ v ∈ (⨆ μ, eigenspace (T : Module.End 𝕜 H) μ)ᗮ,
      T v ∈ (⨆ μ, eigenspace (T : Module.End 𝕜 H) μ)ᗮ := by
  intro v hv
  rw [← Submodule.iInf_orthogonal] at hv ⊢
  refine (T : Module.End 𝕜 H).iInf_invariant (fun μ => ?_) v hv
  exact orthogonal_invariant_of_adjoint T fun x hx => by
    rw [hT.adjoint_apply_eq_of_mem_eigenspace hx]
    exact Submodule.smul_mem _ _ hx

/-- **The orthogonal complement of the span of the eigenspaces of any operator is invariant
under the adjoint** ([brezis2011functional] Proposition 11.36, for a normal `T`; normality is not
needed): each eigenspace is invariant under `T = T††`, so each `(N(T - μ))ᗮ` is invariant under
`T†`. -/
theorem orthogonalComplement_iSup_eigenspaces_invariant_adjoint (T : H →L[𝕜] H) :
    ∀ v ∈ (⨆ μ, eigenspace (T : Module.End 𝕜 H) μ)ᗮ,
      adjoint T v ∈ (⨆ μ, eigenspace (T : Module.End 𝕜 H) μ)ᗮ := by
  intro v hv
  rw [← Submodule.iInf_orthogonal] at hv ⊢
  refine (adjoint T : Module.End 𝕜 H).iInf_invariant (fun μ => ?_) v hv
  refine orthogonal_invariant_of_adjoint (adjoint T) fun x hx => ?_
  have hx' : T x = μ • x := mem_eigenspace_iff.1 hx
  rw [adjoint_adjoint, hx']
  exact Submodule.smul_mem _ _ hx

/-- **The adjoint of a restriction is the restriction of the adjoint**: for a complete subspace
`W` invariant under `S` and `S†`, `(S|_W)† = S†|_W`, since `⟪S† x, y⟫ = ⟪x, S y⟫` on `W`. -/
theorem adjoint_restrict (S : H →L[𝕜] H) {W : Submodule 𝕜 H} [CompleteSpace W]
    (hW : ∀ x ∈ W, S x ∈ W) (hW' : ∀ x ∈ W, adjoint S x ∈ W) :
    adjoint (S.restrict hW) = (adjoint S).restrict hW' := by
  symm
  rw [eq_adjoint_iff]
  intro x y
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_restrict_apply, coe_restrict_apply,
    adjoint_inner_left]

/-- **The restriction of a normal operator to a closed subspace invariant under `T` and `T†` is
normal** ([brezis2011functional] Proposition 11.36, "we obtain a compact normal operator `T₀`
on `Fᗮ`"): the adjoint of the restriction is the restriction of the adjoint
(`adjoint_restrict`), so `‖T₀ x‖ = ‖T x‖ = ‖T† x‖ = ‖T₀† x‖` and
`isStarNormal_iff_norm_eq_adjoint` applies. -/
theorem IsStarNormal.restrict (hT : IsStarNormal T) {W : Submodule 𝕜 H} [CompleteSpace W]
    (hW : ∀ x ∈ W, T x ∈ W) (hW' : ∀ x ∈ W, adjoint T x ∈ W) :
    IsStarNormal (T.restrict hW) := by
  rw [isStarNormal_iff_norm_eq_adjoint, adjoint_restrict T hW hW']
  intro v
  exact isStarNormal_iff_norm_eq_adjoint.1 hT v

omit [CompleteSpace H] in
/-- The restriction of `T` to the orthogonal complement of the span of its eigenspaces has no
eigenvalue: an eigenvector of the restriction is an eigenvector of `T`, hence lies in the span
and in its orthogonal complement. Holds for every operator, without normality. -/
theorem eigenspace_restrict_orthogonalComplement_iSup_eigenspaces_eq_bot (T : H →L[𝕜] H)
    (hW : ∀ v ∈ (⨆ μ, eigenspace (T : Module.End 𝕜 H) μ)ᗮ,
      T v ∈ (⨆ μ, eigenspace (T : Module.End 𝕜 H) μ)ᗮ) (μ : 𝕜) :
    eigenspace ((T : Module.End 𝕜 H).restrict hW) μ = ⊥ :=
  eigenspace_restrict_eq_bot (f := (T : Module.End 𝕜 H)) hW
    ((Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ _)).disjoint

end RCLike

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →L[ℂ] H}

/-- **A compact normal operator on a complex Hilbert space with no nonzero eigenvalue is zero**
([brezis2011functional] Proposition 11.35 in the form the proof of Proposition 11.36 uses): its
spectrum is `{0}` or empty (`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`), so its spectral
radius vanishes, and for a normal element of the C⋆-algebra `H →L[ℂ] H` the spectral radius is
the norm (`IsStarNormal.spectralRadius_eq_nnnorm`). This is the only step that needs `ℂ`. -/
theorem IsStarNormal.eq_zero_of_forall_hasEigenvalue_eq_zero (hT : IsStarNormal T)
    (hK : IsCompactOperator T) :
    (∀ μ, HasEigenvalue (T : Module.End ℂ H) μ → μ = 0) ↔ T = 0 := by
  have := hT
  rw [← nnnorm_eq_zero, ← ENNReal.coe_eq_zero, ← IsStarNormal.spectralRadius_eq_nnnorm T,
    spectralRadius_eq_of_unital, ← not_iff_not, ENNReal.iSup_eq_zero]
  push Not
  apply exists_congr
  simp +contextual [hK.hasEigenvalue_iff_mem_spectrum]

/-- **The core of [brezis2011functional] Proposition 11.36**: the eigenvectors of a compact
normal operator on a complex Hilbert space span a dense subspace,
`(⨆ μ, N(T - μ))ᗮ = ⊥`. The restriction `T₀` of `T` to `W = (⨆ μ, N(T - μ))ᗮ` is compact and
normal and has no eigenvalue, so it is zero (`IsStarNormal.eq_zero_of_forall_hasEigenvalue_eq_zero`,
the book's Proposition 11.35); thus `W ≤ N(T)`, which lies in the span, and `W = ⊥`. This is
Mathlib's proof of the self-adjoint case
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` with the normal ingredients. -/
theorem IsStarNormal.orthogonalComplement_iSup_eigenspaces_eq_bot (hT : IsStarNormal T)
    (hK : IsCompactOperator T) : (⨆ μ, eigenspace (T : Module.End ℂ H) μ)ᗮ = ⊥ := by
  set W : Submodule ℂ H := (⨆ μ, eigenspace (T : Module.End ℂ H) μ)ᗮ with hWdef
  have hW : ∀ v ∈ W, T v ∈ W := hT.orthogonalComplement_iSup_eigenspaces_invariant
  have hW' : ∀ v ∈ W, adjoint T v ∈ W := orthogonalComplement_iSup_eigenspaces_invariant_adjoint T
  set S : W →L[ℂ] W := T.restrict hW with hSdef
  have hS_compact : IsCompactOperator S := hK.restrict' hW
  have hS_normal : IsStarNormal S := hT.restrict hW hW'
  have hS : ∀ μ, eigenspace (S : Module.End ℂ W) μ = ⊥ :=
    eigenspace_restrict_orthogonalComplement_iSup_eigenspaces_eq_bot T hW
  have h : ∀ μ, HasEigenvalue (S : Module.End ℂ W) μ → μ = 0 := by
    simp_all [hasEigenvalue_iff]
  rw [hS_normal.eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact] at h
  rw [← Submodule.subsingleton_iff_eq_bot]
  by_contra! hV
  simpa [h] using hS 0

/-- **The spectral theorem for compact normal operators** ([brezis2011functional]
Proposition 11.36): a compact normal operator on a complex Hilbert space has a Hilbert basis of
eigenvectors, indexed by a set of vectors as in Mathlib's `exists_hilbertBasis`; the eigenvalues
need not be real. No separability is assumed. Assembled from the orthogonality of the
eigenspaces and the density of their span by
`ContinuousLinearMap.exists_hilbertBasis_eigenvectors_of_orthogonalFamily`. -/
theorem IsStarNormal.exists_hilbertBasis_eigenvector (hT : IsStarNormal T)
    (hK : IsCompactOperator T) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H),
      ⇑b = ((↑) : w → H) ∧ ∀ i : w, ∃ μ : ℂ, T i = μ • (i : H) :=
  exists_hilbertBasis_eigenvectors_of_orthogonalFamily hT.orthogonalFamily_eigenspaces
    (hT.orthogonalComplement_iSup_eigenspaces_eq_bot hK)

/-! ### Remark 2: the closure of the numerical range is the closed convex hull of the spectrum -/

/-- The closed convex hull of the spectrum lies in the closure of the numerical range, for
every bounded operator on a complex Hilbert space: `σ(T) ⊆ closure W(T)`
(`spectrum_subset_closure_numericalRange`) and the closure of the numerical range is convex
(`LinearMap.convex_numericalRange`, the Toeplitz–Hausdorff theorem). -/
theorem closure_convexHull_spectrum_subset_closure_numericalRange (T : H →L[ℂ] H) :
    closure (convexHull ℝ (spectrum ℂ T)) ⊆ closure (T : H →ₗ[ℂ] H).numericalRange :=
  closure_minimal (convexHull_min (spectrum_subset_closure_numericalRange T)
    (LinearMap.convex_numericalRange _).closure) isClosed_closure

/-- In an eigenbasis `b` of `T` with eigenvalues `λ`, `⟪u, T u⟫ = ∑ λᵢ ‖⟪bᵢ, u⟫‖²`
([brezis2011functional] §11.4, Remark 2, the computation `(T u, u) = ∑ λᵢ |uᵢ|²`). -/
theorem hasSum_eigenvalue_mul_norm_sq_inner {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℂ}
    (hb : ∀ i, T (b i) = lam i • b i) (hT : IsStarNormal T) (u : H) :
    HasSum (fun i => lam i * ((‖⟪b i, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) ⟪u, T u⟫_ℂ := by
  convert b.hasSum_inner_mul_inner u (T u) using 1
  ext i
  have hi : adjoint T (b i) = conj (lam i) • b i :=
    hT.adjoint_apply_eq_of_mem_eigenspace (mem_eigenspace_iff.2 (hb i))
  rw [← adjoint_inner_left, hi, inner_smul_left, starRingEnd_self_apply, ← inner_conj_symm u,
    Complex.ofReal_pow, ← Complex.conj_mul']
  ring

/-- **[brezis2011functional] §11.4, Remark 2**: for a compact normal operator on a complex
Hilbert space, the closure of the numerical range is the closed convex hull of the spectrum,
`closure W(T) = closure (conv σ(T))` (the book writes `conv` for the closed convex hull).

`⊇` is `closure_convexHull_spectrum_subset_closure_numericalRange`, valid for every operator.
For `⊆`, a point `z = ⟪u, T u⟫ / ⟪u, u⟫` of `W(T)` outside the closed convex hull `C` of the
spectrum would be separated from `C` by a real functional `φ` with `φ ≤ c` on `C` and
`c < φ z` (`geometric_hahn_banach_closed_point`); but in an eigenbasis `⟪u, T u⟫ = ∑ λᵢ |uᵢ|²`
with `∑ |uᵢ|² = ‖u‖²` and every eigenvalue `λᵢ` in `σ(T) ⊆ C`, so
`φ z = ‖u‖⁻² ∑ |uᵢ|² φ(λᵢ) ≤ c`. -/
theorem IsStarNormal.closure_numericalRange_eq_closure_convexHull_spectrum (hT : IsStarNormal T)
    (hK : IsCompactOperator T) :
    closure (T : H →ₗ[ℂ] H).numericalRange = closure (convexHull ℝ (spectrum ℂ T)) := by
  refine le_antisymm (closure_minimal ?_ isClosed_closure)
    (closure_convexHull_spectrum_subset_closure_numericalRange T)
  rintro z ⟨u, hu, rfl⟩
  by_contra hz
  obtain ⟨φ, c, hφc, hcz⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (spectrum ℂ T)).closure isClosed_closure hz
  obtain ⟨w, b, hb, hlam⟩ := hT.exists_hilbertBasis_eigenvector hK
  choose lam hlam using hlam
  have hbi : ∀ i, T (b i) = lam i • b i := fun i => by rw [hb]; exact hlam i
  -- the eigenvalues lie in the spectrum, hence in the closed convex hull
  have hlam_mem : ∀ i, φ (lam i) ≤ c := fun i => by
    refine (hφc _ (subset_closure (subset_convexHull ℝ _ ?_))).le
    rw [ContinuousLinearMap.spectrum_eq]
    refine HasEigenvalue.mem_spectrum
      (hasEigenvalue_of_hasEigenvector (f := (T : Module.End ℂ H)) (x := b i) ⟨?_, ?_⟩)
    · exact mem_eigenspace_iff.2 (hbi i)
    · exact b.orthonormal.ne_zero i
  -- the two expansions
  have h1 := hasSum_eigenvalue_mul_norm_sq_inner b hbi hT u
  have h2 : HasSum (fun i => ‖⟪b i, u⟫_ℂ‖ ^ 2) (‖u‖ ^ 2) := by
    have := b.hasSum_inner_mul_inner u u
    rw [inner_self_eq_norm_sq_to_K] at this
    refine Complex.hasSum_ofReal.1 ?_
    convert this using 1
    · ext i
      rw [← inner_conj_symm u, Complex.ofReal_pow, ← Complex.conj_mul']
    · exact Complex.ofReal_pow _ _
  have hu2 : 0 < ‖u‖ ^ 2 := by positivity
  -- `φ z = ‖u‖⁻² ∑ |uᵢ|² φ (λᵢ) ≤ c`
  have hz' : ⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ = ((‖u‖ ^ 2)⁻¹ : ℝ) • ⟪u, T u⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K, div_eq_inv_mul, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_pow]
    rfl
  have hφ : φ (⟪u, T u⟫_ℂ / ⟪u, u⟫_ℂ) ≤ c := by
    rw [hz', map_smul, smul_eq_mul, h1.tsum_eq.symm, φ.map_tsum h1.summable]
    have h3 : HasSum (fun i => ‖⟪b i, u⟫_ℂ‖ ^ 2 * φ (lam i))
        (φ (∑' i, lam i * ((‖⟪b i, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ))) := by
      rw [h1.tsum_eq]
      convert h1.mapL φ using 1
      ext i
      rw [mul_comm (lam i), ← Complex.real_smul, map_smul, smul_eq_mul]
    have h4 : HasSum (fun i => ‖⟪b i, u⟫_ℂ‖ ^ 2 * c) (‖u‖ ^ 2 * c) := h2.mul_right c
    have h5 : ∑' i, φ (lam i * ((‖⟪b i, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) ≤ ‖u‖ ^ 2 * c := by
      rw [show (fun i => φ (lam i * ((‖⟪b i, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ))) =
          fun i => ‖⟪b i, u⟫_ℂ‖ ^ 2 * φ (lam i) from funext fun i => by
            rw [mul_comm, ← Complex.real_smul, map_smul, smul_eq_mul]]
      rw [← h4.tsum_eq]
      refine h3.summable.tsum_le_tsum (fun i => ?_) h4.summable
      exact mul_le_mul_of_nonneg_left (hlam_mem i) (by positivity)
    calc (‖u‖ ^ 2)⁻¹ * ∑' i, φ (lam i * ((‖⟪b i, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ))
        ≤ (‖u‖ ^ 2)⁻¹ * (‖u‖ ^ 2 * c) := by gcongr
      _ = c := by field_simp
  exact absurd hφ (not_le.2 hcz)

/-- **[brezis2011functional] §11.4, Remark 2**, with the closure on the right dropped: for a
compact normal operator on a complex Hilbert space, `closure W(T) = conv σ(T)`, the plain convex
hull — the spectrum is compact and the convex hull of a compact subset of `ℂ` is compact
(`IsCompact.convexHull`, `Numlib.Analysis.Convex.Caratheodory`), hence closed. -/
theorem IsStarNormal.closure_numericalRange_eq_convexHull_spectrum (hT : IsStarNormal T)
    (hK : IsCompactOperator T) :
    closure (T : H →ₗ[ℂ] H).numericalRange = convexHull ℝ (spectrum ℂ T) := by
  rw [hT.closure_numericalRange_eq_closure_convexHull_spectrum hK]
  exact (spectrum.isCompact T).convexHull.isClosed.closure_eq

end Complex

end ContinuousLinearMap

end
