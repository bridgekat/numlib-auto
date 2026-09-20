/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Extension.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Affine
import Numlib.Analysis.Sobolev.EmbeddingDomain

/-!
# The reference triangle is a Sobolev extension domain

The reference triangle `T̂ = {(x, y) : x > 0, y > 0, x + y < 1}` of the finite element method is a
Lipschitz domain and not of class `C¹`, so the extension theorem of
`Numlib/Analysis/Sobolev/Extension.lean` (Brezis's Theorem 9.7) does not apply to it, and its
hypotenuse is not a coordinate line, so the four reflections of the unit square (Brezis's Remark 9,
`SobolevEuclidean.exists_extensionL_unitSquare`) do not apply either. This file proves that it is
nevertheless a `W^{1,p}`-extension domain for every `1 ≤ p ≤ ∞`, and with it every nondegenerate
triangle of the plane.

## The proof

Two reflections and one affine change of variables:

* the reflection across the side `y = 0` (`SobolevEuclidean.exists_reflectionStep`) extends
  `W^{1,p}(T̂)` to the half diamond `{x > 0, x + |y| < 1}`, and the reflection across `x = 0`
  extends that to the diamond `{|x| + |y| < 1}`;
* the diamond is the affine preimage of the unit square under
  `(x, y) ↦ ((x + y + 1)/2, (x − y + 1)/2)` (`EuclideanSpace.diamondEquiv`), and **being an
  extension domain is affine-invariant** (`IsSobolevExtensionDomain.of_preimage_affine`,
  `SobolevEuclidean.exists_extensionL_of_preimage_affine`): the transport `u ↦ u ∘ F⁻¹` to the
  square, the square's extension operator, and the transport `w ↦ w ∘ F` back are bounded linear
  maps (`SobolevEuclidean.compDiffeoL` for the affine diffeomorphisms of
  `isDiffeoOnWithBoundedJacobian_affine_top` and `isDiffeoOnWithBoundedJacobian_affine_symm`, in
  `Calculus.lean`), and their composite is the identity on the preimage.

The composites are assembled with the operators as variables
(`SobolevEuclidean.fn_comp_affine_of_ops`, `SobolevEuclidean.exists_extensionL_of_step`), as in
`Extension.lean`, and instantiated once each.

## Main definitions

* `EuclideanSpace.referenceTriangle`, the open reference triangle of `ℝ²`, with its vertices
  `EuclideanSpace.referenceTriangleVertex` and barycentric coordinates `EuclideanSpace.baryCoord`;
  `EuclideanSpace.halfDiamond`, `EuclideanSpace.diamond` and `EuclideanSpace.diamondEquiv`, the
  intermediate domains and the affine map of the proof.
* `EuclideanSpace.openTriangle A B C`, the open triangle with vertices `A, B, C`, the image of
  the reference triangle under `x ↦ A + x₀ (B − A) + x₁ (C − A)` (`EuclideanSpace.triangleEquiv`
  is the linear part, for non-collinear vertices).

## Main results

* `IsSobolevExtensionDomain.of_preimage_affine`, `IsSobolevExtensionDomain.of_image_affine`,
  `IsSobolevExtensionDomainAll.of_preimage_affine`, `IsSobolevExtensionDomainAll.of_image_affine`:
  extension domains are affine-invariant; `SobolevEuclidean.exists_extensionL_of_preimage_affine`
  is the same for the shape of Theorem 9.7 (with the `L^p` bound).
* `SobolevEuclidean.exists_extensionL_of_step` (with `IsSobolevExtensionDomain.of_extension_step`
  of `Extension.lean`): an extension operator into a larger extension domain makes the smaller
  one an extension domain.
* `SobolevEuclidean.exists_extensionL_referenceTriangle`: the reference triangle has an extension
  operator in the shape of Theorem 9.7; `isSobolevExtensionDomainAll_referenceTriangle`,
  `isSobolevExtensionDomainAll_of_image_referenceTriangle` (every affine image) and
  `isSobolevExtensionDomainAll_of_eq_openTriangle` (every triangle with non-collinear vertices)
  are the predicate forms; `isSobolevExtensionDomainAll_unitSquare` is the square's.

## References

[brezis2011functional] Theorem 9.7, Remark 9 of Chapter 9; [han2009theoretical] §10.3, where the
reference triangle is the reference element of the linear finite element (Example 10.3.8).
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

/-! ### Extension domains are affine-invariant -/

section AffineInvariance

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **The composite of the transport to `Ω`, an extension operator on `Ω` and the transport back
is the identity on the preimage `Ω' = F⁻¹(Ω)`**, `F x = T x + c`, with the operators as
variables: `A : W^{1,p}(Ω') → W^{1,p}(Ω)` with `A u = u ∘ F⁻¹`, `P : W^{1,p}(Ω) → W^{1,p}(ℝ^N)`
with `P w = w` on `Ω`, `B : W^{1,p}(ℝ^N) → W^{1,p}(ℝ^N)` with `B w = w ∘ F`, and
`Q u = B (P (A u))`; then `Q u = u` almost everywhere on `Ω'`. The almost-everywhere identities
on `Ω` pull back along `F` by `IsDiffeoOnWithBoundedJacobian.ae_comp_restrict`. -/
theorem SobolevEuclidean.fn_comp_affine_of_ops {Ω Ω' : Opens 𝔼} (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼)
    (hΩ' : (Ω' : Set 𝔼) = (fun x ↦ T x + c) ⁻¹' Ω)
    (A : SobolevEuclidean N 1 p Ω' →L[ℝ] SobolevEuclidean N 1 p Ω)
    (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤)
    (B : SobolevEuclidean N 1 p ⊤ →L[ℝ] SobolevEuclidean N 1 p ⊤)
    (Q : SobolevEuclidean N 1 p Ω' →L[ℝ] SobolevEuclidean N 1 p ⊤) (hQ : ∀ u, Q u = B (P (A u)))
    (hA : ∀ u, SobolevMultiIndex.fn (A u) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun y ↦ SobolevMultiIndex.fn u (T.symm y + -T.symm c))
    (hP : ∀ w, SobolevMultiIndex.fn (P w) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn w)
    (hB : ∀ w, SobolevMultiIndex.fn (B w) =ᵐ[volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)]
      fun x ↦ SobolevMultiIndex.fn w (T x + c))
    (u : SobolevEuclidean N 1 p Ω') :
    SobolevMultiIndex.fn (Q u) =ᵐ[volume.restrict (Ω' : Set 𝔼)] SobolevMultiIndex.fn u := by
  have hd := isDiffeoOnWithBoundedJacobian_affine T c Ω
  rw [← hΩ'] at hd
  have h1 : ∀ᵐ x ∂volume.restrict (Ω' : Set 𝔼),
      SobolevMultiIndex.fn (P (A u)) (T x + c) = SobolevMultiIndex.fn (A u) (T x + c) :=
    hd.ae_comp_restrict (P := fun y ↦
      SobolevMultiIndex.fn (P (A u)) y = SobolevMultiIndex.fn (A u) y) (hP (A u))
  have h2 : ∀ᵐ x ∂volume.restrict (Ω' : Set 𝔼),
      SobolevMultiIndex.fn (A u) (T x + c)
        = SobolevMultiIndex.fn u (T.symm (T x + c) + -T.symm c) :=
    hd.ae_comp_restrict (P := fun y ↦
      SobolevMultiIndex.fn (A u) y = SobolevMultiIndex.fn u (T.symm y + -T.symm c)) (hA u)
  have h3 : ∀ᵐ x ∂volume.restrict (Ω' : Set 𝔼),
      SobolevMultiIndex.fn (B (P (A u))) x = SobolevMultiIndex.fn (P (A u)) (T x + c) :=
    (hB (P (A u))).filter_mono
      (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 le_top) le_rfl))
  rw [hQ u]
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx3, hx1, hx2]
  simp

/-- **The `L^p` bound of the composite** of `SobolevEuclidean.fn_comp_affine_of_ops`: the
constants multiply. -/
theorem SobolevEuclidean.eLpNorm_comp_affine_of_ops {Ω Ω' : Opens 𝔼}
    (A : SobolevEuclidean N 1 p Ω' →L[ℝ] SobolevEuclidean N 1 p Ω)
    (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤)
    (B : SobolevEuclidean N 1 p ⊤ →L[ℝ] SobolevEuclidean N 1 p ⊤)
    (Q : SobolevEuclidean N 1 p Ω' →L[ℝ] SobolevEuclidean N 1 p ⊤) (hQ : ∀ u, Q u = B (P (A u)))
    {C₁ C₂ C₃ : ℝ≥0∞}
    (hA : ∀ u, eLpNorm (SobolevMultiIndex.fn (A u)) p (volume.restrict (Ω : Set 𝔼))
      ≤ C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω' : Set 𝔼)))
    (hP : ∀ w, eLpNorm (SobolevMultiIndex.fn (P w)) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))
      ≤ C₂ * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Ω : Set 𝔼)))
    (hB : ∀ w, eLpNorm (SobolevMultiIndex.fn (B w)) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))
      ≤ C₃ * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)))
    (u : SobolevEuclidean N 1 p Ω') :
    eLpNorm (SobolevMultiIndex.fn (Q u)) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))
      ≤ C₃ * C₂ * C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω' : Set 𝔼)) := by
  rw [hQ u]
  calc eLpNorm (SobolevMultiIndex.fn (B (P (A u)))) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))
      ≤ C₃ * eLpNorm (SobolevMultiIndex.fn (P (A u))) p
          (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)) := hB _
    _ ≤ C₃ * (C₂ * eLpNorm (SobolevMultiIndex.fn (A u)) p (volume.restrict (Ω : Set 𝔼))) := by
        gcongr; exact hP _
    _ ≤ C₃ * (C₂ * (C₁ * eLpNorm (SobolevMultiIndex.fn u) p
          (volume.restrict (Ω' : Set 𝔼)))) := by
        gcongr; exact hA _
    _ = C₃ * C₂ * C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω' : Set 𝔼)) := by
        ring

/-- **An extension operator in the shape of Theorem 9.7 transports along an affine bijection**:
if `Ω` has one, so does its preimage `Ω' = F⁻¹(Ω)` under `F x = T x + c`, namely
`u ↦ (P (u ∘ F⁻¹)) ∘ F` (`SobolevEuclidean.compDiffeoL` twice around `P`), with the constants
of the two transports (`SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le`) multiplied in. -/
theorem SobolevEuclidean.exists_extensionL_of_preimage_affine {Ω Ω' : Opens 𝔼}
    (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼) (hΩ' : (Ω' : Set 𝔼) = (fun x ↦ T x + c) ⁻¹' Ω)
    (hΩ : ∃ (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼)) ∧
        ‖P u‖ ≤ C * ‖u‖) :
    ∃ (P : SobolevEuclidean N 1 p Ω' →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω' : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω' : Set 𝔼)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨P, C, hP⟩ := hΩ
  have hd₁ := isDiffeoOnWithBoundedJacobian_affine_symm T c hΩ'
  have hd₂ := isDiffeoOnWithBoundedJacobian_affine_top T c
  obtain ⟨C₁, hC₁, hA⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le
    (F := ℝ) (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p) (μ := volume) hd₁
  obtain ⟨C₃, hC₃, hB⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le
    (F := ℝ) (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p) (μ := volume) hd₂
  obtain ⟨A, hAfn, hAL⟩ : ∃ A : SobolevEuclidean N 1 p Ω' →L[ℝ] SobolevEuclidean N 1 p Ω,
      (∀ u, SobolevMultiIndex.fn (A u) =ᵐ[volume.restrict (Ω : Set 𝔼)]
        fun y ↦ SobolevMultiIndex.fn u (T.symm y + -T.symm c)) ∧
      ∀ u, eLpNorm (SobolevMultiIndex.fn (A u)) p (volume.restrict (Ω : Set 𝔼))
        ≤ C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω' : Set 𝔼)) :=
    ⟨SobolevEuclidean.compDiffeoL hd₁, fun u ↦ SobolevMultiIndex.fn_compDiffeoL hd₁ u, hA⟩
  obtain ⟨B, hBfn, hBL⟩ : ∃ B : SobolevEuclidean N 1 p ⊤ →L[ℝ] SobolevEuclidean N 1 p ⊤,
      (∀ w, SobolevMultiIndex.fn (B w) =ᵐ[volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)]
        fun x ↦ SobolevMultiIndex.fn w (T x + c)) ∧
      ∀ w, eLpNorm (SobolevMultiIndex.fn (B w)) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))
        ≤ C₃ * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)) :=
    ⟨SobolevEuclidean.compDiffeoL hd₂, fun w ↦ SobolevMultiIndex.fn_compDiffeoL hd₂ w, hB⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : SobolevEuclidean N 1 p Ω' →L[ℝ] SobolevEuclidean N 1 p ⊤,
      ∀ u, Q u = B (P (A u)) := ⟨B ∘L P ∘L A, fun u ↦ rfl⟩
  refine SobolevEuclidean.exists_extensionL_of_ops' Q (C := C₃ * ENNReal.ofReal C * C₁)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC₃ ENNReal.ofReal_ne_top) hC₁) fun u ↦ ⟨?_, ?_⟩
  · exact SobolevEuclidean.fn_comp_affine_of_ops T c hΩ' A P B Q hQ hAfn (fun w ↦ (hP w).1) hBfn u
  · refine SobolevEuclidean.eLpNorm_comp_affine_of_ops A P B Q hQ hAL (fun w ↦ ?_) hBL u
    rw [eLpNorm_restrict_coe_top]
    exact (hP w).2.1

/-- **Being a `W^{1,p}`-extension domain is affine-invariant** (preimage form): if `Ω` is one, so
is `Ω' = F⁻¹(Ω)` for every affine bijection `F x = T x + c`. The operator is
`u ↦ (P (u ∘ F⁻¹)) ∘ F`. -/
theorem IsSobolevExtensionDomain.of_preimage_affine {Ω Ω' : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomain N p Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼)
    (hΩ' : (Ω' : Set 𝔼) = (fun x ↦ T x + c) ⁻¹' Ω) : IsSobolevExtensionDomain N p Ω' := by
  obtain ⟨P, hP⟩ := hΩ
  obtain ⟨P', hP'⟩ : ∃ P' : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤,
      ∀ w, SobolevMultiIndex.fn (P' w) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn w :=
    ⟨P ∘L (ContinuousLinearMap.id ℝ _).codRestrict ⊤ (fun _ ↦ Submodule.mem_top),
      fun w ↦ hP ⟨w, Submodule.mem_top⟩⟩
  have hd₁ := isDiffeoOnWithBoundedJacobian_affine_symm T c hΩ'
  have hd₂ := isDiffeoOnWithBoundedJacobian_affine_top T c
  obtain ⟨A, hA⟩ : ∃ A : SobolevEuclidean N 1 p Ω' →L[ℝ] SobolevEuclidean N 1 p Ω,
      ∀ u, SobolevMultiIndex.fn (A u) =ᵐ[volume.restrict (Ω : Set 𝔼)]
        fun y ↦ SobolevMultiIndex.fn u (T.symm y + -T.symm c) :=
    ⟨SobolevEuclidean.compDiffeoL hd₁, fun u ↦ SobolevMultiIndex.fn_compDiffeoL hd₁ u⟩
  obtain ⟨B, hB⟩ : ∃ B : SobolevEuclidean N 1 p ⊤ →L[ℝ] SobolevEuclidean N 1 p ⊤,
      ∀ w, SobolevMultiIndex.fn (B w) =ᵐ[volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)]
        fun x ↦ SobolevMultiIndex.fn w (T x + c) :=
    ⟨SobolevEuclidean.compDiffeoL hd₂, fun w ↦ SobolevMultiIndex.fn_compDiffeoL hd₂ w⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : SobolevEuclidean N 1 p Ω' →L[ℝ] SobolevEuclidean N 1 p ⊤,
      ∀ u, Q u = B (P' (A u)) := ⟨B ∘L P' ∘L A, fun u ↦ rfl⟩
  exact ⟨Q ∘L Submodule.subtypeL ⊤,
    fun u ↦ SobolevEuclidean.fn_comp_affine_of_ops T c hΩ' A P' B Q hQ hA hP' hB u.1⟩

/-- **Being a `W^{1,p}`-extension domain is affine-invariant** (image form): if `Ω` is one, so is
`F(Ω)` for every affine bijection `F x = T x + c`. -/
theorem IsSobolevExtensionDomain.of_image_affine {Ω Ω' : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomain N p Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼)
    (hΩ' : (fun x ↦ T x + c) '' (Ω : Set 𝔼) = Ω') : IsSobolevExtensionDomain N p Ω' :=
  hΩ.of_preimage_affine T.symm (-T.symm c)
    (by rw [← hΩ', affine_image_eq_affine_symm_preimage])

/-- The affine preimage `affinePreimage T c Ω` of a `W^{1,p}`-extension domain is one. -/
theorem IsSobolevExtensionDomain.affinePreimage {Ω : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomain N p Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼) :
    IsSobolevExtensionDomain N p (affinePreimage T c Ω) :=
  hΩ.of_preimage_affine T c rfl

omit [Fact (1 ≤ p)] in
/-- **Being an extension domain for every exponent is affine-invariant** (preimage form). -/
theorem IsSobolevExtensionDomainAll.of_preimage_affine {Ω Ω' : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll N Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼)
    (hΩ' : (Ω' : Set 𝔼) = (fun x ↦ T x + c) ⁻¹' Ω) : IsSobolevExtensionDomainAll N Ω' :=
  fun q _ ↦ (hΩ q).of_preimage_affine T c hΩ'

omit [Fact (1 ≤ p)] in
/-- **Being an extension domain for every exponent is affine-invariant** (image form): every
affine image of an extension domain is one. -/
theorem IsSobolevExtensionDomainAll.of_image_affine {Ω Ω' : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll N Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼)
    (hΩ' : (fun x ↦ T x + c) '' (Ω : Set 𝔼) = Ω') : IsSobolevExtensionDomainAll N Ω' :=
  fun q _ ↦ (hΩ q).of_image_affine T c hΩ'

omit [Fact (1 ≤ p)] in
/-- The affine preimage `affinePreimage T c Ω` of an extension domain for every exponent is one. -/
theorem IsSobolevExtensionDomainAll.affinePreimage {Ω : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll N Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼) :
    IsSobolevExtensionDomainAll N (affinePreimage T c Ω) :=
  fun q _ ↦ (hΩ q).affinePreimage T c

end AffineInvariance

/-! ### Extension domains from extension steps -/

section Steps

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **An extension step into a domain with an extension operator in the shape of Theorem 9.7**
gives one on the smaller domain: for `Ω ⊆ Ω₁`, a bounded linear `S : W^{1,p}(Ω) → W^{1,p}(Ω₁)`
with `S u = u` on `Ω` and `‖S u‖_{L^p(Ω₁)} ≤ C ‖u‖_{L^p(Ω)}`, and an extension operator on `Ω₁`,
the composite `u ↦ P (S u)` is an extension operator on `Ω` with the product of the constants
(`SobolevEuclidean.extension_step_comp`, `SobolevEuclidean.exists_extensionL_of_ops'`). -/
theorem SobolevEuclidean.exists_extensionL_of_step {Ω Ω₁ : Opens 𝔼} (hle : Ω ≤ Ω₁)
    (h : ∃ (S : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₁) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₁ : Set 𝔼))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼)))
    (hΩ₁ : ∃ (P : SobolevEuclidean N 1 p Ω₁ →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω₁ : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₁ : Set 𝔼)) ∧
        ‖P u‖ ≤ C * ‖u‖) :
    ∃ (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨S, C₁, hC₁, hS⟩ := h
  obtain ⟨P, C, hP⟩ := hΩ₁
  have hP' : ∀ w, SobolevMultiIndex.fn (P w) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      SobolevMultiIndex.fn w ∧
      eLpNorm (SobolevMultiIndex.fn (P w)) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))
        ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Ω₁ : Set 𝔼)) :=
    fun w ↦ ⟨(hP w).1.filter_mono
      (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 hle) le_rfl)),
      by rw [eLpNorm_restrict_coe_top]; exact (hP w).2.1⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤,
      ∀ u, Q u = P (S u) := ⟨P ∘L S, fun u ↦ rfl⟩
  exact SobolevEuclidean.exists_extensionL_of_ops' Q
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC₁)
    (SobolevEuclidean.extension_step_comp S P Q hQ hS hP')

end Steps

/-! ### The unit square -/

section UnitSquare

/-- **The unit square is a Sobolev extension domain for every exponent**: Brezis's Remark 9
(`SobolevEuclidean.exists_extensionL_unitSquare`), read as the backbone's predicate. -/
theorem isSobolevExtensionDomainAll_unitSquare :
    IsSobolevExtensionDomainAll 2 (EuclideanSpace.rect 0 1 0 1) := fun q _ ↦
  IsSobolevExtensionDomain.of_exists_extensionL
    (SobolevEuclidean.exists_extensionL_unitSquare (p := q))

end UnitSquare

/-! ### The reference triangle, the half diamond and the diamond -/

section TriangleSets

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanSpace

/-- **The reference triangle** `T̂ = {(x, y) : x > 0, y > 0, x + y < 1}` of the finite element
method ([han2009theoretical] §10.3), as an open set of `ℝ²`. -/
def referenceTriangle : Opens 𝔼₂ :=
  ⟨{x | 0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < 1}, by
    have h0 : Continuous fun x : 𝔼₂ ↦ x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun x : 𝔼₂ ↦ x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (isOpen_lt continuous_const h0).inter ((isOpen_lt continuous_const h1).inter
      (isOpen_lt (h0.add h1) continuous_const))⟩

/-- Membership of the reference triangle, unfolded. -/
theorem mem_referenceTriangle {x : 𝔼₂} :
    x ∈ (referenceTriangle : Set 𝔼₂) ↔ 0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < 1 :=
  Iff.rfl

/-- **The half diamond** `{(x, y) : x > 0, x + |y| < 1}`: the reference triangle, its reflection
across the side `y = 0`, and the open side between them. -/
def halfDiamond : Opens 𝔼₂ :=
  ⟨{x | 0 < x 0 ∧ x 0 + |x 1| < 1}, by
    have h0 : Continuous fun x : 𝔼₂ ↦ x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun x : 𝔼₂ ↦ x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (isOpen_lt continuous_const h0).inter (isOpen_lt (h0.add h1.abs) continuous_const)⟩

/-- Membership of the half diamond, unfolded. -/
theorem mem_halfDiamond {x : 𝔼₂} :
    x ∈ (halfDiamond : Set 𝔼₂) ↔ 0 < x 0 ∧ x 0 + |x 1| < 1 :=
  Iff.rfl

/-- **The diamond** `{(x, y) : |x| + |y| < 1}`: the half diamond, its reflection across `x = 0`,
and the open side between them; an affine image of the unit square. -/
def diamond : Opens 𝔼₂ :=
  ⟨{x | |x 0| + |x 1| < 1}, by
    have h0 : Continuous fun x : 𝔼₂ ↦ x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun x : 𝔼₂ ↦ x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact isOpen_lt (h0.abs.add h1.abs) continuous_const⟩

/-- Membership of the diamond, unfolded. -/
theorem mem_diamond {x : 𝔼₂} : x ∈ (diamond : Set 𝔼₂) ↔ |x 0| + |x 1| < 1 :=
  Iff.rfl

/-- The reference triangle lies in the half diamond. -/
theorem referenceTriangle_subset_halfDiamond :
    (referenceTriangle : Set 𝔼₂) ⊆ halfDiamond := fun x hx ↦ by
  rw [mem_referenceTriangle] at hx
  rw [mem_halfDiamond, abs_of_pos hx.2.1]
  exact ⟨hx.1, hx.2.2⟩

/-- The half diamond lies in the diamond. -/
theorem halfDiamond_subset_diamond : (halfDiamond : Set 𝔼₂) ⊆ diamond := fun x hx ↦ by
  rw [mem_halfDiamond] at hx
  rw [mem_diamond, abs_of_pos hx.1]
  exact hx.2

/-- The reference triangle lies in the half diamond. -/
theorem referenceTriangle_le_halfDiamond : referenceTriangle ≤ halfDiamond :=
  SetLike.coe_subset_coe.1 referenceTriangle_subset_halfDiamond

/-- The half diamond lies in the diamond. -/
theorem halfDiamond_le_diamond : halfDiamond ≤ diamond :=
  SetLike.coe_subset_coe.1 halfDiamond_subset_diamond

/-- The reference triangle lies in the open unit ball. -/
theorem referenceTriangle_subset_ball : (referenceTriangle : Set 𝔼₂) ⊆ ball 0 1 := fun x hx ↦ by
  rw [mem_referenceTriangle] at hx
  rw [mem_ball_zero_iff]
  refine (EuclideanSpace.norm_le_abs_add_abs x).trans_lt ?_
  rw [abs_of_pos hx.1, abs_of_pos hx.2.1]
  exact hx.2.2

/-- The reference triangle is bounded. -/
theorem isBounded_referenceTriangle : Bornology.IsBounded (referenceTriangle : Set 𝔼₂) :=
  isBounded_ball.subset referenceTriangle_subset_ball

/-- The reference triangle is convex: the intersection of three open half planes. -/
theorem convex_referenceTriangle : Convex ℝ (referenceTriangle : Set 𝔼₂) := by
  have h0 := (convex_Ioi (0 : ℝ)).linear_preimage
    ((EuclideanSpace.proj (0 : Fin 2) : 𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →ₗ[ℝ] ℝ)
  have h1 := (convex_Ioi (0 : ℝ)).linear_preimage
    ((EuclideanSpace.proj (1 : Fin 2) : 𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →ₗ[ℝ] ℝ)
  have h2 := (convex_Iio (1 : ℝ)).linear_preimage
    (((EuclideanSpace.proj (0 : Fin 2) : 𝔼₂ →L[ℝ] ℝ) + (EuclideanSpace.proj (1 : Fin 2) :
      𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →ₗ[ℝ] ℝ)
  convert (h0.inter h1).inter h2 using 1
  ext x
  rw [mem_referenceTriangle]
  simp [and_assoc]

/-- The closure of the reference triangle lies in the closed triangle
`{x ≥ 0, y ≥ 0, x + y ≤ 1}`. -/
theorem closure_referenceTriangle_subset :
    closure (referenceTriangle : Set 𝔼₂) ⊆ {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} := by
  have h0 : Continuous fun x : 𝔼₂ ↦ x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun x : 𝔼₂ ↦ x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  refine closure_minimal (fun x hx ↦ ?_) ((isClosed_le continuous_const h0).inter
    ((isClosed_le continuous_const h1).inter (isClosed_le (h0.add h1) continuous_const)))
  rw [mem_referenceTriangle] at hx
  exact ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩

/-- **The closed triangle lies in the closure of the open one**: a point with `x ≥ 0`, `y ≥ 0`,
`x + y ≤ 1` is the limit of the points `x + t (c − x)`, `t → 0⁺`, with `c = (1/3, 1/3)` the
centroid. -/
theorem mem_closure_referenceTriangle {x : 𝔼₂} (hx : 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1) :
    x ∈ closure (referenceTriangle : Set 𝔼₂) := by
  obtain ⟨c, hc⟩ : ∃ c : 𝔼₂, c = !₂[(1 : ℝ) / 3, 1 / 3] := ⟨_, rfl⟩
  have hc0 : c 0 = 1 / 3 := by rw [hc]; rfl
  have hc1 : c 1 = 1 / 3 := by rw [hc]; rfl
  have hlim : Tendsto (fun t : ℝ ↦ x + t • (c - x)) (𝓝[>] 0) (𝓝 x) := by
    have h : Tendsto (fun t : ℝ ↦ x + t • (c - x)) (𝓝 0) (𝓝 (x + (0 : ℝ) • (c - x))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  rw [mem_referenceTriangle]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hc0, hc1]
  obtain ⟨hx0, hx1, hx2⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.2 ht.2.le) hx0, ht.1]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht.2.le) hx1, ht.1]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht.2.le) (sub_nonneg.2 hx2), ht.1]

/-- The closure of the reference triangle is the closed triangle. -/
theorem closure_referenceTriangle :
    closure (referenceTriangle : Set 𝔼₂) = {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} :=
  Subset.antisymm closure_referenceTriangle_subset fun _ hx ↦ mem_closure_referenceTriangle hx

/-- The closed ball of radius `1/8` about `(1/4, 1/4)` lies in the reference triangle: an
inscribed ball of diameter `ρ̂ = 1/4`. -/
theorem closedBall_subset_referenceTriangle :
    closedBall (!₂[(1 : ℝ) / 4, 1 / 4] : 𝔼₂) ((1 / 4 : ℝ) / 2) ⊆ (referenceTriangle : Set 𝔼₂) := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  have h0 := (PiLp.norm_apply_le (x - !₂[(1 : ℝ) / 4, 1 / 4]) 0).trans hx
  have h1 := (PiLp.norm_apply_le (x - !₂[(1 : ℝ) / 4, 1 / 4]) 1).trans hx
  simp only [PiLp.sub_apply, Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
    abs_le] at h0 h1
  rw [mem_referenceTriangle]
  refine ⟨?_, ?_, ?_⟩ <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- **The vertices** `(0, 0), (1, 0), (0, 1)` of the reference triangle, the nodes of the linear
element. -/
def referenceTriangleVertex : Fin 3 → 𝔼₂ := ![!₂[0, 0], !₂[1, 0], !₂[0, 1]]

/-- **The barycentric coordinates** `λ₀ = 1 − x − y`, `λ₁ = x`, `λ₂ = y` of the reference
triangle, the shape functions of the linear element ([han2009theoretical] Example 10.3.2). -/
def baryCoord : Fin 3 → 𝔼₂ → ℝ := ![fun x ↦ 1 - x 0 - x 1, fun x ↦ x 0, fun x ↦ x 1]

/-- The barycentric coordinates sum to `1`. -/
theorem sum_baryCoord (x : 𝔼₂) : ∑ i, baryCoord i x = 1 := by
  simp only [baryCoord, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- A point is the barycentric combination of the vertices with its barycentric coordinates. -/
theorem sum_baryCoord_smul_vertex (x : 𝔼₂) :
    ∑ i, baryCoord i x • referenceTriangleVertex i = x := by
  ext j
  fin_cases j <;> simp [baryCoord, referenceTriangleVertex, Fin.sum_univ_three]

/-- **The open triangle is where all three barycentric coordinates are positive.** -/
theorem mem_referenceTriangle_iff_baryCoord_pos {x : 𝔼₂} :
    x ∈ (referenceTriangle : Set 𝔼₂) ↔ ∀ i, 0 < baryCoord i x := by
  rw [mem_referenceTriangle]
  constructor
  · rintro ⟨h1, h2, h3⟩ i
    fin_cases i <;> simp [baryCoord] <;> linarith
  · intro h
    have h0 := h 0
    simp only [baryCoord, Fin.isValue, Matrix.cons_val_zero] at h0
    exact ⟨h 1, h 2, by linarith⟩

/-- The barycentric coordinates are dual to the vertices: `λᵢ(xⱼ) = δᵢⱼ`. -/
theorem baryCoord_apply_vertex (i j : Fin 3) :
    baryCoord i (referenceTriangleVertex j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [baryCoord, referenceTriangleVertex]

/-- The vertices lie in the closure of the reference triangle. -/
theorem referenceTriangleVertex_mem_closure (i : Fin 3) :
    referenceTriangleVertex i ∈ closure (referenceTriangle : Set 𝔼₂) := by
  refine mem_closure_referenceTriangle ?_
  fin_cases i <;> simp [referenceTriangleVertex]

/-- The barycentric coordinates are smooth (affine). -/
theorem contDiff_baryCoord (i : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (baryCoord i) := by
  have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : 𝔼₂ ↦ x 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : 𝔼₂ →L[ℝ] ℝ).contDiff
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : 𝔼₂ ↦ x 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : 𝔼₂ →L[ℝ] ℝ).contDiff
  fin_cases i
  · exact (contDiff_const.sub h0).sub h1
  · exact h0
  · exact h1

/-! #### The diamond as an affine image of the unit square -/

/-- `|a| + |b| = max (|a + b|, |a − b|)`, in the form of the inequality `< r`. -/
theorem _root_.abs_add_abs_lt_iff {a b r : ℝ} : |a| + |b| < r ↔ |a + b| < r ∧ |a - b| < r := by
  constructor
  · intro h
    exact ⟨(abs_add_le a b).trans_lt h, (abs_sub a b).trans_lt h⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨h1a, h1b⟩ := abs_lt.1 h1
    obtain ⟨h2a, h2b⟩ := abs_lt.1 h2
    rcases abs_cases a with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rcases abs_cases b with ⟨hb, -⟩ | ⟨hb, -⟩ <;>
      linarith

/-- The linear map `(x, y) ↦ ((x + y)/2, (x − y)/2)`. -/
def diamondLinear : 𝔼₂ →ₗ[ℝ] 𝔼₂ where
  toFun x := !₂[(x 0 + x 1) / 2, (x 0 - x 1) / 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

/-- The linear map `(a, b) ↦ (a + b, a − b)`, the inverse of `diamondLinear`. -/
def diamondLinearInv : 𝔼₂ →ₗ[ℝ] 𝔼₂ where
  toFun y := !₂[y 0 + y 1, y 0 - y 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

/-- **The linear part of the affine map carrying the diamond onto the unit square**,
`(x, y) ↦ ((x + y)/2, (x − y)/2)`, as a continuous linear equivalence of `ℝ²`; the affine map is
`x ↦ diamondEquiv x + (1/2, 1/2)`. -/
def diamondEquiv : 𝔼₂ ≃L[ℝ] 𝔼₂ :=
  (LinearEquiv.ofLinearMap diamondLinear diamondLinearInv
    (LinearMap.ext fun y ↦ by
      ext i
      fin_cases i <;> simp [diamondLinear, diamondLinearInv])
    (LinearMap.ext fun x ↦ by
      ext i
      fin_cases i <;> simp [diamondLinear, diamondLinearInv] <;> ring)).toContinuousLinearEquiv

/-- `diamondEquiv (x, y) = ((x + y)/2, (x − y)/2)`. -/
@[simp]
theorem diamondEquiv_apply (x : 𝔼₂) :
    diamondEquiv x = !₂[(x 0 + x 1) / 2, (x 0 - x 1) / 2] :=
  rfl

/-- **The diamond is the affine preimage of the unit square** under
`(x, y) ↦ ((x + y + 1)/2, (x − y + 1)/2)`: `|x| + |y| < 1` if and only if `|x + y| < 1` and
`|x − y| < 1`. -/
theorem coe_diamond_eq_preimage :
    (diamond : Set 𝔼₂) = (fun x ↦ diamondEquiv x + !₂[(1 : ℝ) / 2, 1 / 2]) ⁻¹'
      (EuclideanSpace.rect 0 1 0 1 : Set 𝔼₂) := by
  ext x
  rw [Set.mem_preimage, EuclideanSpace.mem_rect, mem_diamond, abs_add_abs_lt_iff, abs_lt, abs_lt]
  simp only [diamondEquiv_apply, PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

end EuclideanSpace

end TriangleSets

/-! ### The extension operator of the reference triangle -/

section TriangleExtension

open EuclideanSpace

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The reflection of the reference triangle across its side `y = 0`**: an extension operator
`W^{1,p}(T̂) → W^{1,p}(halfDiamond)` (`SobolevEuclidean.exists_reflectionStep` with `v = e₂`,
`c = 0`, `V` the half diamond, whose positive half is the triangle). -/
theorem SobolevEuclidean.exists_extension_referenceTriangle_step₁ :
    ∃ (S : SobolevEuclidean 2 1 p referenceTriangle →L[ℝ] SobolevEuclidean 2 1 p halfDiamond)
      (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (referenceTriangle : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (halfDiamond : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (referenceTriangle : Set _)) := by
  have hinv : Function.Involutive (hyperplaneReflection
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := EuclideanSpace.single 1 (1 : ℝ)) (c := 0) (by simp)
    (V := halfDiamond) (Ω₀ := referenceTriangle) (Ω₁ := halfDiamond)
    (by
      refine hinv.image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [mem_halfDiamond, hyperplaneReflection_single_apply, Fin.isValue, zero_ne_one,
        ↓reduceIte, abs_neg])
    (by
      ext x
      simp only [coe_posHalf, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, add_zero, mem_halfDiamond,
        mem_referenceTriangle]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h3, by rwa [abs_of_pos h3] at h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, by rwa [abs_of_pos h2]⟩, h2⟩)
    (by
      ext x
      simp)

/-- **The reflection of the half diamond across `x = 0`**: an extension operator
`W^{1,p}(halfDiamond) → W^{1,p}(diamond)`. -/
theorem SobolevEuclidean.exists_extension_referenceTriangle_step₂ :
    ∃ (S : SobolevEuclidean 2 1 p halfDiamond →L[ℝ] SobolevEuclidean 2 1 p diamond)
      (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (halfDiamond : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (diamond : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (halfDiamond : Set _)) := by
  have hinv : Function.Involutive (hyperplaneReflection
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := EuclideanSpace.single 0 (1 : ℝ)) (c := 0) (by simp)
    (V := diamond) (Ω₀ := halfDiamond) (Ω₁ := diamond)
    (by
      refine hinv.image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [mem_diamond, hyperplaneReflection_single_apply, Fin.isValue, one_ne_zero,
        ↓reduceIte, abs_neg])
    (by
      ext x
      simp only [coe_posHalf, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, add_zero, mem_halfDiamond,
        mem_diamond]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, by rwa [abs_of_pos h2] at h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [abs_of_pos h1], h1⟩)
    (by
      ext x
      simp)

/-- **The diamond has an extension operator** in the shape of Theorem 9.7: it is the affine
preimage of the unit square (`EuclideanSpace.coe_diamond_eq_preimage`), which has one
(`SobolevEuclidean.exists_extensionL_unitSquare`). -/
theorem SobolevEuclidean.exists_extensionL_diamond :
    ∃ (P : SobolevEuclidean 2 1 p diamond →L[ℝ] SobolevEuclidean 2 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (diamond : Set _)]
          SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (diamond : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ :=
  SobolevEuclidean.exists_extensionL_of_preimage_affine diamondEquiv !₂[(1 : ℝ) / 2, 1 / 2]
    coe_diamond_eq_preimage (SobolevEuclidean.exists_extensionL_unitSquare (p := p))

/-- **The reference triangle has an extension operator**: for
`T̂ = {(x, y) : x > 0, y > 0, x + y < 1}` and `1 ≤ p ≤ ∞` there are a bounded linear
`P : W^{1,p}(T̂) → W^{1,p}(ℝ²)` and a constant `C` with `P u = u` on `T̂`,
`‖P u‖_{L^p(ℝ²)} ≤ C ‖u‖_{L^p(T̂)}` and `‖P u‖_{W^{1,p}(ℝ²)} ≤ C ‖u‖_{W^{1,p}(T̂)}`, the shape of
`SobolevEuclidean.exists_extensionL` (Brezis's Theorem 9.7), although the triangle is only
Lipschitz. By the reflection across `y = 0` to the half diamond, the reflection across `x = 0`
to the diamond, and the diamond's operator (the unit square's transported along an affine
bijection). -/
theorem SobolevEuclidean.exists_extensionL_referenceTriangle :
    ∃ (P : SobolevEuclidean 2 1 p referenceTriangle →L[ℝ] SobolevEuclidean 2 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (referenceTriangle : Set _)]
          SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (referenceTriangle : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ :=
  SobolevEuclidean.exists_extensionL_of_step referenceTriangle_le_halfDiamond
    (SobolevEuclidean.exists_extension_referenceTriangle_step₁ (p := p))
    (SobolevEuclidean.exists_extensionL_of_step halfDiamond_le_diamond
      (SobolevEuclidean.exists_extension_referenceTriangle_step₂ (p := p))
      (SobolevEuclidean.exists_extensionL_diamond (p := p)))

omit [Fact (1 ≤ p)] in
/-- **The diamond is a Sobolev extension domain for every exponent.** -/
theorem isSobolevExtensionDomainAll_diamond : IsSobolevExtensionDomainAll 2 diamond :=
  fun q _ ↦ IsSobolevExtensionDomain.of_exists_extensionL
    (SobolevEuclidean.exists_extensionL_diamond (p := q))

omit [Fact (1 ≤ p)] in
/-- **The reference triangle is a Sobolev extension domain for every exponent**
(`SobolevEuclidean.exists_extensionL_referenceTriangle`, read as the backbone's predicate): the
hypothesis under which the finite element interpolation estimates of [han2009theoretical] §10.3
are stated applies to the book's reference element. -/
theorem isSobolevExtensionDomainAll_referenceTriangle :
    IsSobolevExtensionDomainAll 2 referenceTriangle :=
  fun q _ ↦ IsSobolevExtensionDomain.of_exists_extensionL
    (SobolevEuclidean.exists_extensionL_referenceTriangle (p := q))

omit [Fact (1 ≤ p)] in
/-- **Every nondegenerate triangle of the plane is a Sobolev extension domain for every
exponent**: an open set `K` which is the image `F(T̂)` of the reference triangle under an affine
bijection `F x = T x + c` — the triangle with vertices `c`, `T e₁ + c`, `T e₂ + c` — inherits the
extension operator of `T̂` (`IsSobolevExtensionDomainAll.of_image_affine`). -/
theorem isSobolevExtensionDomainAll_of_image_referenceTriangle
    {K : Opens (EuclideanSpace ℝ (Fin 2))}
    (T : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 2))
    (hK : (fun x ↦ T x + c) '' (referenceTriangle : Set _) = K) :
    IsSobolevExtensionDomainAll 2 K :=
  isSobolevExtensionDomainAll_referenceTriangle.of_image_affine T c hK

end TriangleExtension

/-! ### The triangle with given vertices -/

section Vertices

open EuclideanSpace

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanSpace

/-- The linear map `x ↦ x₀ u + x₁ v` of `ℝ²`. -/
def spanLinear (u v : 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂ :=
  ((EuclideanSpace.proj (0 : Fin 2) : 𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →ₗ[ℝ] ℝ).smulRight u
    + ((EuclideanSpace.proj (1 : Fin 2) : 𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →ₗ[ℝ] ℝ).smulRight v

/-- `spanLinear u v x = x₀ u + x₁ v`. -/
@[simp]
theorem spanLinear_apply (u v x : 𝔼₂) : spanLinear u v x = x 0 • u + x 1 • v := by
  simp [spanLinear]

/-- `x ↦ x₀ u + x₁ v` is injective when `u, v` are linearly independent. -/
theorem spanLinear_injective {u v : 𝔼₂} (h : LinearIndependent ℝ ![u, v]) :
    Function.Injective (spanLinear u v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [spanLinear_apply] at hx
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.1 h (x 0) (x 1) hx
  ext i
  fin_cases i <;> simp [h0, h1]

/-- **The linear part `x ↦ x₀ (B − A) + x₁ (C − A)` of the affine map carrying the reference
triangle onto the triangle with vertices `A, B, C`**, for `A, B, C` not collinear, as a
continuous linear equivalence of `ℝ²`. -/
def triangleEquiv (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) : 𝔼₂ ≃L[ℝ] 𝔼₂ :=
  (LinearEquiv.ofInjectiveEndo (spanLinear (B - A) (C - A))
    (spanLinear_injective h)).toContinuousLinearEquiv

/-- `triangleEquiv A B C h x = x₀ (B − A) + x₁ (C − A)`. -/
@[simp]
theorem triangleEquiv_apply (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) (x : 𝔼₂) :
    triangleEquiv A B C h x = x 0 • (B - A) + x 1 • (C - A) :=
  spanLinear_apply _ _ _

/-- **The open triangle with vertices `A, B, C`**,
`{A + s (B − A) + t (C − A) : s > 0, t > 0, s + t < 1}`: the image of the reference triangle
under the affine map `x ↦ A + x₀ (B − A) + x₁ (C − A)`. -/
def openTriangle (A B C : 𝔼₂) : Set 𝔼₂ :=
  (fun x : 𝔼₂ ↦ A + x 0 • (B - A) + x 1 • (C - A)) '' (referenceTriangle : Set 𝔼₂)

/-- Membership of the open triangle: the barycentric description with positive weights. -/
theorem mem_openTriangle {A B C x : 𝔼₂} :
    x ∈ openTriangle A B C ↔
      ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ s + t < 1 ∧ x = A + s • (B - A) + t • (C - A) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_referenceTriangle] at hy
    exact ⟨y 0, y 1, hy.1, hy.2.1, hy.2.2, rfl⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    refine ⟨!₂[s, t], ?_, rfl⟩
    rw [mem_referenceTriangle]
    exact ⟨hs, ht, hst⟩

/-- The open triangle is the image of the reference triangle under the affine bijection
`x ↦ triangleEquiv A B C h x + A`. -/
theorem openTriangle_eq_image (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    openTriangle A B C
      = (fun x ↦ triangleEquiv A B C h x + A) '' (referenceTriangle : Set 𝔼₂) := by
  unfold openTriangle
  congr 1
  funext x
  rw [triangleEquiv_apply]
  abel

/-- The open triangle with non-collinear vertices is open. -/
theorem isOpen_openTriangle (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    IsOpen (openTriangle A B C) := by
  rw [openTriangle_eq_image A B C h]
  exact ((triangleEquiv A B C h).affineHomeomorph A).isOpenMap _ referenceTriangle.isOpen

/-- The open triangle with non-collinear vertices `A, B, C`, as an open set. -/
def openTriangleOpens (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) : Opens 𝔼₂ :=
  ⟨openTriangle A B C, isOpen_openTriangle A B C h⟩

/-- The underlying set of `openTriangleOpens A B C h` is `openTriangle A B C`. -/
@[simp]
theorem coe_openTriangleOpens (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    (openTriangleOpens A B C h : Set 𝔼₂) = openTriangle A B C :=
  rfl

end EuclideanSpace

/-- **Every triangle of the plane with non-collinear vertices `A, B, C` is a Sobolev extension
domain for every exponent**: an open set `K` equal to the open triangle
`{A + s (B − A) + t (C − A) : s, t > 0, s + t < 1}` is the affine image of the reference
triangle (`EuclideanSpace.openTriangle_eq_image`), hence inherits its extension operator. -/
theorem isSobolevExtensionDomainAll_of_eq_openTriangle (A B C : 𝔼₂)
    (h : LinearIndependent ℝ ![B - A, C - A]) {K : Opens 𝔼₂}
    (hK : (K : Set 𝔼₂) = openTriangle A B C) : IsSobolevExtensionDomainAll 2 K :=
  isSobolevExtensionDomainAll_of_image_referenceTriangle (triangleEquiv A B C h) A
    (by rw [hK, openTriangle_eq_image A B C h])

/-- The open triangle with non-collinear vertices is a Sobolev extension domain for every
exponent. -/
theorem isSobolevExtensionDomainAll_openTriangleOpens (A B C : 𝔼₂)
    (h : LinearIndependent ℝ ![B - A, C - A]) :
    IsSobolevExtensionDomainAll 2 (openTriangleOpens A B C h) :=
  isSobolevExtensionDomainAll_of_eq_openTriangle A B C h rfl

end Vertices

end
