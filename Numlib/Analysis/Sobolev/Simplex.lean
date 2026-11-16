/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# The reference triangle as a Sobolev extension domain

An open set $\Omega \subseteq \mathbb{R}^N$ is a **$W^{1,p}$-extension domain** if there is a
bounded linear operator $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ with $Pu = u$ almost
everywhere on $\Omega$ (`IsSobolevExtensionDomain`). An extension operator **in the shape of Theorem
9.7** of [brezis2011functional] satisfies in addition, with one constant $C$, the bounds
$\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\Omega)}$ and $\|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C
\|u\|_{W^{1,p}(\Omega)}$. This module proves that the reference triangle $\hat T = \{(x, y) : x >
0,\ y > 0,\ x + y < 1\}$ of the finite element method is a $W^{1,p}$-extension domain for every
$1 \le p \le \infty$, and with it every nondegenerate triangle of the plane. The reference triangle
is the reference element of the linear finite element in [han2009theoretical], §10.3 (Example
10.3.8).

The triangle is a Lipschitz domain but not of class $C^1$, so the extension theorem of
`Numlib.Analysis.Sobolev.Extension` (Theorem 9.7 of [brezis2011functional]) does not apply to it.
Its hypotenuse is not a coordinate line, so the four reflections of the unit square (Remark 9 of
Chapter 9 of [brezis2011functional], `SobolevEuclidean.exists_extensionL_unitSquare`) do not apply
either. The module also proves that being an extension domain is invariant under affine bijections.

## Main definitions

* `EuclideanSpace.referenceTriangle`: the open reference triangle $\hat T$ of $\mathbb{R}^2$.
* `EuclideanSpace.referenceTriangleVertex`, `EuclideanSpace.baryCoord`: the vertices and the
  barycentric coordinates of $\hat T$.
* `EuclideanSpace.halfDiamond`, `EuclideanSpace.diamond`, `EuclideanSpace.diamondEquiv`: the
  intermediate domains $\{x > 0,\ x + |y| < 1\}$ and $\{|x| + |y| < 1\}$, and the linear part of the
  affine map that carries the diamond onto the unit square.
* `EuclideanSpace.openTriangle`: the open triangle with vertices $A, B, C$, the image of $\hat T$
  under $x \mapsto A + x_0 (B - A) + x_1 (C - A)$.
* `EuclideanSpace.triangleEquiv`: the linear part $x \mapsto x_0 (B - A) + x_1 (C - A)$ of that map,
  as a linear equivalence when $A, B, C$ are not collinear.

## Main results

* `IsSobolevExtensionDomain.of_preimage_affine`, `IsSobolevExtensionDomain.of_image_affine`,
  `IsSobolevExtensionDomainAll.of_preimage_affine`, `IsSobolevExtensionDomainAll.of_image_affine`:
  the preimage and the image of an extension domain under an affine bijection are extension domains.
* `SobolevEuclidean.exists_extensionL_of_preimage_affine`: the same for an extension operator in the
  shape of Theorem 9.7.
* `SobolevEuclidean.exists_extensionL_of_step`: if a bounded extension operator maps
  $W^{1,p}(\Omega)$ into $W^{1,p}(\Omega_1)$ and $\Omega_1$ has an extension operator in the shape
  of Theorem 9.7, then $\Omega$ has one.
* `isSobolevExtensionDomainAll_unitSquare`: the unit square is an extension domain for every
  exponent.
* `SobolevEuclidean.exists_extensionL_referenceTriangle`: the reference triangle has an extension
  operator in the shape of Theorem 9.7.
* `isSobolevExtensionDomainAll_referenceTriangle`: the reference triangle is an extension domain for
  every exponent.
* `isSobolevExtensionDomainAll_of_image_referenceTriangle`,
  `isSobolevExtensionDomainAll_of_eq_openTriangle`: every affine image of the reference triangle,
  and so every triangle with non-collinear vertices, is an extension domain for every exponent.

## Proof outline

The reflection across the side $y = 0$ extends $W^{1,p}(\hat T)$ to the half diamond
$\{x > 0,\ x + |y| < 1\}$. The reflection across $x = 0$ extends this space to the diamond
$\{|x| + |y| < 1\}$. The diamond is the preimage of the unit square under the affine map
$F(x, y) = ((x + y + 1)/2, (x - y + 1)/2)$. The transport $u \mapsto u \circ F^{-1}$ to the square,
the extension operator of the square, and the transport $w \mapsto w \circ F$ back are bounded
linear maps, and their composite is the identity on the diamond.

## Implementation notes

* The composites of the proof are first assembled with the operators as variables
  (`SobolevEuclidean.fn_comp_affine_of_ops`, `SobolevEuclidean.exists_extensionL_of_step`), as in
  `Numlib.Analysis.Sobolev.Extension`, and then instantiated once each.
* The transports are `SobolevEuclidean.compDiffeoL` for the affine diffeomorphisms of
  `isDiffeoOnWithBoundedJacobian_affine_top` and `isDiffeoOnWithBoundedJacobian_affine_symm` in
  `Numlib.Analysis.Sobolev.Calculus`.
* A point $x$ of $\mathbb{R}^2$ has the coordinates `x 0` and `x 1`, written $(x, y)$ or
  $(x_0, x_1)$ in the comments.
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

/-! ### Extension domains are affine-invariant -/

section AffineInvariance

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **The composite of the transport to $\Omega$, an extension operator on $\Omega$, and the
transport back is the identity on the preimage.** Let $T$ be a continuous linear automorphism of
$\mathbb{R}^N$, let $c \in \mathbb{R}^N$, let $F(x) = Tx + c$, and let $\Omega, \Omega'$ be open
sets with $\Omega' = F^{-1}(\Omega)$. Let $1 \le p \le \infty$, and let
$$A : W^{1,p}(\Omega') \to W^{1,p}(\Omega), \quad P : W^{1,p}(\Omega) \to
  W^{1,p}(\mathbb{R}^N),$$
$$B : W^{1,p}(\mathbb{R}^N) \to W^{1,p}(\mathbb{R}^N), \quad Q : W^{1,p}(\Omega') \to
  W^{1,p}(\mathbb{R}^N)$$
be bounded linear maps with $Q u = B(P(A u))$ for all $u$. Assume that $Au = u \circ F^{-1}$
almost everywhere on $\Omega$, that $Pw = w$ almost everywhere on $\Omega$, and that
$Bw = w \circ F$ almost everywhere on $\mathbb{R}^N$. Then $Qu = u$ almost everywhere on
$\Omega'$ for every $u \in W^{1,p}(\Omega')$.

The almost-everywhere identities on $\Omega$ pull back along $F$ by
`IsDiffeoOnWithBoundedJacobian.ae_comp_restrict`. -/
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

/-- **The $L^p$ bound of the composite** of `SobolevEuclidean.fn_comp_affine_of_ops`. Let
$\Omega, \Omega'$ be open sets of $\mathbb{R}^N$, let $1 \le p \le \infty$, and let
$A : W^{1,p}(\Omega') \to W^{1,p}(\Omega)$, $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$, $B
: W^{1,p}(\mathbb{R}^N) \to W^{1,p}(\mathbb{R}^N)$ and
$Q : W^{1,p}(\Omega') \to W^{1,p}(\mathbb{R}^N)$ be bounded linear maps with $Qu = B(P(Au))$.
Let $C_1, C_2, C_3 \in [0, \infty]$ with $\|Au\|_{L^p(\Omega)} \le C_1 \|u\|_{L^p(\Omega')}$,
$\|Pw\|_{L^p(\mathbb{R}^N)} \le C_2 \|w\|_{L^p(\Omega)}$ and $\|Bw\|_{L^p(\mathbb{R}^N)} \le C_3
\|w\|_{L^p(\mathbb{R}^N)}$ for all arguments. Then
$$\|Qu\|_{L^p(\mathbb{R}^N)} \le C_3 C_2 C_1 \|u\|_{L^p(\Omega')}.$$
-/
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

/-- **An extension operator in the shape of Theorem 9.7 transports along an affine bijection.** Let
$1 \le p \le \infty$, let $T$ be a continuous linear automorphism of $\mathbb{R}^N$, let
$c \in \mathbb{R}^N$, let $F(x) = Tx + c$, and let $\Omega, \Omega'$ be open sets with
$\Omega' = F^{-1}(\Omega)$. Assume that there are a bounded linear map
$P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ and a constant $C$ such that for every
$u \in W^{1,p}(\Omega)$, $Pu = u$ almost everywhere on $\Omega$, $\|Pu\|_{L^p(\mathbb{R}^N)} \le
C \|u\|_{L^p(\Omega)}$ and $\|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C \|u\|_{W^{1,p}(\Omega)}$. Then
there are a bounded linear map $P' : W^{1,p}(\Omega') \to W^{1,p}(\mathbb{R}^N)$ and a constant
$C'$ with the same three properties on $\Omega'$.

The operator is $P'u = (P(u \circ F^{-1})) \circ F$, built from `SobolevEuclidean.compDiffeoL`
on both sides of $P$. The constant $C'$ contains the constants of the two transports, from
`SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le`. -/
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

/-- **Being a $W^{1,p}$-extension domain is affine-invariant** (preimage form). Let
$1 \le p \le \infty$, let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain, let
$T$ be a continuous linear automorphism of $\mathbb{R}^N$, let $c \in \mathbb{R}^N$, and let
$\Omega'$ be an open set with $\Omega' = F^{-1}(\Omega)$ for $F(x) = Tx + c$. Then $\Omega'$ is
a $W^{1,p}$-extension domain.

The extension operator is $u \mapsto (P(u \circ F^{-1})) \circ F$, where $P$ is the extension
operator of $\Omega$. -/
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

/-- **Being a $W^{1,p}$-extension domain is affine-invariant** (image form). Let
$1 \le p \le \infty$, let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension domain, let
$T$ be a continuous linear automorphism of $\mathbb{R}^N$, let $c \in \mathbb{R}^N$, and let
$\Omega'$ be an open set with $\Omega' = F(\Omega)$ for $F(x) = Tx + c$. Then $\Omega'$ is a
$W^{1,p}$-extension domain. -/
theorem IsSobolevExtensionDomain.of_image_affine {Ω Ω' : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomain N p Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼)
    (hΩ' : (fun x ↦ T x + c) '' (Ω : Set 𝔼) = Ω') : IsSobolevExtensionDomain N p Ω' :=
  hΩ.of_preimage_affine T.symm (-T.symm c)
    (by rw [← hΩ', affine_image_eq_affine_symm_preimage])

/-- Let $1 \le p \le \infty$, and let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,p}$-extension
domain. Then for every continuous linear automorphism $T$ of $\mathbb{R}^N$ and every
$c \in \mathbb{R}^N$, the open set $F^{-1}(\Omega)$ with $F(x) = Tx + c$
(`affinePreimage T c Ω`) is a $W^{1,p}$-extension domain. -/
theorem IsSobolevExtensionDomain.affinePreimage {Ω : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomain N p Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼) :
    IsSobolevExtensionDomain N p (affinePreimage T c Ω) :=
  hΩ.of_preimage_affine T c rfl

omit [Fact (1 ≤ p)] in
/-- **Being an extension domain for every exponent is affine-invariant** (preimage form). Let
$\Omega \subseteq \mathbb{R}^N$ be a $W^{1,q}$-extension domain for every $1 \le q \le \infty$,
let $T$ be a continuous linear automorphism of $\mathbb{R}^N$, let $c \in \mathbb{R}^N$, and let
$\Omega'$ be an open set with $\Omega' = F^{-1}(\Omega)$ for $F(x) = Tx + c$. Then $\Omega'$ is
a $W^{1,q}$-extension domain for every $1 \le q \le \infty$. -/
theorem IsSobolevExtensionDomainAll.of_preimage_affine {Ω Ω' : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll N Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼)
    (hΩ' : (Ω' : Set 𝔼) = (fun x ↦ T x + c) ⁻¹' Ω) : IsSobolevExtensionDomainAll N Ω' :=
  fun q _ ↦ (hΩ q).of_preimage_affine T c hΩ'

omit [Fact (1 ≤ p)] in
/-- **Being an extension domain for every exponent is affine-invariant** (image form). Let
$\Omega \subseteq \mathbb{R}^N$ be a $W^{1,q}$-extension domain for every $1 \le q \le \infty$,
let $T$ be a continuous linear automorphism of $\mathbb{R}^N$, let $c \in \mathbb{R}^N$, and let
$\Omega'$ be an open set with $\Omega' = F(\Omega)$ for $F(x) = Tx + c$. Then $\Omega'$ is a
$W^{1,q}$-extension domain for every $1 \le q \le \infty$. -/
theorem IsSobolevExtensionDomainAll.of_image_affine {Ω Ω' : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll N Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼)
    (hΩ' : (fun x ↦ T x + c) '' (Ω : Set 𝔼) = Ω') : IsSobolevExtensionDomainAll N Ω' :=
  fun q _ ↦ (hΩ q).of_image_affine T c hΩ'

omit [Fact (1 ≤ p)] in
/-- Let $\Omega \subseteq \mathbb{R}^N$ be a $W^{1,q}$-extension domain for every
$1 \le q \le \infty$. Then for every continuous linear automorphism $T$ of $\mathbb{R}^N$ and
every $c \in \mathbb{R}^N$, the open set `affinePreimage T c Ω`, which is $F^{-1}(\Omega)$ for
$F(x) = Tx + c$, is a $W^{1,q}$-extension domain for every $1 \le q \le \infty$. -/
theorem IsSobolevExtensionDomainAll.affinePreimage {Ω : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll N Ω) (T : 𝔼 ≃L[ℝ] 𝔼) (c : 𝔼) :
    IsSobolevExtensionDomainAll N (affinePreimage T c Ω) :=
  fun q _ ↦ (hΩ q).affinePreimage T c

end AffineInvariance

/-! ### Extension domains from extension steps -/

section Steps

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **An extension step into a domain with an extension operator gives an extension operator on the
smaller domain.** Let $1 \le p \le \infty$, and let $\Omega \subseteq \Omega_1$ be open sets of
$\mathbb{R}^N$. Assume that there are a bounded linear map
$S : W^{1,p}(\Omega) \to W^{1,p}(\Omega_1)$ and a constant $C < \infty$ such that $Su = u$
almost everywhere on $\Omega$ and $\|Su\|_{L^p(\Omega_1)} \le C \|u\|_{L^p(\Omega)}$ for every
$u$. Assume that $\Omega_1$ has an extension operator in the shape of Theorem 9.7 of
[brezis2011functional]: a bounded linear map $P : W^{1,p}(\Omega_1) \to W^{1,p}(\mathbb{R}^N)$
and a constant $C_1$ such that $Pu = u$ almost everywhere on $\Omega_1$,
$\|Pu\|_{L^p(\mathbb{R}^N)} \le C_1 \|u\|_{L^p(\Omega_1)}$ and $\|Pu\|_{W^{1,p}(\mathbb{R}^N)}
\le C_1 \|u\|_{W^{1,p}(\Omega_1)}$. Then $\Omega$ has an extension operator with the same three
properties.

The operator is the composite $u \mapsto P(Su)$, with the product of the constants. The proof
uses `SobolevEuclidean.extension_step_comp` and `SobolevEuclidean.exists_extensionL_of_ops'`. -/
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

/-- **The unit square is a Sobolev extension domain for every exponent.** The open square
$(0, 1) \times (0, 1) \subseteq \mathbb{R}^2$ is a $W^{1,q}$-extension domain for every
$1 \le q \le \infty$.

This is Remark 9 of Chapter 9 of [brezis2011functional],
`SobolevEuclidean.exists_extensionL_unitSquare`, stated with the predicate
`IsSobolevExtensionDomainAll`. -/
theorem isSobolevExtensionDomainAll_unitSquare :
    IsSobolevExtensionDomainAll 2 (EuclideanSpace.rect 0 1 0 1) := fun q _ ↦
  IsSobolevExtensionDomain.of_exists_extensionL
    (SobolevEuclidean.exists_extensionL_unitSquare (p := q))

end UnitSquare

/-! ### The reference triangle, the half diamond and the diamond -/

section TriangleSets

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

namespace EuclideanSpace

/-- **The reference triangle** $\hat T = \{(x, y) : x > 0,\ y > 0,\ x + y < 1\}$ of the finite
element method ([han2009theoretical], §10.3), as an open set of $\mathbb{R}^2$. -/
def referenceTriangle : Opens 𝔼₂ :=
  ⟨{x | 0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < 1}, by
    have h0 : Continuous fun x : 𝔼₂ ↦ x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun x : 𝔼₂ ↦ x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (isOpen_lt continuous_const h0).inter ((isOpen_lt continuous_const h1).inter
      (isOpen_lt (h0.add h1) continuous_const))⟩

/-- A point $(x, y)$ of $\mathbb{R}^2$ lies in the reference triangle if and only if $x > 0$,
$y > 0$ and $x + y < 1$. -/
theorem mem_referenceTriangle {x : 𝔼₂} :
    x ∈ (referenceTriangle : Set 𝔼₂) ↔ 0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < 1 :=
  Iff.rfl

/-- **The half diamond** $\{(x, y) : x > 0,\ x + |y| < 1\}$, as an open set of $\mathbb{R}^2$. It is
the union of the reference triangle, its reflection across the side $y = 0$, and the open side
between them. -/
def halfDiamond : Opens 𝔼₂ :=
  ⟨{x | 0 < x 0 ∧ x 0 + |x 1| < 1}, by
    have h0 : Continuous fun x : 𝔼₂ ↦ x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun x : 𝔼₂ ↦ x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (isOpen_lt continuous_const h0).inter (isOpen_lt (h0.add h1.abs) continuous_const)⟩

/-- A point $(x, y)$ of $\mathbb{R}^2$ lies in the half diamond if and only if $x > 0$ and
$x + |y| < 1$. -/
theorem mem_halfDiamond {x : 𝔼₂} :
    x ∈ (halfDiamond : Set 𝔼₂) ↔ 0 < x 0 ∧ x 0 + |x 1| < 1 :=
  Iff.rfl

/-- **The diamond** $\{(x, y) : |x| + |y| < 1\}$, as an open set of $\mathbb{R}^2$. It is the union
of the half diamond, its reflection across $x = 0$, and the open side between them. It is an
affine image of the unit square. -/
def diamond : Opens 𝔼₂ :=
  ⟨{x | |x 0| + |x 1| < 1}, by
    have h0 : Continuous fun x : 𝔼₂ ↦ x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun x : 𝔼₂ ↦ x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact isOpen_lt (h0.abs.add h1.abs) continuous_const⟩

/-- A point $(x, y)$ of $\mathbb{R}^2$ lies in the diamond if and only if $|x| + |y| < 1$. -/
theorem mem_diamond {x : 𝔼₂} : x ∈ (diamond : Set 𝔼₂) ↔ |x 0| + |x 1| < 1 :=
  Iff.rfl

/-- The reference triangle is a subset of the half diamond. -/
theorem referenceTriangle_subset_halfDiamond :
    (referenceTriangle : Set 𝔼₂) ⊆ halfDiamond := fun x hx ↦ by
  rw [mem_referenceTriangle] at hx
  rw [mem_halfDiamond, abs_of_pos hx.2.1]
  exact ⟨hx.1, hx.2.2⟩

/-- The half diamond is a subset of the diamond. -/
theorem halfDiamond_subset_diamond : (halfDiamond : Set 𝔼₂) ⊆ diamond := fun x hx ↦ by
  rw [mem_halfDiamond] at hx
  rw [mem_diamond, abs_of_pos hx.1]
  exact hx.2

/-- The reference triangle is contained in the half diamond, as an inequality of open sets. -/
theorem referenceTriangle_le_halfDiamond : referenceTriangle ≤ halfDiamond :=
  SetLike.coe_subset_coe.1 referenceTriangle_subset_halfDiamond

/-- The half diamond is contained in the diamond, as an inequality of open sets. -/
theorem halfDiamond_le_diamond : halfDiamond ≤ diamond :=
  SetLike.coe_subset_coe.1 halfDiamond_subset_diamond

/-- The reference triangle is a subset of the open unit ball of $\mathbb{R}^2$. -/
theorem referenceTriangle_subset_ball : (referenceTriangle : Set 𝔼₂) ⊆ ball 0 1 := fun x hx ↦ by
  rw [mem_referenceTriangle] at hx
  rw [mem_ball_zero_iff]
  refine (EuclideanSpace.norm_le_abs_add_abs x).trans_lt ?_
  rw [abs_of_pos hx.1, abs_of_pos hx.2.1]
  exact hx.2.2

/-- The reference triangle is bounded. -/
theorem isBounded_referenceTriangle : Bornology.IsBounded (referenceTriangle : Set 𝔼₂) :=
  isBounded_ball.subset referenceTriangle_subset_ball

/-- The reference triangle is convex, as the intersection of three open half planes. -/
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

/-- The closure of the reference triangle is a subset of the closed triangle
$\{(x, y) : x \ge 0,\ y \ge 0,\ x + y \le 1\}$. -/
theorem closure_referenceTriangle_subset :
    closure (referenceTriangle : Set 𝔼₂) ⊆ {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} := by
  have h0 : Continuous fun x : 𝔼₂ ↦ x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun x : 𝔼₂ ↦ x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  refine closure_minimal (fun x hx ↦ ?_) ((isClosed_le continuous_const h0).inter
    ((isClosed_le continuous_const h1).inter (isClosed_le (h0.add h1) continuous_const)))
  rw [mem_referenceTriangle] at hx
  exact ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩

/-- **The closed triangle lies in the closure of the open triangle.** Every point $z = (x, y)$ with
$x \ge 0$, $y \ge 0$ and $x + y \le 1$ lies in the closure of the reference triangle.

The point $z$ is the limit of the points $z + t (g - z)$ as $t \to 0^+$, where $g = (1/3, 1/3)$
is the centroid. -/
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

/-- The closure of the reference triangle is the closed triangle
$\{(x, y) : x \ge 0,\ y \ge 0,\ x + y \le 1\}$. -/
theorem closure_referenceTriangle :
    closure (referenceTriangle : Set 𝔼₂) = {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} :=
  Subset.antisymm closure_referenceTriangle_subset fun _ hx ↦ mem_closure_referenceTriangle hx

/-- The closed ball of radius $1/8$ about $(1/4, 1/4)$ is a subset of the reference triangle. It is
an inscribed ball of diameter $\hat\rho = 1/4$. -/
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

/-- **The vertices** $(0, 0)$, $(1, 0)$, $(0, 1)$ of the reference triangle, indexed by $0, 1, 2$.
They are the nodes of the linear element. -/
def referenceTriangleVertex : Fin 3 → 𝔼₂ := ![!₂[0, 0], !₂[1, 0], !₂[0, 1]]

/-- **The barycentric coordinates** of the reference triangle: $\lambda_0(x, y) = 1 - x - y$,
$\lambda_1(x, y) = x$ and $\lambda_2(x, y) = y$. They are the shape functions of the linear
element ([han2009theoretical], Example 10.3.2).

They are defined on all of $\mathbb{R}^2$. -/
def baryCoord : Fin 3 → 𝔼₂ → ℝ := ![fun x ↦ 1 - x 0 - x 1, fun x ↦ x 0, fun x ↦ x 1]

/-- The barycentric coordinates sum to $1$: $\lambda_0(z) + \lambda_1(z) + \lambda_2(z) = 1$ for
every $z \in \mathbb{R}^2$. -/
theorem sum_baryCoord (x : 𝔼₂) : ∑ i, baryCoord i x = 1 := by
  simp only [baryCoord, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Every point $z \in \mathbb{R}^2$ is the combination $z = \sum_{i=0}^{2} \lambda_i(z) a_i$ of the
vertices $a_i$ of the reference triangle with its barycentric coordinates. -/
theorem sum_baryCoord_smul_vertex (x : 𝔼₂) :
    ∑ i, baryCoord i x • referenceTriangleVertex i = x := by
  ext j
  fin_cases j <;> simp [baryCoord, referenceTriangleVertex, Fin.sum_univ_three]

/-- **The reference triangle is the set where all three barycentric coordinates are positive.** A
point $z \in \mathbb{R}^2$ lies in the reference triangle if and only if $\lambda_i(z) > 0$ for
$i = 0, 1, 2$. -/
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

/-- The barycentric coordinates are dual to the vertices: $\lambda_i(a_j) = \delta_{ij}$ for
$i, j \in \{0, 1, 2\}$. -/
theorem baryCoord_apply_vertex (i j : Fin 3) :
    baryCoord i (referenceTriangleVertex j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [baryCoord, referenceTriangleVertex]

/-- Every vertex of the reference triangle lies in the closure of the reference triangle. -/
theorem referenceTriangleVertex_mem_closure (i : Fin 3) :
    referenceTriangleVertex i ∈ closure (referenceTriangle : Set 𝔼₂) := by
  refine mem_closure_referenceTriangle ?_
  fin_cases i <;> simp [referenceTriangleVertex]

/-- Every barycentric coordinate $\lambda_i$ is smooth ($C^\infty$) on $\mathbb{R}^2$, since it is
affine. -/
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

/-! ### The diamond as an affine image of the unit square -/

/-- For real numbers $a$, $b$ and $r$, $|a| + |b| < r$ if and only if $|a + b| < r$ and
$|a - b| < r$. This is the identity $|a| + |b| = \max\{|a + b|, |a - b|\}$, in the form of an
inequality. -/
theorem _root_.abs_add_abs_lt_iff {a b r : ℝ} : |a| + |b| < r ↔ |a + b| < r ∧ |a - b| < r := by
  constructor
  · intro h
    exact ⟨(abs_add_le a b).trans_lt h, (abs_sub a b).trans_lt h⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨h1a, h1b⟩ := abs_lt.1 h1
    obtain ⟨h2a, h2b⟩ := abs_lt.1 h2
    rcases abs_cases a with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rcases abs_cases b with ⟨hb, -⟩ | ⟨hb, -⟩ <;>
      linarith

/-- The linear map $(x, y) \mapsto ((x + y)/2, (x - y)/2)$ of $\mathbb{R}^2$. -/
def diamondLinear : 𝔼₂ →ₗ[ℝ] 𝔼₂ where
  toFun x := !₂[(x 0 + x 1) / 2, (x 0 - x 1) / 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

/-- The linear map $(a, b) \mapsto (a + b, a - b)$ of $\mathbb{R}^2$, the inverse of
`EuclideanSpace.diamondLinear`. -/
def diamondLinearInv : 𝔼₂ →ₗ[ℝ] 𝔼₂ where
  toFun y := !₂[y 0 + y 1, y 0 - y 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

/-- **The linear part of the affine map that carries the diamond onto the unit square**: the map
$(x, y) \mapsto ((x + y)/2, (x - y)/2)$, as a continuous linear equivalence $L$ of
$\mathbb{R}^2$. The affine map is $x \mapsto L(x) + (1/2, 1/2)$. -/
def diamondEquiv : 𝔼₂ ≃L[ℝ] 𝔼₂ :=
  (LinearEquiv.ofLinearMap diamondLinear diamondLinearInv
    (LinearMap.ext fun y ↦ by
      ext i
      fin_cases i <;> simp [diamondLinear, diamondLinearInv])
    (LinearMap.ext fun x ↦ by
      ext i
      fin_cases i <;> simp [diamondLinear, diamondLinearInv] <;> ring)).toContinuousLinearEquiv

/-- The map `EuclideanSpace.diamondEquiv` sends $(x, y)$ to $((x + y)/2, (x - y)/2)$. -/
@[simp]
theorem diamondEquiv_apply (x : 𝔼₂) :
    diamondEquiv x = !₂[(x 0 + x 1) / 2, (x 0 - x 1) / 2] :=
  rfl

/-- **The diamond is the affine preimage of the unit square.** The diamond is the preimage of the
open square $(0, 1) \times (0, 1)$ under the affine map
$(x, y) \mapsto ((x + y + 1)/2, (x - y + 1)/2)$.

The proof uses that $|x| + |y| < 1$ holds if and only if $|x + y| < 1$ and $|x - y| < 1$
(`abs_add_abs_lt_iff`). -/
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

/-- **The reflection of the reference triangle across its side $y = 0$.** Let $1 \le p \le \infty$.
There are a bounded linear map $S : W^{1,p}(\hat T) \to W^{1,p}(H)$, where $H$ is the half
diamond, and a constant $C < \infty$ such that for every $u \in W^{1,p}(\hat T)$, $Su = u$
almost everywhere on $\hat T$ and $\|Su\|_{L^p(H)} \le C \|u\|_{L^p(\hat T)}$.

This is `SobolevEuclidean.exists_reflectionStep` with the unit vector $v = e_2$, the translation
$c = 0$, and $V$ the half diamond, whose positive half is the triangle. -/
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

/-- **The reflection of the half diamond across $x = 0$.** Let $1 \le p \le \infty$, let $H$ be the
half diamond and let $D$ be the diamond. There are a bounded linear map
$S : W^{1,p}(H) \to W^{1,p}(D)$ and a constant $C < \infty$ such that for every
$u \in W^{1,p}(H)$, $Su = u$ almost everywhere on $H$ and
$\|Su\|_{L^p(D)} \le C \|u\|_{L^p(H)}$. -/
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

/-- **The diamond has an extension operator** in the shape of Theorem 9.7 of [brezis2011functional].
Let $1 \le p \le \infty$ and let $D$ be the diamond. There are a bounded linear map
$P : W^{1,p}(D) \to W^{1,p}(\mathbb{R}^2)$ and a constant $C$ such that for every
$u \in W^{1,p}(D)$, $Pu = u$ almost everywhere on $D$, $\|Pu\|_{L^p(\mathbb{R}^2)} \le C
\|u\|_{L^p(D)}$ and $\|Pu\|_{W^{1,p}(\mathbb{R}^2)} \le C \|u\|_{W^{1,p}(D)}$.

The diamond is the affine preimage of the unit square
(`EuclideanSpace.coe_diamond_eq_preimage`), which has such an operator
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

/-- **The reference triangle has an extension operator** in the shape of Theorem 9.7 of
[brezis2011functional]. Let $1 \le p \le \infty$ and let $\hat T = \{(x, y) : x > 0,\ y > 0,\
x + y < 1\}$. There are a bounded linear map $P : W^{1,p}(\hat T) \to W^{1,p}(\mathbb{R}^2)$ and
a constant $C$ such that for every $u \in W^{1,p}(\hat T)$,
$$Pu = u \text{ a.e. on } \hat T, \qquad \|Pu\|_{L^p(\mathbb{R}^2)} \le C \|u\|_{L^p(\hat T)},
  \qquad \|Pu\|_{W^{1,p}(\mathbb{R}^2)} \le C \|u\|_{W^{1,p}(\hat T)}.$$

This is the shape of `SobolevEuclidean.exists_extensionL`, although the triangle is only
Lipschitz. The operator is the reflection across $y = 0$ to the half diamond, then the
reflection across $x = 0$ to the diamond, then the extension operator of the diamond, which is
the operator of the unit square transported along an affine bijection. -/
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
/-- **The diamond is a Sobolev extension domain for every exponent**: the diamond
$\{(x, y) : |x| + |y| < 1\}$ is a $W^{1,q}$-extension domain for every $1 \le q \le \infty$. -/
theorem isSobolevExtensionDomainAll_diamond : IsSobolevExtensionDomainAll 2 diamond :=
  fun q _ ↦ IsSobolevExtensionDomain.of_exists_extensionL
    (SobolevEuclidean.exists_extensionL_diamond (p := q))

omit [Fact (1 ≤ p)] in
/-- **The reference triangle is a Sobolev extension domain for every exponent**: the reference
triangle $\hat T$ is a $W^{1,q}$-extension domain for every $1 \le q \le \infty$.

This is `SobolevEuclidean.exists_extensionL_referenceTriangle`, stated with the predicate
`IsSobolevExtensionDomainAll`. It shows that the hypothesis under which the finite element
interpolation estimates of [han2009theoretical], §10.3, are stated holds for the reference
element of the book. -/
theorem isSobolevExtensionDomainAll_referenceTriangle :
    IsSobolevExtensionDomainAll 2 referenceTriangle :=
  fun q _ ↦ IsSobolevExtensionDomain.of_exists_extensionL
    (SobolevEuclidean.exists_extensionL_referenceTriangle (p := q))

omit [Fact (1 ≤ p)] in
/-- **Every nondegenerate triangle of the plane is a Sobolev extension domain for every exponent.**
Let $T$ be a continuous linear automorphism of $\mathbb{R}^2$, let $c \in \mathbb{R}^2$, and let
$K$ be an open set with $K = F(\hat T)$ for $F(x) = Tx + c$. Then $K$ is a $W^{1,q}$-extension
domain for every $1 \le q \le \infty$.

The set $K$ is the triangle with vertices $c$, $Te_1 + c$ and $Te_2 + c$. It inherits the
extension operator of $\hat T$ by `IsSobolevExtensionDomainAll.of_image_affine`. -/
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

/-- For $u, v \in \mathbb{R}^2$, the linear map $x \mapsto x_0 u + x_1 v$ of $\mathbb{R}^2$. -/
def spanLinear (u v : 𝔼₂) : 𝔼₂ →ₗ[ℝ] 𝔼₂ :=
  ((EuclideanSpace.proj (0 : Fin 2) : 𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →ₗ[ℝ] ℝ).smulRight u
    + ((EuclideanSpace.proj (1 : Fin 2) : 𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →ₗ[ℝ] ℝ).smulRight v

/-- The map `EuclideanSpace.spanLinear u v` sends $x$ to $x_0 u + x_1 v$. -/
@[simp]
theorem spanLinear_apply (u v x : 𝔼₂) : spanLinear u v x = x 0 • u + x 1 • v := by
  simp [spanLinear]

/-- If $u, v \in \mathbb{R}^2$ are linearly independent, then the map $x \mapsto x_0 u + x_1 v$ is
injective. -/
theorem spanLinear_injective {u v : 𝔼₂} (h : LinearIndependent ℝ ![u, v]) :
    Function.Injective (spanLinear u v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [spanLinear_apply] at hx
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.1 h (x 0) (x 1) hx
  ext i
  fin_cases i <;> simp [h0, h1]

/-- **The linear part of the affine map that carries the reference triangle onto the triangle with
vertices $A, B, C$.** For $A, B, C \in \mathbb{R}^2$ such that $B - A$ and $C - A$ are linearly
independent (that is, $A, B, C$ are not collinear), this is the map
$x \mapsto x_0 (B - A) + x_1 (C - A)$, as a continuous linear equivalence of $\mathbb{R}^2$. -/
def triangleEquiv (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) : 𝔼₂ ≃L[ℝ] 𝔼₂ :=
  (LinearEquiv.ofInjectiveEndo (spanLinear (B - A) (C - A))
    (spanLinear_injective h)).toContinuousLinearEquiv

/-- The map `EuclideanSpace.triangleEquiv A B C h` sends $x$ to $x_0 (B - A) + x_1 (C - A)$. -/
@[simp]
theorem triangleEquiv_apply (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) (x : 𝔼₂) :
    triangleEquiv A B C h x = x 0 • (B - A) + x 1 • (C - A) :=
  spanLinear_apply _ _ _

/-- **The open triangle with vertices $A, B, C$**: the set
$$\{A + s (B - A) + t (C - A) : s > 0,\ t > 0,\ s + t < 1\} \subseteq \mathbb{R}^2,$$
defined as the image of the reference triangle under the affine map
$x \mapsto A + x_0 (B - A) + x_1 (C - A)$.

The definition applies to any three points. For collinear points the set has empty interior. -/
def openTriangle (A B C : 𝔼₂) : Set 𝔼₂ :=
  (fun x : 𝔼₂ ↦ A + x 0 • (B - A) + x 1 • (C - A)) '' (referenceTriangle : Set 𝔼₂)

/-- A point $x \in \mathbb{R}^2$ lies in the open triangle with vertices $A, B, C$ if and only if
$x = A + s (B - A) + t (C - A)$ for some $s > 0$ and $t > 0$ with $s + t < 1$. -/
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

/-- Let $A, B, C \in \mathbb{R}^2$ be such that $B - A$ and $C - A$ are linearly independent. Then
the open triangle with vertices $A, B, C$ is the image of the reference triangle under the
affine bijection $x \mapsto L(x) + A$, where $L$ is `EuclideanSpace.triangleEquiv A B C h`. -/
theorem openTriangle_eq_image (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    openTriangle A B C
      = (fun x ↦ triangleEquiv A B C h x + A) '' (referenceTriangle : Set 𝔼₂) := by
  unfold openTriangle
  congr 1
  funext x
  rw [triangleEquiv_apply]
  abel

/-- Let $A, B, C \in \mathbb{R}^2$ be such that $B - A$ and $C - A$ are linearly independent. Then
the open triangle with vertices $A, B, C$ is an open set. -/
theorem isOpen_openTriangle (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    IsOpen (openTriangle A B C) := by
  rw [openTriangle_eq_image A B C h]
  exact ((triangleEquiv A B C h).affineHomeomorph A).isOpenMap _ referenceTriangle.isOpen

/-- The open triangle with vertices $A, B, C$, as an open set of $\mathbb{R}^2$, for $A, B, C$ such
that $B - A$ and $C - A$ are linearly independent. -/
def openTriangleOpens (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) : Opens 𝔼₂ :=
  ⟨openTriangle A B C, isOpen_openTriangle A B C h⟩

/-- The underlying set of `EuclideanSpace.openTriangleOpens A B C h` is
`EuclideanSpace.openTriangle A B C`. -/
@[simp]
theorem coe_openTriangleOpens (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    (openTriangleOpens A B C h : Set 𝔼₂) = openTriangle A B C :=
  rfl

end EuclideanSpace

/-- **Every triangle of the plane with non-collinear vertices is a Sobolev extension domain for
every exponent.** Let $A, B, C \in \mathbb{R}^2$ be such that $B - A$ and $C - A$ are linearly
independent, and let $K$ be an open set equal to the open triangle
$$\{A + s (B - A) + t (C - A) : s > 0,\ t > 0,\ s + t < 1\}.$$
Then $K$ is a $W^{1,q}$-extension domain for every $1 \le q \le \infty$.

The open triangle is an affine image of the reference triangle
(`EuclideanSpace.openTriangle_eq_image`), and so it inherits the extension operator of the
reference triangle. -/
theorem isSobolevExtensionDomainAll_of_eq_openTriangle (A B C : 𝔼₂)
    (h : LinearIndependent ℝ ![B - A, C - A]) {K : Opens 𝔼₂}
    (hK : (K : Set 𝔼₂) = openTriangle A B C) : IsSobolevExtensionDomainAll 2 K :=
  isSobolevExtensionDomainAll_of_image_referenceTriangle (triangleEquiv A B C h) A
    (by rw [hK, openTriangle_eq_image A B C h])

/-- Let $A, B, C \in \mathbb{R}^2$ be such that $B - A$ and $C - A$ are linearly independent. Then
the open triangle with vertices $A, B, C$ is a $W^{1,q}$-extension domain for every
$1 \le q \le \infty$. -/
theorem isSobolevExtensionDomainAll_openTriangleOpens (A B C : 𝔼₂)
    (h : LinearIndependent ℝ ![B - A, C - A]) :
    IsSobolevExtensionDomainAll 2 (openTriangleOpens A B C h) :=
  isSobolevExtensionDomainAll_of_eq_openTriangle A B C h rfl

end Vertices

end
