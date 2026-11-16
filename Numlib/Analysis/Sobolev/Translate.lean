/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Operators

/-!
# Translations of Sobolev functions on an invariant open set

Let $\Omega$ be an open subset of a normed space $E$ that is invariant under the translation by $h$,
that is, $x + h \in \Omega$ if and only if $x \in \Omega$, and let $\mu$ be a right-invariant
measure on $E$. This module shows that the translation $\tau_h u = u(\cdot + h)$ is a linear
isometry of $L^p(\Omega)$ and of $W^{k,p}(\Omega)$, that it commutes with the weak derivatives, and
that it preserves $W_0^{k,p}(\Omega)$. This is the machinery behind the method of translations of L.
Nirenberg for the regularity of elliptic equations ([brezis2011functional], §9.6, on the whole space
and on the half space $\{x_N > 0\}$, which is invariant under the tangential translations). It is
also behind the translation invariance of the whole-line problems of [brezis2011functional], §8.4.

A last section treats a general open set $\Omega$ and the translated domain
$\Omega - h = \{x : x + h \in \Omega\}$: the translation carries functions on $\Omega$, their weak
derivatives and their integrals against test functions to $\Omega - h$.

## Main definitions

* `IsTranslationInvariant`: the set $\Omega$ is invariant under the translation by $h$.
* `TestFunction.compAddRightOn`: the translate $\varphi(\cdot + h)$ of a test function on an
  invariant open set $\Omega$, as a test function on $\Omega$.
* `MeasureTheory.Lp.translate`: the translation $\tau_h$ as a linear isometry of $L^p(\Omega)$.
* `SobolevMultiIndex.translateL`: the translation $\tau_h$ as a linear isometry of
  $W^{k,p}(\Omega)$.

## Main results

* `IsTranslationInvariant.measurePreserving`: the translation by $h$ preserves the restriction of
  $\mu$ to an invariant open set $\Omega$.
* `LocallyIntegrableOn.comp_add_right` and `MeasureTheory.MemLp.comp_add_right`: the translate of a
  function that is locally integrable on $\Omega$, or in $L^p(\Omega)$, is again one.
* `integral_smul_comp_add_right`: the change of variables $\int_\Omega \psi(x) u(x + h) \, dx =
  \int_\Omega \psi(x - h) u(x) \, dx$ against a test function $\psi$.
* `HasWeakIteratedLineDerivOn.comp_add_right`: translation commutes with the weak derivative.
* `MeasureTheory.Lp.translate_neg_translate` and `MeasureTheory.Lp.inner_translate`:
  $\tau_{-h} \tau_h = 1$ on $L^p(\Omega)$, and $\langle \tau_h u, v \rangle = \langle u, \tau_{-h} v
  \rangle$ in $L^2(\Omega)$.
* `SobolevMultiIndex.weakDeriv_translateL`: the weak derivatives of $\tau_h u$ are the translates of
  the weak derivatives of $u$.
* `SobolevMultiIndex.translateL_mem_zero`: $W_0^{k,p}(\Omega)$ is invariant under the translations
  that leave $\Omega$ invariant ([brezis2011functional], §9.6, (54)).
* `HasWeakIteratedLineDerivOn.comp_add_right_of_preimage`: the translation carries a weak derivative
  on $\Omega$ to a weak derivative on $\Omega - h$.

## Implementation notes

* Everything is stated for a general normed space $E$ (proper, hence finite-dimensional, where
  $W^{k,p}(\Omega)$ or local integrability is involved), a general target $F$ and a right-invariant
  measure $\mu$. The invariance of $\Omega$ is an explicit hypothesis, not a property of a named
  domain; the half space and the whole space are instances.
* The sign of the translation is $\tau_h u = u(\cdot + h)$. The whole-space translation
  `MeasureTheory.Lp.translateₗᵢ` of `Numlib.Analysis.Convolution.Bochner` is
  $g \mapsto g(\cdot - y)$, the convention of harmonic analysis, so
  `MeasureTheory.Lp.translateₗᵢ 𝕜 F p (-h)` is `MeasureTheory.Lp.translate` on $\Omega = E$.
* The difference quotients $D_h = (\tau_h - 1)/|h|$ built on these isometries are the tool of one
  proof, and they are defined with it in `Numlib.Analysis.PDE.Elliptic.Regularity`.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### Open sets invariant under a translation -/

section Invariant

variable {E : Type*} [AddGroup E]

/-- Let $E$ be an additive group. A set $\Omega \subseteq E$ is **invariant under the translation
by** $h \in E$ if $x + h \in \Omega$ if and only if $x \in \Omega$, for every $x \in E$. The
whole space is invariant under every translation, and the half space $\{x_N > 0\}$ is invariant
under the tangential translations, those with $h_N = 0$. This is what the method of translations
of [brezis2011functional], §9.6, needs of the domain. -/
def IsTranslationInvariant (Ω : Set E) (h : E) : Prop := ∀ x, x + h ∈ Ω ↔ x ∈ Ω

namespace IsTranslationInvariant

variable {Ω : Set E} {h : E}

/-- If $\Omega$ is invariant under the translation by $h$ and $x \in \Omega$, then
$x + h \in \Omega$. -/
theorem mem (hΩ : IsTranslationInvariant Ω h) {x : E} (hx : x ∈ Ω) : x + h ∈ Ω := (hΩ x).2 hx

/-- If $\Omega$ is invariant under the translation by $h$, then the preimage of $\Omega$ under
$x \mapsto x + h$ is $\Omega$. -/
theorem preimage_eq (hΩ : IsTranslationInvariant Ω h) : (· + h) ⁻¹' Ω = Ω :=
  Set.ext fun x ↦ hΩ x

/-- A set that is invariant under the translation by $h$ is invariant under the translation by $-h$.
-/
theorem neg (hΩ : IsTranslationInvariant Ω h) : IsTranslationInvariant Ω (-h) := fun x ↦ by
  have := hΩ (x + -h)
  rw [neg_add_cancel_right] at this
  exact this.symm

/-- The whole space is invariant under every translation. -/
theorem univ (h : E) : IsTranslationInvariant (univ : Set E) h := fun _ ↦ Iff.rfl

/-- Every set is invariant under the translation by $0$. -/
theorem zero (Ω : Set E) : IsTranslationInvariant Ω 0 := fun x ↦ by rw [add_zero]

/-- A set that is invariant under the translations by $h$ and by $h'$ is invariant under the
translation by $h + h'$. -/
theorem add {h' : E} (hΩ : IsTranslationInvariant Ω h) (hΩ' : IsTranslationInvariant Ω h') :
    IsTranslationInvariant Ω (h + h') := fun x ↦ by
  rw [← add_assoc, hΩ', hΩ]

end IsTranslationInvariant

end Invariant

section InvariantSmul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $E$ be a real normed space, let $\Omega \subseteq E$ and let $y \in E$. If $\Omega$ is
invariant under the translation by $t y$ for every $t \in \mathbb{R}$, then $x + t y \in \Omega$
for every $x \in \Omega$ and every $t \in \mathbb{R}$. So $\Omega$ contains the lines through
its points in the direction $y$. -/
theorem IsTranslationInvariant.smul_mem {Ω : Set E} {y : E}
    (hΩ : ∀ t : ℝ, IsTranslationInvariant Ω (t • y)) {x : E} (hx : x ∈ Ω) (t : ℝ) :
    x + t • y ∈ Ω :=
  (hΩ t).mem hx

end InvariantSmul

/-! ### Translations of locally integrable functions and of test functions -/

section Translate

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
  {Ω : Opens E} {h : E}

omit [NormedSpace ℝ E] in
/-- Let $E$ have its Borel σ-algebra, let $\mu$ be a right-invariant measure on $E$, and let
$\Omega \subseteq E$ be open and invariant under the translation by $h$. Then the map
$x \mapsto x + h$ preserves the restriction $\mu|_\Omega$. -/
theorem IsTranslationInvariant.measurePreserving [μ.IsAddRightInvariant]
    (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    MeasurePreserving (· + h) (μ.restrict (Ω : Set E)) (μ.restrict (Ω : Set E)) := by
  have := (measurePreserving_add_right μ h).restrict_preimage Ω.isOpen.measurableSet
  rwa [hΩ.preimage_eq] at this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Let $E$ be proper with its Borel σ-algebra, let $\mu$ be right-invariant, and let $\Omega$ and
$\Omega'$ be open sets with $\Omega' = \{x : x + h \in \Omega\} = \Omega - h$. If $u$ is locally
integrable on $\Omega$, then $x \mapsto u(x + h)$ is locally integrable on $\Omega'$. -/
theorem LocallyIntegrableOn.comp_add_right_of_preimage [μ.IsAddRightInvariant] [ProperSpace E]
    {Ω' : Opens E} {u : E → F} (hu : LocallyIntegrableOn u Ω μ)
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    LocallyIntegrableOn (fun x ↦ u (x + h)) Ω' μ := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu
  rw [locallyIntegrableOn_iff Ω'.isOpen.isLocallyClosed]
  intro k hk hkc
  have hk' : (· + h) '' k ⊆ (Ω : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    have := hk hx
    rw [hΩ'] at this
    exact this
  have := hu ((· + h) '' k) hk' (hkc.image (continuous_id.add continuous_const))
  exact ((measurePreserving_add_right μ h).integrableOn_image
    (MeasurableEquiv.addRight h).measurableEmbedding).1 this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Let $E$ be proper with its Borel σ-algebra, let $\mu$ be right-invariant, and let $\Omega$ be
open and invariant under the translation by $h$. If $u$ is locally integrable on $\Omega$, then
$x \mapsto u(x + h)$ is locally integrable on $\Omega$. -/
theorem LocallyIntegrableOn.comp_add_right [μ.IsAddRightInvariant] [ProperSpace E] {u : E → F}
    (hu : LocallyIntegrableOn u Ω μ) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    LocallyIntegrableOn (fun x ↦ u (x + h)) Ω μ :=
  LocallyIntegrableOn.comp_add_right_of_preimage hu hΩ.preimage_eq.symm

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Let $E$ have its Borel σ-algebra, let $\mu$ be right-invariant, let $\Omega$ be open and
invariant under the translation by $h$, and let $p \in [0, \infty]$. If $u \in L^p(\Omega)$,
then $x \mapsto u(x + h)$ lies in $L^p(\Omega)$.

The two norms are equal, because the translation preserves the measure; the isometry is
`MeasureTheory.Lp.translate`. -/
theorem MeasureTheory.MemLp.comp_add_right [μ.IsAddRightInvariant] {u : E → F} {p : ℝ≥0∞}
    (hu : MemLp u p (μ.restrict (Ω : Set E))) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    MemLp (fun x ↦ u (x + h)) p (μ.restrict (Ω : Set E)) :=
  hu.comp_measurePreserving hΩ.measurePreserving

/-- Let $\Omega$ be open and invariant under the translation by $h$. For a test function $\varphi$
on $\Omega$, this is the translate $x \mapsto \varphi(x + h)$, as a test function on $\Omega$. -/
def TestFunction.compAddRightOn (φ : 𝓓(Ω, F)) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    𝓓(Ω, F) where
  toFun x := φ (x + h)
  contDiff' := φ.contDiff.comp (contDiff_id.add contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight h)
  tsupport_subset' := by
    have : tsupport (fun x ↦ φ (x + h)) = (Homeomorph.addRight h) ⁻¹' tsupport φ := by
      rw [tsupport, tsupport, (Homeomorph.addRight h).preimage_closure]
      rfl
    rw [this]
    intro x hx
    exact (hΩ x).1 (φ.tsupport_subset hx)

omit [MeasurableSpace E] [BorelSpace E] in
/-- As a function, the translate `TestFunction.compAddRightOn φ hΩ` is $x \mapsto \varphi(x + h)$.
-/
@[simp]
theorem TestFunction.compAddRightOn_coe (φ : 𝓓(Ω, F))
    (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    (φ.compAddRightOn hΩ : E → F) = fun x ↦ φ (x + h) :=
  rfl

/-- Let $\mu$ be right-invariant, let $\Omega$ be open and invariant under the translation by $h$,
let $u : E \to F$, and let $\psi$ be a real test function on $\Omega$. Then the change of
variables $x \mapsto x + h$ gives
$$\int_\Omega \psi(x) \, u(x + h) \, d\mu(x) = \int_\Omega \psi(x - h) \, u(x) \, d\mu(x).$$
No integrability of $u$ is assumed. -/
theorem integral_smul_comp_add_right [μ.IsAddRightInvariant] (u : E → F)
    (hΩ : IsTranslationInvariant (Ω : Set E) h) (ψ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set E), ψ x • u (x + h) ∂μ = ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ := by
  have e1 : ∫ x in (Ω : Set E), ψ x • u (x + h) ∂μ = ∫ x, ψ x • u (x + h) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [ψ.eq_zero_of_notMem hx, zero_smul]
  have e2 : ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ = ∫ x, ψ (x - h) • u x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      have := (ψ.compAddRightOn hΩ.neg).eq_zero_of_notMem hx
      simp only [TestFunction.compAddRightOn_coe, ← sub_eq_add_neg] at this
      rw [this, zero_smul]
  rw [e1, e2, ← integral_add_right_eq_self (fun x ↦ ψ (x - h) • u x) h]
  simp only [add_sub_cancel_right]

end Translate

/-! ### The translation commutes with the weak derivative -/

section WeakDerivTranslate

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
  [μ.IsAddRightInvariant] {Ω : Opens E} {h : E}

/-- **Translation commutes with the weak derivative.** Let $E$ be a proper real normed space with
its Borel σ-algebra, let $\mu$ be right-invariant, and let $\Omega$ be open and invariant under
the translation by $h$. If $w$ is a weak derivative of $u$ along the tuple $y \in E^n$ of
directions on $\Omega$, then $x \mapsto w(x + h)$ is a weak derivative of $x \mapsto u(x + h)$
along $y$ on $\Omega$.

The proof replaces the test function $\varphi$ by its translate $\varphi(\cdot - h)$, which is
again a test function on $\Omega$. -/
theorem HasWeakIteratedLineDerivOn.comp_add_right {n : ℕ} {y : Fin n → E} {u w : E → F}
    (hu : HasWeakIteratedLineDerivOn y u w Ω μ) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    HasWeakIteratedLineDerivOn y (fun x ↦ u (x + h)) (fun x ↦ w (x + h)) Ω μ where
  locallyIntegrableOn := LocallyIntegrableOn.comp_add_right hu.locallyIntegrableOn hΩ
  locallyIntegrableOn_weakDeriv :=
    LocallyIntegrableOn.comp_add_right hu.locallyIntegrableOn_weakDeriv hΩ
  integral_smul_eq φ := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(Ω, ℝ), (ψ : E → ℝ) = fun x ↦ φ (x - h) :=
      ⟨φ.compAddRightOn hΩ.neg, by simp [sub_eq_add_neg]⟩
    have hψd : ∀ x, iteratedFDeriv ℝ n (ψ : E → ℝ) x y
        = iteratedFDeriv ℝ n (φ : E → ℝ) (x - h) y := fun x ↦ by
      rw [hψ, iteratedFDeriv_comp_sub']
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • u (x + h) ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n ψ x y • u x ∂μ := by
      have := integral_smul_comp_add_right (μ := μ) u hΩ (φ.iteratedFDerivApply n y)
      simp only [TestFunction.iteratedFDerivApply_apply] at this
      rw [this]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψd])
    have e2 : ∫ x in (Ω : Set E), φ x • w (x + h) ∂μ = ∫ x in (Ω : Set E), ψ x • w x ∂μ := by
      rw [integral_smul_comp_add_right (μ := μ) w hΩ φ]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψ])
    rw [e1, e2, hu.integral_smul_eq ψ]

end WeakDerivTranslate

/-! ### Translations on $L^p(\Omega)$ -/

namespace MeasureTheory.Lp

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} [μ.IsAddRightInvariant]
  {Ω : Opens E} {h : E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (F p) in
/-- Let $p \ge 1$, let $E$ have its Borel σ-algebra, let $\mu$ be right-invariant, and let $\Omega$
be open and invariant under the translation by $h$. The **translation** by $h$ on $L^p(\Omega)$
is the map $\tau_h u = u(\cdot + h)$. It is a linear isometry of $L^p(\Omega)$, by the
translation invariance of the measure.

The map is `MeasureTheory.Lp.compMeasurePreservingₗᵢ` for $x \mapsto x + h$. -/
def translate (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    Lp F p (μ.restrict (Ω : Set E)) →ₗᵢ[ℝ] Lp F p (μ.restrict (Ω : Set E)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (· + h) hΩ.measurePreserving

/-- For $u \in L^p(\Omega)$, the translate $\tau_h u$ equals $x \mapsto u(x + h)$ almost everywhere
on $\Omega$. -/
theorem coeFn_translate (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : Lp F p (μ.restrict (Ω : Set E))) :
    translate F p hΩ u =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ u (x + h) :=
  Lp.coeFn_compMeasurePreserving u hΩ.measurePreserving

/-- Translating by $h$ and then by $-h$ is the identity on $L^p(\Omega)$: $\tau_{-h}(\tau_h u) = u$.
-/
theorem translate_neg_translate (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : Lp F p (μ.restrict (Ω : Set E))) :
    translate F p hΩ.neg (translate F p hΩ u) = u := by
  refine Lp.ext ?_
  have h1 := coeFn_translate hΩ.neg (translate F p hΩ u)
  have h2 := hΩ.neg.measurePreserving.quasiMeasurePreserving.ae_eq_comp (coeFn_translate hΩ u)
  refine h1.trans (h2.trans (Eventually.of_forall fun x ↦ ?_))
  simp

/-- **Adjointness of the translations** in $L^2(\Omega)$. For real functions $u, v \in L^2(\Omega)$,
$$\langle \tau_h u, v \rangle = \langle u, \tau_{-h} v \rangle.$$
The proof is the change of variables $x \mapsto x - h$. -/
theorem inner_translate (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u v : Lp ℝ 2 (μ.restrict (Ω : Set E))) :
    ⟪translate ℝ 2 hΩ u, v⟫_ℝ = ⟪u, translate ℝ 2 hΩ.neg v⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∫ x, ⟪translate ℝ 2 hΩ u x, v x⟫_ℝ ∂(μ.restrict (Ω : Set E))
      = ∫ x, u (x + h) * v x ∂(μ.restrict (Ω : Set E)) := by
    refine integral_congr_ae ((coeFn_translate hΩ u).mono fun x hx ↦ ?_)
    simp [hx, mul_comm]
  have e2 : ∫ x, ⟪u x, translate ℝ 2 hΩ.neg v x⟫_ℝ ∂(μ.restrict (Ω : Set E))
      = ∫ x, u x * v (x + -h) ∂(μ.restrict (Ω : Set E)) := by
    refine integral_congr_ae ((coeFn_translate hΩ.neg v).mono fun x hx ↦ ?_)
    simp [hx, mul_comm]
  rw [e1, e2, ← hΩ.measurePreserving.integral_comp (MeasurableEquiv.addRight h).measurableEmbedding
    (fun x ↦ u x * v (x + -h))]
  simp only [add_neg_cancel_right]

end MeasureTheory.Lp

/-! ### Translations on $W^{k,p}(\Omega)$ -/

namespace SobolevMultiIndex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [μ.IsAddRightInvariant] {h : E}

variable (F b k p μ) in
/-- For $u \in W^{k,p}(\Omega)$, the family $(\tau_h \partial^\alpha u)_{|\alpha| \le k}$ of the
translates of its weak derivatives, as an element of the ambient $\ell^p$ product
`SobolevMultiIndexTuple F ι k p Ω μ`. -/
def translateTuple (hΩ : IsTranslationInvariant (Ω : Set E) h) (u : SobolevMultiIndex F b k p Ω μ) :
    SobolevMultiIndexTuple F ι k p Ω μ :=
  WithLp.toLp p fun α ↦ Lp.translate F p hΩ (weakDeriv u α)

/-- For $u \in W^{k,p}(\Omega)$, the family of the translates of its weak derivatives lies in
$W^{k,p}(\Omega)$, because translation commutes with the weak derivatives
(`HasWeakIteratedLineDerivOn.comp_add_right`). -/
theorem translateTuple_mem (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) :
    translateTuple F b k p μ hΩ u ∈ SobolevMultiIndex F b k p Ω μ := fun α ↦
  ((hasWeakIteratedLineDerivOn u α).comp_add_right hΩ).congr_ae
    (Lp.coeFn_translate hΩ (weakDeriv u 0)).symm (Lp.coeFn_translate hΩ (weakDeriv u α)).symm

variable (F b k p μ) in
/-- Let $p \ge 1$, let $E$ be a proper real normed space with its Borel σ-algebra and a basis $b$
indexed by a finite linearly ordered type, let $\mu$ be right-invariant, and let $\Omega$ be
open and invariant under the translation by $h$. The **translation** by $h$ on $W^{k,p}(\Omega)$
is the linear isometry $\tau_h$ that maps $u$, with weak derivatives $\partial^\alpha u$ for
$|\alpha| \le k$, to the element with weak derivatives $\tau_h \partial^\alpha u$. This is the
map $u \mapsto \tau_h u$ of [brezis2011functional], §9.6.

The space $W^{k,p}(\Omega)$ is `SobolevMultiIndex F b k p Ω μ`. Every weak derivative is
translated by `HasWeakIteratedLineDerivOn.comp_add_right`, and each $L^p(\Omega)$ norm is
preserved. The invariance of $H^1_0(\mathbb{R}^N_+)$ under the tangential translations is
`SobolevMultiIndex.translateL_mem_zero`. -/
def translateL (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    SobolevMultiIndex F b k p Ω μ →ₗᵢ[ℝ] SobolevMultiIndex F b k p Ω μ where
  toLinearMap :=
    { toFun := fun u ↦ ⟨translateTuple F b k p μ hΩ u, translateTuple_mem hΩ u⟩
      map_add' := fun u v ↦ Subtype.ext (PiLp.ext fun α ↦ by
        exact map_add (Lp.translate F p hΩ) (weakDeriv u α) (weakDeriv v α))
      map_smul' := fun c u ↦ Subtype.ext (PiLp.ext fun α ↦ by
        exact map_smul (Lp.translate F p hΩ) c (weakDeriv u α)) }
  norm_map' u := by
    rw [← Submodule.norm_coe, ← Submodule.norm_coe]
    refine le_antisymm (PiLp.norm_le_norm_of_forall_norm_le fun α ↦ ?_)
      (PiLp.norm_le_norm_of_forall_norm_le fun α ↦ ?_)
    · exact (LinearIsometry.norm_map _ _).le
    · exact (LinearIsometry.norm_map _ _).symm.le

/-- For $u \in W^{k,p}(\Omega)$ and each multi-index $\alpha$ with $|\alpha| \le k$, the weak
derivative of the translate is the translate of the weak derivative: $\partial^\alpha(\tau_h
u) = \tau_h \partial^\alpha u$ in $L^p(\Omega)$. -/
theorem weakDeriv_translateL (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    weakDeriv (translateL F b k p μ hΩ u) α = Lp.translate F p hΩ (weakDeriv u α) :=
  rfl

/-- For $u \in W^{k,p}(\Omega)$, the function of $\tau_h u$ equals $x \mapsto v(x + h)$ almost
everywhere on $\Omega$, where $v$ is the function of $u$. -/
theorem fn_translateL (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) :
    fn (translateL F b k p μ hΩ u) =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ fn u (x + h) :=
  Lp.coeFn_translate hΩ (weakDeriv u 0)

/-- **$W_0^{k,p}(\Omega)$ is invariant under the translations that leave $\Omega$ invariant**: if
$u \in W_0^{k,p}(\Omega)$, then $\tau_h u \in W_0^{k,p}(\Omega)$. For $W^{1,2}$ this is
[brezis2011functional], §9.6, (54): "$H^1_0(\Omega)$ is invariant under tangential
translations".

The translate of a test function on $\Omega$ is a test function on $\Omega$, and the translation
is continuous on $W^{k,p}(\Omega)$, so it preserves the closure
`SobolevMultiIndexZero F b k p Ω μ` of the test functions. -/
theorem translateL_mem_zero (hΩ : IsTranslationInvariant (Ω : Set E) h)
    {u : SobolevMultiIndex F b k p Ω μ} (hu : u ∈ SobolevMultiIndexZero F b k p Ω μ) :
    translateL F b k p μ hΩ u ∈ SobolevMultiIndexZero F b k p Ω μ := by
  have hT : ∀ v ∈ testFunctions F b k p Ω μ,
      translateL F b k p μ hΩ v ∈ testFunctions F b k p Ω μ := by
    rintro v ⟨φ, hφ⟩
    refine ⟨φ.compAddRightOn hΩ, (fn_translateL hΩ v).trans ?_⟩
    rw [TestFunction.compAddRightOn_coe]
    exact hΩ.measurePreserving.quasiMeasurePreserving.ae_eq_comp hφ
  have hmem : u ∈ closure (testFunctions F b k p Ω μ : Set (SobolevMultiIndex F b k p Ω μ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hu
  change translateL F b k p μ hΩ u ∈ (SobolevMultiIndexZero F b k p Ω μ : Set _)
  rw [SobolevMultiIndexZero, Submodule.topologicalClosure_coe]
  refine closure_mono (image_subset_iff.2 fun v hv => mem_preimage.2 (hT v hv)) ?_
  exact image_closure_subset_closure_image (translateL F b k p μ hΩ).continuous ⟨u, hmem, rfl⟩

end SobolevMultiIndex

/-!
### Translation to a translated domain

The translation $u \mapsto u(\cdot + h)$ carries $W^{1,p}(\Omega)$ to $W^{1,p}(\Omega - h)$, with
the weak derivatives translated. The sections above treat an open set that is invariant under the
translation. This section treats the translated domain $\Omega' = \Omega - h$, which is
`(· + h) ⁻¹' Ω`; the density of smooth functions on a domain with the segment property needs it.
-/

section TranslatePreimage

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
  {Ω Ω' : Opens E} {h : E}

/-- Let $\Omega$ and $\Omega'$ be open sets with $\Omega' = \{x : x + h \in \Omega\} = \Omega - h$.
For a test function $\varphi$ on $\Omega'$, this is the translate $x \mapsto \varphi(x - h)$, as
a test function on $\Omega$. -/
def TestFunction.compSubRightOfPreimage (φ : 𝓓(Ω', F))
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) : 𝓓(Ω, F) where
  toFun x := φ (x - h)
  contDiff' := φ.contDiff.comp (contDiff_id.sub contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight h)
  tsupport_subset' := by
    have : tsupport (fun x ↦ φ (x - h)) = (Homeomorph.subRight h) ⁻¹' tsupport φ := by
      rw [tsupport, tsupport, (Homeomorph.subRight h).preimage_closure]
      rfl
    rw [this]
    intro x hx
    have := φ.tsupport_subset hx
    rw [hΩ'] at this
    simpa using this

omit [NormedSpace ℝ E] in
/-- Let $E$ have its Borel σ-algebra, let $\mu$ be right-invariant, and let $\Omega' = \Omega - h$.
The map $x \mapsto x + h$ is measure preserving from $\mu|_{\Omega'}$ to $\mu|_\Omega$. -/
theorem measurePreserving_add_right_restrict_of_preimage [μ.IsAddRightInvariant]
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    MeasurePreserving (· + h) (μ.restrict (Ω' : Set E)) (μ.restrict (Ω : Set E)) := by
  have := (measurePreserving_add_right μ h).restrict_preimage Ω.isOpen.measurableSet
  rwa [← hΩ'] at this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Let $E$ have its Borel σ-algebra, let $\mu$ be right-invariant, let $\Omega' = \Omega - h$, and
let $p \in [0, \infty]$. If $u \in L^p(\Omega)$, then $x \mapsto u(x + h)$ lies in
$L^p(\Omega')$. -/
theorem MeasureTheory.MemLp.comp_add_right_of_preimage [μ.IsAddRightInvariant] {u : E → F}
    {p : ℝ≥0∞} (hu : MemLp u p (μ.restrict (Ω : Set E)))
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    MemLp (fun x ↦ u (x + h)) p (μ.restrict (Ω' : Set E)) :=
  hu.comp_measurePreserving (measurePreserving_add_right_restrict_of_preimage hΩ')

/-- Let $\mu$ be right-invariant, let $\Omega' = \Omega - h$, let $u : E \to F$, and let $\psi$ be a
real test function on $\Omega'$. Then the change of variables $x \mapsto x + h$ gives
$$\int_{\Omega'} \psi(x) \, u(x + h) \, d\mu(x) = \int_\Omega \psi(x - h) \, u(x) \, d\mu(x).$$
-/
theorem integral_smul_comp_add_right_of_preimage [μ.IsAddRightInvariant] (u : E → F)
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) (ψ : 𝓓(Ω', ℝ)) :
    ∫ x in (Ω' : Set E), ψ x • u (x + h) ∂μ = ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ := by
  have e1 : ∫ x in (Ω' : Set E), ψ x • u (x + h) ∂μ = ∫ x, ψ x • u (x + h) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [ψ.eq_zero_of_notMem hx, zero_smul]
  have e2 : ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ = ∫ x, ψ (x - h) • u x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      have := (ψ.compSubRightOfPreimage hΩ').eq_zero_of_notMem hx
      exact by rw [show ψ (x - h) = 0 from this, zero_smul]
  rw [e1, e2, ← integral_add_right_eq_self (fun x ↦ ψ (x - h) • u x) h]
  simp only [add_sub_cancel_right]

/-- **Translation commutes with the weak derivative, from $\Omega$ to $\Omega - h$.** Let $E$ be a
proper real normed space with its Borel σ-algebra, let $\mu$ be right-invariant, and let
$\Omega' = \Omega - h$. If $w$ is a weak derivative of $u$ along the tuple $y \in E^n$ of
directions on $\Omega$, then $x \mapsto w(x + h)$ is a weak derivative of $x \mapsto u(x + h)$
along $y$ on $\Omega'$.

The proof replaces a test function $\varphi$ on $\Omega'$ by its translate $\varphi(\cdot - h)$,
which is a test function on $\Omega$. -/
theorem HasWeakIteratedLineDerivOn.comp_add_right_of_preimage [μ.IsAddRightInvariant]
    [ProperSpace E] {n : ℕ} {y : Fin n → E} {u w : E → F}
    (hu : HasWeakIteratedLineDerivOn y u w Ω μ)
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    HasWeakIteratedLineDerivOn y (fun x ↦ u (x + h)) (fun x ↦ w (x + h)) Ω' μ where
  locallyIntegrableOn := LocallyIntegrableOn.comp_add_right_of_preimage hu.locallyIntegrableOn hΩ'
  locallyIntegrableOn_weakDeriv :=
    LocallyIntegrableOn.comp_add_right_of_preimage hu.locallyIntegrableOn_weakDeriv hΩ'
  integral_smul_eq φ := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(Ω, ℝ), (ψ : E → ℝ) = fun x ↦ φ (x - h) :=
      ⟨φ.compSubRightOfPreimage hΩ', rfl⟩
    have hψd : ∀ x, iteratedFDeriv ℝ n (ψ : E → ℝ) x y
        = iteratedFDeriv ℝ n (φ : E → ℝ) (x - h) y := fun x ↦ by
      rw [hψ, iteratedFDeriv_comp_sub']
    have e1 : ∫ x in (Ω' : Set E), iteratedFDeriv ℝ n φ x y • u (x + h) ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n ψ x y • u x ∂μ := by
      have := integral_smul_comp_add_right_of_preimage (μ := μ) u hΩ' (φ.iteratedFDerivApply n y)
      simp only [TestFunction.iteratedFDerivApply_apply] at this
      rw [this]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψd])
    have e2 : ∫ x in (Ω' : Set E), φ x • w (x + h) ∂μ = ∫ x in (Ω : Set E), ψ x • w x ∂μ := by
      rw [integral_smul_comp_add_right_of_preimage (μ := μ) w hΩ' φ]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψ])
    rw [e1, e2, hu.integral_smul_eq ψ]

end TranslatePreimage


/-- Let $E$ be a normed additive group, $\theta : E \to \mathbb{R}$ and $h \in E$. The topological
support of $x \mapsto \theta(x + h)$ is contained in the preimage of the topological support of
$\theta$ under $x \mapsto x + h$. -/
theorem tsupport_comp_add_right_subset {E : Type*} [NormedAddCommGroup E] {θ : E → ℝ} (h : E) :
    tsupport (fun x ↦ θ (x + h)) ⊆ (fun x ↦ x + h) ⁻¹' tsupport θ :=
  closure_minimal (fun y hy ↦ subset_closure (by simpa [Function.support] using hy))
    ((isClosed_tsupport θ).preimage (continuous_add_const h))

end
