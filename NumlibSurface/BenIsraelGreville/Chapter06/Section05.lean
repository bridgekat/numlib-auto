/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.PrincipalAngles
import Numlib.LinearAlgebra.Matrix.QR
import NumlibSurface.BenIsraelGreville.Chapter00.Section06

/-!
# Principal angles between subspaces

Section 6.5 of [benIsrael2003generalized] defines the inclination of two
subspaces and relates their orthogonal projections to principal angles.

## Deviations from the source

* **Lemma 1(b)** (correction). Orthogonality for distinct eigenvalues of
  the projection product applies to its nonzero eigenvalues. At zero the
  kernel need not be orthogonal to the nonzero eigenspaces.
* **Lemma 3** (correction). The projection distance uses the largest
  principal angle for subspaces of equal positive dimension, including
  right-angle padding for zero cosines.
* **Lemma 4 and Theorems 11–12** (scope). The block ranks are positive.
  The book's volume convention assigns zero to rank-zero matrices.
-/

namespace BenIsraelGreville.Chapter06

open scoped InnerProductSpace
open Module

section Inclination

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Definition 2(a)** of [benIsrael2003generalized], Chapter 6. The
product of two orthogonal projections vanishes exactly for orthogonal
subspaces. -/
theorem projectionProduct_eq_zero_iff_orthogonal (L M : Submodule 𝕜 E) :
    L.starProjection ∘L M.starProjection = 0 ↔ L ⟂ M :=
  Submodule.starProjection_comp_starProjection_eq_zero_iff

/-- **Definition 2(b)** of [benIsrael2003generalized], Chapter 6.
Inclined subspaces have a nonzero product of orthogonal projections. -/
def Inclined (L M : Submodule 𝕜 E) : Prop := L.starProjection ∘L M.starProjection ≠ 0

/-- **Definition 2(c)** of [benIsrael2003generalized], Chapter 6.
The parts of the subspaces orthogonal to their intersection are
orthogonal to each other. -/
def OrthogonallyIncident (L M : Submodule 𝕜 E) : Prop :=
  L ⊓ (L ⊓ M)ᗮ ⟂ M ⊓ (L ⊓ M)ᗮ

/-- **Definition 2(d)** of [benIsrael2003generalized], Chapter 6.
The first subspace is completely inclined to the second when its
intersection with the orthogonal complement of the second vanishes. -/
def CompletelyInclined (L M : Submodule 𝕜 E) : Prop := L ⊓ Mᗮ = ⊥

/-- **Definition 2(e)** of [benIsrael2003generalized], Chapter 6.
Each subspace is completely inclined to the other. -/
def TotallyInclined (L M : Submodule 𝕜 E) : Prop :=
  CompletelyInclined L M ∧ CompletelyInclined M L

/-- **Definition 2(f)** of [benIsrael2003generalized], Chapter 6.
The dimension of inclination is the rank of the projection product. -/
noncomputable def inclinationDimension (L M : Submodule 𝕜 E) : ℕ :=
  finrank 𝕜 (L.starProjection ∘L M.starProjection).toLinearMap.range

/-- **Definition 2(g)** of [benIsrael2003generalized], Chapter 6.
The coefficient of inclination is the trace of the projection product. -/
noncomputable def inclinationCoefficient (L M : Submodule 𝕜 E) : 𝕜 :=
  LinearMap.trace 𝕜 E (L.starProjection ∘L M.starProjection).toLinearMap

/-- **Definition 2(h)** of [benIsrael2003generalized], Chapter 6.
Projecting either member of a reciprocal pair onto the opposite
ambient subspace gives the other member. -/
def AreReciprocalSubspaces (L M P Q : Submodule 𝕜 E) : Prop :=
  Q.map L.starProjection.toLinearMap = P ∧ P.map M.starProjection.toLinearMap = Q

/-- **Definition 2(i)** of [benIsrael2003generalized], Chapter 6.
Two nonzero vectors are reciprocal when their lines are reciprocal. -/
def AreReciprocalVectors (L M : Submodule 𝕜 E) (x y : E) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ AreReciprocalSubspaces L M (𝕜 ∙ x) (𝕜 ∙ y)

/-- **Equation (105)** of [benIsrael2003generalized], Chapter 6.
The trace of the product of two line projections is the normalized
product of the two inner products. -/
theorem inclinationCoefficient_span_singleton (x y : E) :
    inclinationCoefficient (𝕜 ∙ x) (𝕜 ∙ y) =
      (inner 𝕜 x y * inner 𝕜 y x) / ((‖x‖ : 𝕜) ^ 2 * (‖y‖ : 𝕜) ^ 2) := by
  let c := inner 𝕜 x y / (‖x‖ : 𝕜) ^ 2 / (‖y‖ : 𝕜) ^ 2
  let f := (innerSL 𝕜 y).toLinearMap
  have he : ((𝕜 ∙ x).starProjection ∘L (𝕜 ∙ y).starProjection).toLinearMap =
      (c • f).smulRight x := by
    ext1 v
    change (𝕜 ∙ x).starProjection ((𝕜 ∙ y).starProjection v) =
      (c * inner 𝕜 y v) • x
    rw [Submodule.starProjection_singleton 𝕜 v, map_smul,
      Submodule.starProjection_singleton 𝕜 y, smul_smul]
    apply congrArg (fun a : 𝕜 => a • x)
    simp only [c, RCLike.ofReal_pow, div_eq_mul_inv]
    ring
  rw [inclinationCoefficient, he, LinearMap.trace_smulRight]
  change c * inner 𝕜 y x = _
  simp only [c, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem mem_left_of_projectionProduct_eigenvector {L M : Submodule 𝕜 E}
    {x : E} {μ : 𝕜} (hμ : μ ≠ 0) (h : L.starProjection (M.starProjection x) = μ • x) :
    x ∈ L := by
  have hx : μ • x ∈ L := h ▸ L.starProjection_apply_mem _
  simpa only [smul_smul, inv_mul_cancel₀ hμ, one_smul] using L.smul_mem μ⁻¹ hx

private theorem projectionProduct_eigenvalue_mul_norm_sq {L M : Submodule 𝕜 E}
    {x : E} {μ : 𝕜} (hx : x ∈ L) (he : L.starProjection (M.starProjection x) = μ • x) :
    μ * (‖x‖ : 𝕜) ^ 2 = (‖M.starProjection x‖ : 𝕜) ^ 2 := by
  have hL : L.starProjection x = x := L.starProjection_eq_self_iff.mpr hx
  have hM : M.starProjection (M.starProjection x) = M.starProjection x :=
    M.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem _)
  calc
    μ * (‖x‖ : 𝕜) ^ 2 = inner 𝕜 x (μ • x) := by
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    _ = inner 𝕜 (L.starProjection x) (M.starProjection x) := by
      rw [← he, Submodule.inner_starProjection_left_eq_right]
    _ = inner 𝕜 (M.starProjection x) (M.starProjection x) := by
      rw [hL, Submodule.inner_starProjection_left_eq_right, hM]
    _ = _ := inner_self_eq_norm_sq_to_K _

/-- **Lemma 1(a)** of [benIsrael2003generalized], Chapter 6. Every
eigenvalue of a product of orthogonal projections is real and lies in
the closed unit interval. -/
theorem lemma_6_1_spectrum {L M : Submodule 𝕜 E} {x : E} {μ : 𝕜}
    (hx : x ≠ 0) (h : L.starProjection (M.starProjection x) = μ • x) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, μ = (t : 𝕜) := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  have he := projectionProduct_eigenvalue_mul_norm_sq
    (mem_left_of_projectionProduct_eigenvector hμ h) h
  have hp : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) _
  have hp' : (‖x‖ : 𝕜) ^ 2 ≠ 0 :=
    pow_ne_zero _ (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx))
  refine ⟨‖M.starProjection x‖ ^ 2 / ‖x‖ ^ 2,
    ⟨div_nonneg (sq_nonneg _) hp.le, (div_le_one hp).mpr ?_⟩, ?_⟩
  · exact pow_le_pow_left₀ (norm_nonneg _) (M.norm_starProjection_apply_le x) _
  · rw [RCLike.ofReal_div, RCLike.ofReal_pow, RCLike.ofReal_pow]
    exact (eq_div_iff hp').mpr he

/-- **Lemma 1(b)** of [benIsrael2003generalized], Chapter 6, for
distinct nonzero eigenvalues. Their eigenspaces are orthogonal. -/
theorem lemma_6_1_orthogonal {L M : Submodule 𝕜 E} {x y : E} {α β : 𝕜}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hab : α ≠ β)
    (hx : L.starProjection (M.starProjection x) = α • x)
    (hy : L.starProjection (M.starProjection y) = β • y) :
    inner 𝕜 x y = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact inner_zero_left _
  have hLx := L.starProjection_eq_self_iff.mpr
    (mem_left_of_projectionProduct_eigenvector hα hx)
  have hLy := L.starProjection_eq_self_iff.mpr
    (mem_left_of_projectionProduct_eigenvector hβ hy)
  obtain ⟨a, -, ha⟩ := lemma_6_1_spectrum hx0 hx
  have he :
      inner 𝕜 (L.starProjection (M.starProjection x)) y =
        inner 𝕜 x (L.starProjection (M.starProjection y)) := by
    rw [L.inner_starProjection_left_eq_right, hLy, M.inner_starProjection_left_eq_right,
      ← L.inner_starProjection_left_eq_right, hLx]
  rw [hx, hy, inner_smul_left, inner_smul_right] at he
  have ha' : (starRingEnd 𝕜) α = α := by rw [ha, RCLike.conj_ofReal]
  rw [ha', ← sub_eq_zero, ← sub_mul] at he
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hab)

/-- **Lemma 1(c)** of [benIsrael2003generalized], Chapter 6.
The fixed space of a projection product is the intersection. -/
theorem lemma_6_1_fixed (L M : Submodule 𝕜 E) (x : E) :
    L.starProjection (M.starProjection x) = x ↔ x ∈ L ⊓ M := by
  constructor
  · intro hx
    have hy := L.norm_starProjection_apply_le (M.starProjection x)
    rw [hx] at hy
    have hM := (M.mem_iff_norm_starProjection x).mpr
      (le_antisymm (M.norm_starProjection_apply_le x) hy)
    exact ⟨hx ▸ L.starProjection_apply_mem _, hM⟩
  · rintro ⟨hL, hM⟩
    rw [M.starProjection_eq_self_iff.mpr hM, L.starProjection_eq_self_iff.mpr hL]

/-- **Lemma 1(d)** of [benIsrael2003generalized], Chapter 6.
The kernel of the product splits into the orthogonal complement of the
second subspace and its intersection with the orthogonal complement of
the first subspace. -/
theorem lemma_6_1_kernel (L M : Submodule 𝕜 E) :
    (L.starProjection ∘L M.starProjection).ker = Mᗮ ⊔ (M ⊓ Lᗮ) ∧
      Disjoint Mᗮ (M ⊓ Lᗮ) := by
  refine ⟨?_, Disjoint.mono_right inf_le_left M.isCompl_orthogonal.disjoint.symm⟩
  ext x
  change L.starProjection (M.starProjection x) = 0 ↔ x ∈ Mᗮ ⊔ (M ⊓ Lᗮ)
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_sup]
  constructor
  · intro hx
    exact ⟨x - M.starProjection x, M.sub_starProjection_mem_orthogonal x,
      M.starProjection x, ⟨M.starProjection_apply_mem x, hx⟩, sub_add_cancel _ _⟩
  · rintro ⟨v, hv, w, ⟨hw, hw'⟩, rfl⟩
    rw [map_add, (M.starProjection_apply_eq_zero_iff).mpr hv, zero_add,
      M.starProjection_eq_self_iff.mpr hw]
    exact hw'

private theorem reciprocalVectors_iff_project {L M : Submodule 𝕜 E} {x y : E} :
    AreReciprocalVectors L M x y ↔ x ≠ 0 ∧ y ≠ 0 ∧
      ∃ a b : 𝕜ˣ, L.starProjection y = (a : 𝕜) • x ∧
        M.starProjection x = (b : 𝕜) • y := by
  unfold AreReciprocalVectors AreReciprocalSubspaces
  simp only [Submodule.map_span, Set.image_singleton, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨hx, hy, hL, hM⟩
    obtain ⟨a, ha⟩ := Submodule.span_singleton_eq_span_singleton.mp hL.symm
    obtain ⟨b, hb⟩ := Submodule.span_singleton_eq_span_singleton.mp hM.symm
    exact ⟨hx, hy, a, b, ha.symm, hb.symm⟩
  · rintro ⟨hx, hy, a, b, ha, hb⟩
    exact ⟨hx, hy, (Submodule.span_singleton_eq_span_singleton.mpr ⟨a, ha.symm⟩).symm,
      (Submodule.span_singleton_eq_span_singleton.mpr ⟨b, hb.symm⟩).symm⟩

/-- **Theorem 8(a)** of [benIsrael2003generalized], Chapter 6.
Reciprocal vectors are eigenvectors of the two projection products at
the common coefficient given by their normalized inner products. -/
theorem theorem_6_8_of_reciprocal {L M : Submodule 𝕜 E} {x y : E}
    (h : AreReciprocalVectors L M x y) :
    let c := (inner 𝕜 x y * inner 𝕜 y x) / ((‖x‖ : 𝕜) ^ 2 * (‖y‖ : 𝕜) ^ 2)
    L.starProjection (M.starProjection x) = c • x ∧
      M.starProjection (L.starProjection y) = c • y := by
  obtain ⟨hx, hy, a, b, ha, hb⟩ := reciprocalVectors_iff_project.mp h
  have hL : x ∈ L := by
    have hm : (a : 𝕜) • x ∈ L := ha ▸ L.starProjection_apply_mem y
    simpa only [smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul] using
      L.smul_mem ((a : 𝕜)⁻¹) hm
  have hM : y ∈ M := by
    have hm : (b : 𝕜) • y ∈ M := hb ▸ M.starProjection_apply_mem x
    simpa only [smul_smul, inv_mul_cancel₀ b.ne_zero, one_smul] using
      M.smul_mem ((b : 𝕜)⁻¹) hm
  have ha' : (a : 𝕜) = inner 𝕜 x y / (‖x‖ : 𝕜) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)))).mpr
    rw [← inner_self_eq_norm_sq_to_K, ← inner_smul_right, ← ha,
      ← L.inner_starProjection_left_eq_right, L.starProjection_eq_self_iff.mpr hL]
  have hb' : (b : 𝕜) = inner 𝕜 y x / (‖y‖ : 𝕜) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)))).mpr
    rw [← inner_self_eq_norm_sq_to_K, ← inner_smul_right, ← hb,
      ← M.inner_starProjection_left_eq_right, M.starProjection_eq_self_iff.mpr hM]
  constructor
  · rw [hb, map_smul, ha, smul_smul, mul_comm (b : 𝕜), ha', hb', div_mul_div_comm]
  · rw [ha, map_smul, hb, smul_smul, ha', hb', div_mul_div_comm]

/-- **Theorem 8(b)** of [benIsrael2003generalized], Chapter 6.
An eigenvector of the projection product with nonzero eigenvalue has
a reciprocal partner obtained by projecting to the second subspace. -/
theorem theorem_6_8_of_eigenvector {L M : Submodule 𝕜 E} {x : E} {μ : 𝕜}
    (hx : x ≠ 0) (hμ : μ ≠ 0) (h : L.starProjection (M.starProjection x) = μ • x) :
    let y := M.starProjection x
    AreReciprocalVectors L M x y ∧ M.starProjection (L.starProjection y) = μ • y := by
  let y := M.starProjection x
  have hy : y ≠ 0 := by
    intro he
    change L.starProjection y = μ • x at h
    rw [he, map_zero] at h
    exact smul_ne_zero hμ hx h.symm
  refine ⟨reciprocalVectors_iff_project.mpr ⟨hx, hy, Units.mk0 μ hμ, 1, h, by simp⟩, ?_⟩
  change M.starProjection (L.starProjection y) = μ • y
  rw [show L.starProjection y = μ • x from h, map_smul]

/-- **Theorem 9** of [benIsrael2003generalized], Chapter 6, Equation
(106). The four orthogonality conditions between reciprocal pairs are
equivalent, and distinct inclination coefficients force orthogonality. -/
theorem theorem_6_9 {L M : Submodule 𝕜 E} {x₁ y₁ x₂ y₂ : E}
    (h₁ : AreReciprocalVectors L M x₁ y₁) (h₂ : AreReciprocalVectors L M x₂ y₂) :
    (inner 𝕜 x₁ x₂ = 0 ↔ inner 𝕜 x₁ y₂ = 0) ∧
    (inner 𝕜 x₁ x₂ = 0 ↔ inner 𝕜 y₁ x₂ = 0) ∧
    (inner 𝕜 x₁ x₂ = 0 ↔ inner 𝕜 y₁ y₂ = 0) ∧
    (inclinationCoefficient (𝕜 ∙ x₁) (𝕜 ∙ y₁) ≠
      inclinationCoefficient (𝕜 ∙ x₂) (𝕜 ∙ y₂) → inner 𝕜 x₁ x₂ = 0) := by
  obtain ⟨hx₁, _, a₁, b₁, ha₁, hb₁⟩ := reciprocalVectors_iff_project.mp h₁
  obtain ⟨hx₂, _, a₂, b₂, ha₂, hb₂⟩ := reciprocalVectors_iff_project.mp h₂
  have hL₁ : L.starProjection (M.starProjection x₁) = ((b₁ : 𝕜) * a₁) • x₁ := by
    rw [hb₁, map_smul, ha₁, smul_smul]
  have hL₂ : L.starProjection (M.starProjection x₂) = ((b₂ : 𝕜) * a₂) • x₂ := by
    rw [hb₂, map_smul, ha₂, smul_smul]
  have hp₁ := L.starProjection_eq_self_iff.mpr
    (mem_left_of_projectionProduct_eigenvector (mul_ne_zero b₁.ne_zero a₁.ne_zero) hL₁)
  have hp₂ := L.starProjection_eq_self_iff.mpr
    (mem_left_of_projectionProduct_eigenvector (mul_ne_zero b₂.ne_zero a₂.ne_zero) hL₂)
  have hy₂ : M.starProjection y₂ = y₂ := by
    apply M.starProjection_eq_self_iff.mpr
    have hm : (b₂ : 𝕜) • y₂ ∈ M := hb₂ ▸ M.starProjection_apply_mem x₂
    simpa only [smul_smul, inv_mul_cancel₀ b₂.ne_zero, one_smul] using
      M.smul_mem ((b₂ : 𝕜)⁻¹) hm
  have hxy : inner 𝕜 x₁ y₂ = (a₂ : 𝕜) * inner 𝕜 x₁ x₂ := by
    calc
      _ = inner 𝕜 (L.starProjection x₁) y₂ := by rw [hp₁]
      _ = _ := by rw [L.inner_starProjection_left_eq_right, ha₂, inner_smul_right]
  have hyx : inner 𝕜 y₁ x₂ = starRingEnd 𝕜 (a₁ : 𝕜) * inner 𝕜 x₁ x₂ := by
    calc
      _ = inner 𝕜 y₁ (L.starProjection x₂) := by rw [hp₂]
      _ = _ := by rw [← L.inner_starProjection_left_eq_right, ha₁, inner_smul_left]
  have hyy : starRingEnd 𝕜 (b₁ : 𝕜) * inner 𝕜 y₁ y₂ = inner 𝕜 x₁ y₂ := by
    rw [← inner_smul_left, ← hb₁, M.inner_starProjection_left_eq_right, hy₂]
  have hs₁ : starRingEnd 𝕜 (a₁ : 𝕜) ≠ 0 := star_ne_zero.mpr a₁.ne_zero
  have hs₂ : starRingEnd 𝕜 (b₁ : 𝕜) ≠ 0 := star_ne_zero.mpr b₁.ne_zero
  have he₁ : inner 𝕜 x₁ x₂ = 0 ↔ inner 𝕜 x₁ y₂ = 0 := by
    rw [hxy, mul_eq_zero, or_iff_right a₂.ne_zero]
  have he₂ : inner 𝕜 x₁ x₂ = 0 ↔ inner 𝕜 y₁ x₂ = 0 := by
    rw [hyx, mul_eq_zero, or_iff_right hs₁]
  have he₃ : inner 𝕜 x₁ y₂ = 0 ↔ inner 𝕜 y₁ y₂ = 0 := by
    rw [← hyy, mul_eq_zero, or_iff_right hs₂]
  refine ⟨he₁, he₂, he₁.trans he₃, ?_⟩
  intro hne
  have hc₁ := (theorem_6_8_of_reciprocal h₁).1
  have hc₂ := (theorem_6_8_of_reciprocal h₂).1
  rw [← inclinationCoefficient_span_singleton] at hc₁ hc₂
  have hh₁ : inclinationCoefficient (𝕜 ∙ x₁) (𝕜 ∙ y₁) = (b₁ : 𝕜) * a₁ :=
    (smul_left_injective 𝕜 hx₁) (hc₁.symm.trans hL₁)
  have hh₂ : inclinationCoefficient (𝕜 ∙ x₂) (𝕜 ∙ y₂) = (b₂ : 𝕜) * a₂ :=
    (smul_left_injective 𝕜 hx₂) (hc₂.symm.trans hL₂)
  rw [hh₁, hh₂] at hne
  exact lemma_6_1_orthogonal (mul_ne_zero b₁.ne_zero a₁.ne_zero)
    (mul_ne_zero b₂.ne_zero a₂.ne_zero) hne hL₁ hL₂

private theorem projectionProduct_range (L M : Submodule 𝕜 E) :
    (L.starProjection ∘L M.starProjection).toLinearMap.range =
      M.map L.starProjection.toLinearMap := by
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp, Submodule.range_starProjection]

private theorem projectionProduct_adjoint (L M : Submodule 𝕜 E) :
    (L.starProjection ∘L M.starProjection).toLinearMap.adjoint =
      (M.starProjection ∘L L.starProjection).toLinearMap := by
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.adjoint_comp, L.starProjection_isSymmetric.adjoint_eq,
    M.starProjection_isSymmetric.adjoint_eq]

/-- **Equation (107)** and **Exercise 66(d)** of [benIsrael2003generalized],
Chapter 6. The two projected images have dimension equal to the rank
of the projection product. -/
theorem projectedSubspaces_finrank (L M : Submodule 𝕜 E) :
    finrank 𝕜 (M.map L.starProjection.toLinearMap) = inclinationDimension L M ∧
    finrank 𝕜 (L.map M.starProjection.toLinearMap) = inclinationDimension L M := by
  constructor
  · rw [inclinationDimension, projectionProduct_range]
  · have h := (L.starProjection ∘L M.starProjection).toLinearMap.finrank_range_adjoint
    rw [projectionProduct_adjoint, projectionProduct_range] at h
    exact h

private theorem map_projectedSubspace (L M : Submodule 𝕜 E) :
    (L.map M.starProjection.toLinearMap).map L.starProjection.toLinearMap =
      M.map L.starProjection.toLinearMap := by
  rw [← projectionProduct_range M L, ← projectionProduct_range L M,
    ← LinearMap.range_comp, ← projectionProduct_adjoint L M]
  have hEq : L.starProjection.toLinearMap ∘ₗ
        (L.starProjection ∘L M.starProjection).toLinearMap.adjoint =
      (L.starProjection ∘L M.starProjection).toLinearMap ∘ₗ
        (L.starProjection ∘L M.starProjection).toLinearMap.adjoint := by
    rw [projectionProduct_adjoint]
    ext1 x
    change L.starProjection (M.starProjection (L.starProjection x)) =
      L.starProjection (M.starProjection (M.starProjection (L.starProjection x)))
    rw [M.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem _)]
  rw [hEq, LinearMap.range_self_comp_adjoint]

/-- The projected images $P_L M$ and $P_M L$ are reciprocal subspaces. -/
theorem projectedSubspaces_reciprocal (L M : Submodule 𝕜 E) :
    AreReciprocalSubspaces L M (M.map L.starProjection.toLinearMap)
      (L.map M.starProjection.toLinearMap) :=
  ⟨map_projectedSubspace L M, map_projectedSubspace M L⟩

/-- **Equation (108)** of [benIsrael2003generalized], Chapter 6.
Passing to the reciprocal projected images preserves the inclination
coefficient. In fact it preserves the projection product. -/
theorem projectedSubspaces_projectionProduct (L M : Submodule 𝕜 E) :
    let P := M.map L.starProjection.toLinearMap
    let Q := L.map M.starProjection.toLinearMap
    P.starProjection ∘L Q.starProjection = L.starProjection ∘L M.starProjection := by
  let P := M.map L.starProjection.toLinearMap
  let Q := L.map M.starProjection.toLinearMap
  let T := L.starProjection ∘L M.starProjection
  have hP : P ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact L.starProjection_apply_mem y
  have hQ : Q ≤ M := by
    rintro _ ⟨y, -, rfl⟩
    exact M.starProjection_apply_mem y
  have hKer : Qᗮ = T.toLinearMap.ker := by
    have he : T.toLinearMap.adjoint.range = Q := by
      change (L.starProjection ∘L M.starProjection).toLinearMap.adjoint.range = _
      rw [projectionProduct_adjoint, projectionProduct_range]
    rw [← he, LinearMap.orthogonal_range, LinearMap.adjoint_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  let y := Q.starProjection x
  change P.starProjection y = T x
  have hx : T (x - y) = 0 := by
    have hx := Q.sub_starProjection_mem_orthogonal x
    rw [hKer] at hx
    exact hx
  have hy : y ∈ M := hQ (Q.starProjection_apply_mem x)
  rw [map_sub, sub_eq_zero] at hx
  rw [hx]
  change P.starProjection y = L.starProjection (M.starProjection y)
  rw [M.starProjection_eq_self_iff.mpr hy]
  exact Submodule.eq_starProjection_of_mem_orthogonal (K := P) ⟨y, hy, rfl⟩
    ((Submodule.orthogonal_le hP) (L.sub_starProjection_mem_orthogonal y))

/-- **Equation (108)** of [benIsrael2003generalized], Chapter 6, in its
trace form for the reciprocal projected images. -/
theorem projectedSubspaces_inclinationCoefficient (L M : Submodule 𝕜 E) :
    inclinationCoefficient (M.map L.starProjection.toLinearMap)
      (L.map M.starProjection.toLinearMap) = inclinationCoefficient L M := by
  unfold inclinationCoefficient
  rw [projectedSubspaces_projectionProduct L M]

private theorem completelyInclined_of_map_starProjection {L P Q : Submodule 𝕜 E}
    (h : Q.map L.starProjection.toLinearMap = P) : CompletelyInclined P Q := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hx' : x ∈ Q.map L.starProjection.toLinearMap := h ▸ hx.1
  obtain ⟨y, hy, he⟩ := hx'
  change L.starProjection y = x at he
  have hxL : x ∈ L := he ▸ L.starProjection_apply_mem y
  have hz := (Submodule.mem_orthogonal Q x).mp hx.2 y hy
  have hi : inner 𝕜 x x = 0 := by
    calc
      _ = inner 𝕜 (L.starProjection y) x := by rw [he]
      _ = inner 𝕜 y x := by
        rw [L.inner_starProjection_left_eq_right, L.starProjection_eq_self_iff.mpr hxL]
      _ = 0 := hz
  rw [Submodule.mem_bot]
  exact inner_self_eq_zero.mp hi

/-- **Exercise 65** and **Exercise 66(c)** of [benIsrael2003generalized],
Chapter 6. The projected images are totally inclined. -/
theorem exercise_6_65 (L M : Submodule 𝕜 E) :
    TotallyInclined (M.map L.starProjection.toLinearMap) (L.map M.starProjection.toLinearMap) :=
  ⟨completelyInclined_of_map_starProjection (map_projectedSubspace L M),
    completelyInclined_of_map_starProjection (map_projectedSubspace M L)⟩

/-- **Exercise 64** of [benIsrael2003generalized], Chapter 6, Equation
(120). Within the first subspace, the orthogonal complements of the
second subspace and the two reciprocal images agree. -/
theorem exercise_6_64 (L M : Submodule 𝕜 E) :
    L ⊓ (M.map L.starProjection.toLinearMap)ᗮ = L ⊓ Mᗮ ∧
    L ⊓ Mᗮ = L ⊓ (L.map M.starProjection.toLinearMap)ᗮ := by
  constructor
  · rw [← projectionProduct_range L M, LinearMap.orthogonal_range, projectionProduct_adjoint]
    ext x
    simp only [Submodule.mem_inf]
    refine and_congr_right fun hx => ?_
    change M.starProjection (L.starProjection x) = 0 ↔ x ∈ Mᗮ
    rw [L.starProjection_eq_self_iff.mpr hx, Submodule.starProjection_apply_eq_zero_iff]
  · rw [← projectionProduct_range M L, LinearMap.orthogonal_range, projectionProduct_adjoint]
    ext x
    simp only [Submodule.mem_inf]
    refine and_congr_right fun hx => ?_
    change x ∈ Mᗮ ↔ L.starProjection (M.starProjection x) = 0
    constructor
    · intro h
      rw [(M.starProjection_apply_eq_zero_iff).mpr h, map_zero]
    · intro h
      have he := projectionProduct_eigenvalue_mul_norm_sq (μ := (0 : 𝕜)) hx
        (by simpa only [zero_smul] using h)
      rw [zero_mul] at he
      have hz := RCLike.ofReal_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
      exact (M.starProjection_apply_eq_zero_iff).mp (norm_eq_zero.mp hz)

/-- **Exercise 66(a,b)** of [benIsrael2003generalized], Chapter 6.
Each ambient subspace splits into the image of the other subspace under
projection and its own directions orthogonal to the other subspace. -/
theorem exercise_6_66_split (L M : Submodule 𝕜 E) :
    let P := M.map L.starProjection.toLinearMap
    let Q := L.map M.starProjection.toLinearMap
    (L = P ⊔ (L ⊓ Mᗮ) ∧ Disjoint P (L ⊓ Mᗮ)) ∧
    (M = Q ⊔ (M ⊓ Lᗮ) ∧ Disjoint Q (M ⊓ Lᗮ)) := by
  have h (U V : Submodule 𝕜 E) :
      let P := V.map U.starProjection.toLinearMap
      U = P ⊔ (U ⊓ Vᗮ) ∧ Disjoint P (U ⊓ Vᗮ) := by
    let P := V.map U.starProjection.toLinearMap
    have hP : P ≤ U := by
      rintro _ ⟨y, -, rfl⟩
      exact U.starProjection_apply_mem y
    have he : U ⊓ Pᗮ = U ⊓ Vᗮ := (exercise_6_64 U V).1
    change U = P ⊔ (U ⊓ Vᗮ) ∧ Disjoint P (U ⊓ Vᗮ)
    rw [← he]
    refine ⟨le_antisymm ?_ (sup_le hP inf_le_left),
      P.isCompl_orthogonal.disjoint.mono_right inf_le_right⟩
    intro x hx
    refine Submodule.mem_sup.mpr ⟨P.starProjection x, P.starProjection_apply_mem x,
      x - P.starProjection x, ⟨U.sub_mem hx (hP (P.starProjection_apply_mem x)),
        P.sub_starProjection_mem_orthogonal x⟩, add_sub_cancel _ _⟩
  exact ⟨h L M, h M L⟩

/-- **Exercise 66(e–g)** of [benIsrael2003generalized], Chapter 6.
The projected and unpaired directions have the stated orthogonalities. -/
theorem exercise_6_66_orthogonal (L M : Submodule 𝕜 E) :
    (L.map M.starProjection.toLinearMap ⟂ L ⊓ Mᗮ) ∧
    (M.map L.starProjection.toLinearMap ⟂ M ⊓ Lᗮ) ∧
    (L ⊓ Mᗮ ⟂ M ⊓ Lᗮ) := by
  have hL : M.map L.starProjection.toLinearMap ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact L.starProjection_apply_mem x
  have hM : L.map M.starProjection.toLinearMap ≤ M := by
    rintro _ ⟨x, -, rfl⟩
    exact M.starProjection_apply_mem x
  refine ⟨Submodule.isOrtho_comm.mp (Submodule.isOrtho_iff_le.mpr ?_),
    Submodule.isOrtho_comm.mp (Submodule.isOrtho_iff_le.mpr ?_), Submodule.isOrtho_iff_le.mpr ?_⟩
  · exact inf_le_right.trans (Submodule.orthogonal_le hM)
  · exact inf_le_right.trans (Submodule.orthogonal_le hL)
  · exact inf_le_right.trans (Submodule.orthogonal_le inf_le_left)

section Angles

variable (L M : Submodule 𝕜 E)

/-- **Definition 3** of [benIsrael2003generalized], Chapter 6.
The ordered principal angles have cosines equal to the singular values
of the restricted orthogonal projection, padded by right angles. -/
noncomputable def principalAngle (i : ℕ) : ℝ := L.principalAngle M i

/-- The principal angles increase and lie in the closed first quadrant. -/
theorem principalAngle_order : Monotone (principalAngle L M) ∧
    ∀ i, principalAngle L M i ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨L.monotone_principalAngle M, L.principalAngle_mem_Icc M⟩

/-- **Theorem 10** of [benIsrael2003generalized], Chapter 6, Equations
(110a)–(110b). The principal cosine is the maximum inner product of
unit pairs orthogonal to the preceding principal vectors. -/
theorem theorem_6_10 {q : ℕ} {f g : Fin q → E} (h : L.IsPrincipalVectors M f g) (k : Fin q) :
    IsGreatest {r : ℝ | ∃ u ∈ L, ∃ v ∈ M, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      (∀ i < k, inner 𝕜 (f i) u = 0) ∧ (∀ i < k, inner 𝕜 (g i) v = 0) ∧
        RCLike.re (inner 𝕜 u v) = r} (Real.cos (principalAngle L M k)) := by
  rw [principalAngle, Submodule.principalAngle, Real.cos_arccos
    ((by norm_num : (-1 : ℝ) ≤ 0).trans (L.cosPrincipalAngle_nonneg M k))
    (L.cosPrincipalAngle_le_one M k)]
  exact h.isGreatest_re_inner k

/-- **Lemma 2**, intersection multiplicity, of [benIsrael2003generalized],
Chapter 6. The number of unit principal cosines is the dimension of
the intersection. -/
theorem lemma_6_2_intersection (h : finrank 𝕜 M ≤ finrank 𝕜 L) :
    finrank 𝕜 (L ⊓ M : Submodule 𝕜 E) =
      (Finset.univ.filter fun i : Fin (finrank 𝕜 M) => L.cosPrincipalAngle M i = 1).card :=
  L.finrank_inf_eq_card M h

/-- **Definition 4** of [benIsrael2003generalized], Chapter 6, Equation
(112a). The distance between subspaces is the operator norm of the
difference of their orthogonal projections. -/
noncomputable def subspaceDistance : ℝ := L.gap M

/-- **Lemma 3** of [benIsrael2003generalized], Chapter 6, Equation (113).
For equal positive dimensions the projection distance is the sine of
the last principal angle, including a right angle if its cosine is zero. -/
theorem lemma_6_3 {q : ℕ} (hL : finrank 𝕜 L = q + 1) (hM : finrank 𝕜 M = q + 1) :
    subspaceDistance L M = Real.sin (principalAngle L M q) :=
  L.gap_eq_sin_principalAngle M hL hM

/-- For unequal dimensions the projection distance is one. -/
theorem subspaceDistance_eq_one_of_finrank_ne (h : finrank 𝕜 L ≠ finrank 𝕜 M) :
    subspaceDistance L M = 1 :=
  le_antisymm (L.gap_le_one M) (le_of_not_gt fun hlt => h (L.finrank_eq_of_gap_lt_one M hlt))

/-- **Exercise 67** of [benIsrael2003generalized], Chapter 6.
The subspace distance is at most one. -/
theorem exercise_6_67 : subspaceDistance L M ≤ 1 := L.gap_le_one M

/-- **Exercise 68** of [benIsrael2003generalized], Chapter 6.
Distance strictly below one is equivalent to total inclination, which
is equivalent to both dimensions equaling the inclination dimension. -/
theorem exercise_6_68 :
    (subspaceDistance L M < 1 ↔ TotallyInclined L M) ∧
    (TotallyInclined L M ↔
      finrank 𝕜 L = inclinationDimension L M ∧ finrank 𝕜 M = inclinationDimension L M) := by
  obtain ⟨⟨hL, hLd⟩, ⟨hM, hMd⟩⟩ := exercise_6_66_split L M
  obtain ⟨hP, hQ⟩ := projectedSubspaces_finrank L M
  have hl := Submodule.finrank_sup_add_finrank_inf_eq
    (M.map L.starProjection.toLinearMap) (L ⊓ Mᗮ)
  have hm := Submodule.finrank_sup_add_finrank_inf_eq
    (L.map M.starProjection.toLinearMap) (M ⊓ Lᗮ)
  rw [hLd.eq_bot, finrank_bot, add_zero, ← hL, hP] at hl
  rw [hMd.eq_bot, finrank_bot, add_zero, ← hM, hQ] at hm
  have hDim : TotallyInclined L M ↔
      finrank 𝕜 L = inclinationDimension L M ∧ finrank 𝕜 M = inclinationDimension L M := by
    simp only [TotallyInclined, CompletelyInclined, ← Submodule.finrank_eq_zero]
    omega
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, hDim⟩
  · constructor
    · by_contra hne
      exact (ne_of_lt h) (L.gap_eq_one_of_inf_orthogonal_ne_bot M hne)
    · by_contra hne
      exact (ne_of_lt h) ((L.gap_comm M).trans (M.gap_eq_one_of_inf_orthogonal_ne_bot L hne))
  · obtain ⟨hl, hm⟩ := hDim.mp h
    exact lt_of_le_of_ne (L.gap_le_one M)
      (fun he => (L.gap_eq_one_iff_of_finrank_eq M (hl.trans hm.symm)).mp he h.1)

/-- **Exercise 69** of [benIsrael2003generalized], Chapter 6.
The subspace distance is zero exactly when the subspaces coincide. -/
theorem exercise_6_69 : subspaceDistance L M = 0 ↔ L = M := L.gap_eq_zero_iff M

/-- **Equation (115a)** of [benIsrael2003generalized], Chapter 6.
The product of principal sines includes common and padded directions. -/
noncomputable def principalSineProduct : ℝ :=
  ∏ i ∈ Finset.range (min (finrank 𝕜 L) (finrank 𝕜 M)), Real.sin (principalAngle L M i)

/-- **Equation (115b)** of [benIsrael2003generalized], Chapter 6.
The product of principal cosines includes any zero cosines up to the
smaller dimension. -/
noncomputable def principalCosineProduct : ℝ :=
  ∏ i ∈ Finset.range (min (finrank 𝕜 L) (finrank 𝕜 M)), L.cosPrincipalAngle M i

end Angles

end Inclination

section CrossGram

open Matrix

/-- **Lemma 2** of [benIsrael2003generalized], Chapter 6, Equation (111).
The singular values of the cross Gram matrix of orthonormal bases
are the corresponding principal cosines. -/
theorem lemma_6_2 {𝕜 m p q : Type*} [RCLike 𝕜] [Fintype m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {Q : Matrix m p 𝕜} {Z : Matrix m q 𝕜} (hQ : Qᴴ * Q = 1) (hZ : Zᴴ * Z = 1) (i : ℕ) :
    (toEuclideanLin Q).range.cosPrincipalAngle (toEuclideanLin Z).range i =
      (Qᴴ * Z).sortedSingularValues i :=
  Submodule.cosPrincipalAngle_eq_singularValues hQ hZ i

end CrossGram

section Volume

open Matrix Chapter00

private theorem abs_det_eq_prod_sortedSingularValues {r : ℕ} (D : Matrix (Fin r) (Fin r) ℝ) :
    |D.det| = ∏ i : Fin r, D.sortedSingularValues i := by
  obtain ⟨U, hU, V, hV, h⟩ := D.exists_svd
  have hU' : |U.det| = 1 := by simpa only [Real.norm_eq_abs] using norm_det_of_mem_unitaryGroup hU
  have hV' : |V.det| = 1 := by simpa only [Real.norm_eq_abs] using norm_det_of_mem_unitaryGroup hV
  have he : D = U * diagonal (fun i : Fin r => D.sortedSingularValues i) * Vᵀ := by
    have hD := eq_mul_mul_star_of_star_mul_mul_eq hU hV h
    simpa only [rectDiagonal_eq_diagonal, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] using hD
  conv_lhs => rw [he, det_mul, det_mul, det_transpose, det_diagonal, abs_mul, abs_mul, hU',
    hV', one_mul, mul_one]
  exact abs_of_nonneg (Finset.prod_nonneg fun i _ => D.sortedSingularValues_nonneg i)

private theorem volume_rank_factor {m r : ℕ} (B : Matrix (Fin m) (Fin r) ℝ)
    (hB : B.rank = r) (hr : r ≠ 0) :
    ∃ Q : Matrix (Fin m) (Fin r) ℝ, ∃ R : Matrix (Fin r) (Fin r) ℝ,
      Qᵀ * Q = 1 ∧ B = Q * R ∧ IsUnit R ∧
      (toEuclideanLin B).range = (toEuclideanLin Q).range ∧ matrixVolume B = |R.det| := by
  have hmr : r ≤ m := hB ▸ B.rank_le_height
  obtain ⟨Q, hQ, V, -, h⟩ := B.exists_thin_svd hmr
  let R := diagonal (fun i : Fin r => B.sortedSingularValues i) * Vᵀ
  have hEQ : B = Q * R := by
    simpa only [R, ← Matrix.mul_assoc, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] using h
  have hRrank : r ≤ R.rank := by
    have hle := rank_mul_le_right Q R
    rwa [← hEQ, hB] at hle
  have hR : IsUnit R :=
    isUnit_of_rank_eq_card (by rw [Fintype.card_fin]; exact le_antisymm R.rank_le_width hRrank)
  have hInv := mul_nonsing_inv R ((isUnit_iff_isUnit_det R).mp hR)
  have hRange : (toEuclideanLin R).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro x
    refine ⟨toEuclideanLin R⁻¹ x, ?_⟩
    rw [← toEuclideanLin_mul_apply, hInv, toEuclideanLin_one, LinearMap.id_apply]
  have hQt : Qᵀ * Q = 1 := hQ
  refine ⟨Q, R, hQt, hEQ, hR, ?_, ?_⟩
  · rw [hEQ, toEuclideanLin_mul, LinearMap.range_comp_of_range_eq_top _ hRange]
  · have hGram : Bᵀ * B = Rᵀ * R := by
      calc
        Bᵀ * B = (Q * R)ᵀ * (Q * R) := congrArg (fun M => Mᵀ * M) hEQ
        _ = Rᵀ * (Qᵀ * Q) * R := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQt, Matrix.mul_one]
    have hs := matrixVolume_sq_eq_det_transpose_mul B hB hr
    rw [hGram, det_mul, det_transpose, ← pow_two, ← sq_abs R.det] at hs
    have hNonneg : 0 ≤ matrixVolume B := by
      rw [matrixVolume_eq_sqrt_sum_minors B hB hr]
      exact Real.sqrt_nonneg _
    exact (sq_eq_sq₀ hNonneg (abs_nonneg _)).mp hs

private theorem kVolume_fullColumn_sq {m r : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (hr : r ≠ 0) : kVolume r A ^ 2 = (Aᵀ * A).det := by
  by_cases hA : A.rank = r
  · rw [kVolume_eq_matrixVolume A hA hr, matrixVolume_sq_eq_det_transpose_mul A hA hr]
  · have hlt : A.rank < r := lt_of_le_of_ne A.rank_le_width hA
    rw [kVolume, ite_eq_left (Or.inr hlt), zero_pow (by decide : (2 : ℕ) ≠ 0)]
    symm
    by_contra hn
    have hU : IsUnit (Aᵀ * A) := (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
    have hR := rank_of_isUnit _ hU
    rw [← conjTranspose_eq_transpose_of_trivial, rank_conjTranspose_mul_self, Fintype.card_fin]
      at hR
    exact hA hR

private theorem det_one_sub_transpose_mul {p q : ℕ} (X : Matrix (Fin p) (Fin q) ℝ) :
    (1 - Xᵀ * X).det = ∏ i ∈ Finset.range (min p q), (1 - X.sortedSingularValues i ^ 2) := by
  let V := X.rightSingularUnitary
  let D := diagonal (fun i => X.colSingularValues i ^ 2)
  have h2 : V * Vᵀ = 1 := X.rightSingularUnitary_mul_star
  have hGram : Xᵀ * X = V * D * Vᵀ := X.conjTranspose_mul_self_eq_conj_diagonal
  have hSub : 1 - Xᵀ * X = V * (1 - D) * Vᵀ := by
    rw [hGram, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, h2]
  have hDet : (1 - Xᵀ * X).det = (1 - D).det := by
    rw [hSub, det_mul, det_mul, ← mul_right_comm, ← det_mul, h2, det_one, one_mul]
  have hD : (1 - D).det = ∏ i, (1 - X.colSingularValues i ^ 2) := by
    dsimp only [D]
    rw [← diagonal_one, diagonal_sub, det_diagonal]
  obtain ⟨e, he⟩ := X.exists_equiv_colSingularValues_eq_sortedSingularValues
  rw [hDet, hD, ← e.prod_comp]
  calc
    _ = ∏ i : Fin (Fintype.card (Fin q)), (1 - X.sortedSingularValues i ^ 2) := by
      simp only [he]
    _ = ∏ i ∈ Finset.range q, (1 - X.sortedSingularValues i ^ 2) := by
      rw [Fin.prod_univ_eq_prod_range (fun i => 1 - X.sortedSingularValues i ^ 2),
        Fintype.card_fin]
    _ = _ := by
      symm
      refine Finset.prod_subset (Finset.range_subset_range.mpr (min_le_right p q)) ?_
      intro i _ hi
      have he := X.sortedSingularValues_eq_zero_iff_rank_le i
      have hr : X.rank ≤ min p q := le_min X.rank_le_height X.rank_le_width
      simp only [he.mpr (hr.trans (Nat.le_of_not_gt fun hh => hi (Finset.mem_range.mpr hh))),
        zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]

/-- **Lemma 4** of [benIsrael2003generalized], Chapter 6, Equation (117).
The full-column degree volume of a column concatenation is the product
of the block volumes and the sines of their principal angles. -/
theorem lemma_6_4 {m p q : ℕ} (B : Matrix (Fin m) (Fin p) ℝ) (C : Matrix (Fin m) (Fin q) ℝ)
    (hB : B.rank = p) (hC : C.rank = q) (hp : p ≠ 0) (hq : q ≠ 0) :
    kVolume (p + q) ((fromCols B C).submatrix id finSumFinEquiv.symm) =
      matrixVolume B * matrixVolume C *
        principalSineProduct (toEuclideanLin B).range (toEuclideanLin C).range := by
  obtain ⟨Q, R, hQ, hBQ, -, hBr, hBv⟩ := volume_rank_factor B hB hp
  obtain ⟨Z, S, hZ, hCZ, -, hCr, hCv⟩ := volume_rank_factor C hC hq
  let A := (fromCols B C).submatrix id finSumFinEquiv.symm
  let X := Qᵀ * Z
  let D := fromBlocks R (0 : Matrix (Fin p) (Fin q) ℝ) 0 S
  let F := fromCols Q Z
  have hF : (fromCols B C) = F * D := by
    simp only [F, D, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add, ← hBQ, ← hCZ]
  have hG : Fᵀ * F = fromBlocks 1 X Xᵀ 1 := by
    change (fromCols Q Z)ᵀ * fromCols Q Z = _
    rw [transpose_fromCols, fromRows_mul_fromCols, hQ, hZ]
    have hX : Xᵀ = Zᵀ * Q := by simp only [X, transpose_mul, transpose_transpose]
    rw [hX]
  have hGramDet : (Fᵀ * F).det = (1 - Xᵀ * X).det := by
    rw [hG, det_fromBlocks_eq_det_mul_schurComplement _ _ _ _ isUnit_one,
      det_one, one_mul, Chapter00.schurComplement, inv_one, Matrix.mul_one]
  have hD : D.det = R.det * S.det := det_fromBlocks_zero₂₁ _ _ _
  have he : (Aᵀ * A).det = ((fromCols B C)ᵀ * fromCols B C).det := by
    dsimp only [A]
    rw [transpose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id]
    exact det_submatrix_equiv_self finSumFinEquiv.symm _
  have hs := kVolume_fullColumn_sq A (by omega : p + q ≠ 0)
  rw [he, hF, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᵀ F,
    ← Matrix.mul_assoc Dᵀ, det_mul, det_mul, det_transpose, hD, hGramDet,
    det_one_sub_transpose_mul] at hs
  have hSin : principalSineProduct (toEuclideanLin B).range (toEuclideanLin C).range ^ 2 =
      ∏ i ∈ Finset.range (min p q), (1 - X.sortedSingularValues i ^ 2) := by
    unfold principalSineProduct
    rw [finrank_range_toEuclideanLin, finrank_range_toEuclideanLin, hB, hC, hBr, hCr,
      ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [principalAngle, Submodule.principalAngle, Real.sin_arccos, Real.sq_sqrt]
    · rw [lemma_6_2 hQ hZ i, conjTranspose_eq_transpose_of_trivial]
    · have h₀ := (toEuclideanLin Q).range.cosPrincipalAngle_nonneg (toEuclideanLin Z).range i
      have h₁ := (toEuclideanLin Q).range.cosPrincipalAngle_le_one (toEuclideanLin Z).range i
      nlinarith
  have hSin₀ : 0 ≤ principalSineProduct (toEuclideanLin B).range (toEuclideanLin C).range := by
    apply Finset.prod_nonneg
    intro i _
    have ha := (principalAngle_order (toEuclideanLin B).range (toEuclideanLin C).range).2 i
    exact Real.sin_nonneg_of_nonneg_of_le_pi ha.1 (ha.2.trans (by linarith [Real.pi_pos]))
  have hVol : 0 ≤ kVolume (p + q) A := by
    unfold kVolume
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  apply (sq_eq_sq₀ hVol (mul_nonneg (mul_nonneg (hBv ▸ abs_nonneg _) (hCv ▸ abs_nonneg _))
    hSin₀)).mp
  rw [mul_pow, mul_pow, hBv, hCv, sq_abs, sq_abs, hSin, hs]
  ring

private theorem rankFactor_left_range {m n p : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {F : Matrix (Fin m) (Fin p) ℝ} {G : Matrix (Fin p) (Fin n) ℝ}
    (h : IsRankFactorization A F G) :
    (toEuclideanLin A).range = (toEuclideanLin F).range := by
  apply Submodule.eq_of_le_of_finrank_le
  · rw [h.eq_mul, toEuclideanLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rw [finrank_range_toEuclideanLin, finrank_range_toEuclideanLin, h.rank_eq, h.rank_left]

/-- **Theorem 11** of [benIsrael2003generalized], Chapter 6, Equation (118).
If the two positive-rank column spaces form a direct sum, the concatenated
volume is the product of the block volumes and their principal sines. -/
theorem theorem_6_11 {m n₁ n₂ p q : ℕ} (B : Matrix (Fin m) (Fin n₁) ℝ)
    (C : Matrix (Fin m) (Fin n₂) ℝ)
    (hB : B.rank = p) (hC : C.rank = q) (hp : p ≠ 0) (hq : q ≠ 0)
    (ha : ((fromCols B C).submatrix id finSumFinEquiv.symm).rank = p + q) :
    matrixVolume ((fromCols B C).submatrix id finSumFinEquiv.symm) =
      matrixVolume B * matrixVolume C *
        principalSineProduct (toEuclideanLin B).range (toEuclideanLin C).range := by
  obtain ⟨F₁, G₁, h₁⟩ : ∃ (F₁ : Matrix (Fin m) (Fin p) ℝ)
      (G₁ : Matrix (Fin p) (Fin n₁) ℝ),
      IsRankFactorization B F₁ G₁ := by
    rw [← hB]
    exact Chapter00.lemma_1 B
  obtain ⟨F₂, G₂, h₂⟩ : ∃ (F₂ : Matrix (Fin m) (Fin q) ℝ)
      (G₂ : Matrix (Fin q) (Fin n₂) ℝ),
      IsRankFactorization C F₂ G₂ := by
    rw [← hC]
    exact Chapter00.lemma_1 C
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  let f : Fin (n₁ + n₂) ≃ Fin n₁ ⊕ Fin n₂ := finSumFinEquiv.symm
  let A := (fromCols B C).submatrix id f
  let F := (fromCols F₁ F₂).submatrix id e
  let D : Matrix (Fin p ⊕ Fin q) (Fin n₁ ⊕ Fin n₂) ℝ := fromBlocks G₁ 0 0 G₂
  let G := D.submatrix e f
  have h1F : F₁.rank = p := h₁.rank_left.trans (Fintype.card_fin _)
  have h2F : F₂.rank = q := h₂.rank_left.trans (Fintype.card_fin _)
  have h1G : G₁.rank = p := h₁.rank_right.trans (Fintype.card_fin _)
  have h2G : G₂.rank = q := h₂.rank_right.trans (Fintype.card_fin _)
  have hrA : A.rank = p + q := ha
  have hEq : A = F * G := by
    change (fromCols B C).submatrix id f = (fromCols F₁ F₂).submatrix id e * D.submatrix e f
    rw [submatrix_mul_equiv]
    exact congrArg (fun X : Matrix (Fin m) (Fin n₁ ⊕ Fin n₂) ℝ => X.submatrix id f)
      (by simp only [D, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add,
        ← h₁.eq_mul, ← h₂.eq_mul])
  have hrF : F.rank = p + q := by
    apply le_antisymm F.rank_le_width
    have hl := rank_mul_le_left F G
    rwa [← hEq, hrA] at hl
  have hrG : G.rank = p + q := by
    change (D.submatrix (⇑e) (⇑f)).rank = _
    rw [rank_submatrix, show D.rank = G₁.rank + G₂.rank from rank_fromBlocks_diagonal G₁ G₂,
      h1G, h2G]
  have hAF : IsRankFactorization A F G := ⟨hEq,
    hrA.trans (Fintype.card_fin _).symm, hrF.trans (Fintype.card_fin _).symm,
    hrG.trans (Fintype.card_fin _).symm⟩
  have hFvol : matrixVolume F = matrixVolume F₁ * matrixVolume F₂ *
      principalSineProduct (toEuclideanLin B).range (toEuclideanLin C).range := by
    have hh := lemma_6_4 F₁ F₂ h1F h2F hp hq
    change kVolume (p + q) F = _ at hh
    rwa [kVolume_eq_matrixVolume F hrF (by omega), ← rankFactor_left_range h₁,
      ← rankFactor_left_range h₂] at hh
  have hGvol : matrixVolume G = matrixVolume G₁ * matrixVolume G₂ := by
    have hGram : (G * Gᵀ).det = (D * Dᵀ).det := by
      change (D.submatrix e f * (D.submatrix e f)ᵀ).det = _
      rw [transpose_submatrix, submatrix_mul_equiv]
      exact det_submatrix_equiv_self e _
    have hBlock : (D * Dᵀ).det = (G₁ * G₁ᵀ).det * (G₂ * G₂ᵀ).det := by
      dsimp only [D]
      rw [fromBlocks_transpose, transpose_zero, transpose_zero, fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
      exact det_fromBlocks_zero₂₁ _ _ _
    have hs := matrixVolume_sq_eq_det_mul_transpose G hrG (by omega)
    rw [hGram, hBlock, ← matrixVolume_sq_eq_det_mul_transpose G₁ h1G hp,
      ← matrixVolume_sq_eq_det_mul_transpose G₂ h2G hq, ← mul_pow] at hs
    exact (sq_eq_sq₀ (matrixVolume_nonneg G)
      (mul_nonneg (matrixVolume_nonneg G₁) (matrixVolume_nonneg G₂))).mp hs
  change matrixVolume A = _
  rw [matrixVolume_mul_of_rankFactorization hAF, hFvol, hGvol,
    matrixVolume_mul_of_rankFactorization h₁, matrixVolume_mul_of_rankFactorization h₂]
  ring

/-- **Theorem 12** of [benIsrael2003generalized], Chapter 6, Equation
(119). The cross determinant of full-column-rank matrices of the same
positive width is the product of their volumes and principal cosines. -/
theorem theorem_6_12 {m r : ℕ} (B C : Matrix (Fin m) (Fin r) ℝ)
    (hB : B.rank = r) (hC : C.rank = r) (hr : r ≠ 0) :
    |(Bᵀ * C).det| = matrixVolume B * matrixVolume C *
      principalCosineProduct (toEuclideanLin B).range (toEuclideanLin C).range := by
  obtain ⟨Q, R, hQ, hBQ, -, hBr, hBv⟩ := volume_rank_factor B hB hr
  obtain ⟨Z, S, hZ, hCZ, -, hCr, hCv⟩ := volume_rank_factor C hC hr
  have hGram : Bᵀ * C = Rᵀ * (Qᵀ * Z) * S := by
    rw [hBQ, hCZ, transpose_mul]
    simp only [Matrix.mul_assoc]
  have hProd : principalCosineProduct (toEuclideanLin B).range (toEuclideanLin C).range =
      ∏ i : Fin r, (Qᵀ * Z).sortedSingularValues i := by
    unfold principalCosineProduct
    rw [finrank_range_toEuclideanLin, finrank_range_toEuclideanLin, hB, hC, min_self,
      hBr, hCr]
    have he (i : ℕ) : (toEuclideanLin Q).range.cosPrincipalAngle (toEuclideanLin Z).range i =
        (Qᵀ * Z).sortedSingularValues i := lemma_6_2 hQ hZ i
    simp only [he, Fin.prod_univ_eq_prod_range]
  rw [hGram, det_mul, det_mul, det_transpose, abs_mul, abs_mul, hBv, hCv, hProd,
    abs_det_eq_prod_sortedSingularValues (Qᵀ * Z)]
  ring

end Volume

end BenIsraelGreville.Chapter06
