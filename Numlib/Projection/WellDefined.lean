/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Projection.Basic
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Complementary subspaces in projection methods

For a linear operator $A$ with trial space $S$ and test space $C$, the projected system
is invertible exactly when $AS$ and $C^\perp$ are complementary, provided $S$ and $C$ have
equal finite dimensions. The complementarity condition also gives a residual decomposition
for every initial residual.

## Main results

* `isUnit_crossGram_map_iff_isCompl` gives the projected matrix criterion.
* `existsUnique_isPetrovGalerkin_of_isCompl` gives the unique iterate by projection onto $AS$.
* `isCompl_map_orthogonal_of_isCoercive` gives complementarity for coercive $A$ and $C=S$.
* `isCompl_map_orthogonal_comap_of_isSymmetric` gives complementarity for invertible
  symmetric $A$ and $C=A^{-1}S$.
-/

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- If $AS$ and $C^\perp$ are complementary and $A$ is injective on $S$, the Petrov–Galerkin
problem on $x_0+S$ with constraint space $C$ has a unique solution for every $b$. -/
theorem existsUnique_isPetrovGalerkin_of_isCompl {A : E →ₗ[𝕜] F} {S : Submodule 𝕜 E}
    {C : Submodule 𝕜 F} (h : IsCompl (S.map A) Cᗮ) (hA : Set.InjOn A S) (b : F) (x₀ : E) :
    ∃! x, IsPetrovGalerkin A b x₀ S C x := by
  let P := (S.map A).projection Cᗮ h
  obtain ⟨z, hz, hAz⟩ := Submodule.mem_map.1 (Submodule.projection_apply_mem h (b - A x₀))
  have hPG : IsPetrovGalerkin A b x₀ S C (x₀ + z) := by
    refine ⟨by simpa using hz, ?_⟩
    rw [residual_eq_sub_apply_sub, add_sub_cancel_left, hAz]
    exact Submodule.sub_projection_mem h _
  refine ⟨x₀ + z, hPG, fun x hx => hx.eq_of_forall hPG ?_⟩
  intro δ hδ hAδ
  have hzero : A δ = 0 := by
    have hm : A δ ∈ S.map A ⊓ Cᗮ := ⟨Submodule.mem_map_of_mem hδ, hAδ⟩
    rwa [h.disjoint.eq_bot, Submodule.mem_bot] at hm
  exact hA hδ S.zero_mem (hzero.trans (map_zero A).symm)

/-- The projected matrix $C^*AS$ for two bases indexed by the same finite type is invertible
if and only if the image of the trial space and the orthogonal complement of the test space
are complementary. -/
theorem isUnit_crossGram_map_iff_isCompl [FiniteDimensional 𝕜 F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Submodule 𝕜 E} {C : Submodule 𝕜 F}
    (A : E →ₗ[𝕜] F) (s : Module.Basis ι 𝕜 S) (c : Module.Basis ι 𝕜 C) :
    IsUnit (LinearMap.crossGram 𝕜 (fun j => A (s j)) (fun i => (c i : F))) ↔
      IsCompl (S.map A) Cᗮ := by
  let V : ι → F := fun j => A (s j)
  let W : ι → F := fun i => c i
  change IsUnit (LinearMap.crossGram 𝕜 V W) ↔ _
  constructor
  · intro h
    have hV₀ : Submodule.span 𝕜 (Set.range fun i => (s i : E)) = S := by
      change Submodule.span 𝕜 (Set.range (S.subtype ∘ s)) = S
      rw [Set.range_comp, ← Submodule.map_span, s.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    have hV : Submodule.span 𝕜 (Set.range V) = S.map A := by
      rw [← hV₀, Submodule.map_span, ← Set.range_comp]
      rfl
    have hW : Submodule.span 𝕜 (Set.range W) = C := by
      change Submodule.span 𝕜 (Set.range (C.subtype ∘ c)) = C
      rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    have hP := LinearMap.IsIdempotentElem.isCompl
      (LinearMap.obliqueProjectionOfBases_isIdempotentElem V W h)
    rwa [LinearMap.range_obliqueProjectionOfBases V W h,
      LinearMap.ker_obliqueProjectionOfBases V W h, hV, hW] at hP
  · intro h
    let : FiniteDimensional 𝕜 S := Module.Finite.of_basis s
    let f : S →ₗ[𝕜] S.map A :=
      (A.comp S.subtype).codRestrict _ fun x => Submodule.mem_map_of_mem x.2
    have hdim : Module.finrank 𝕜 (S.map A) = Module.finrank 𝕜 S := by
      have h₁ := Submodule.finrank_add_eq_of_isCompl h
      have h₂ := Submodule.finrank_add_eq_of_isCompl C.isCompl_orthogonal
      have h₃ : Module.finrank 𝕜 S = Module.finrank 𝕜 C := by
        rw [Module.finrank_eq_card_basis s, Module.finrank_eq_card_basis c]
      omega
    have hf : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).2 (by
        intro y
        obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.2
        exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩)
    let G := LinearMap.crossGram 𝕜 V W
    have hnull : ∀ y : ι → 𝕜, G.mulVec y = 0 → y = 0 := by
      intro y hy
      let z := s.equivFun.symm y
      have hz : (z : E) = ∑ j, y j • (s j : E) := by
        rw [show z = ∑ j, y j • s j from s.equivFun_symm_apply y]
        simp
      have hPG : IsPetrovGalerkin A 0 0 S C (z : E) := by
        rw [hz, ← zero_add (∑ j, y j • (s j : E)), isPetrovGalerkin_iff_mulVec s c]
        simpa [G, V, W, LinearMap.crossGram, Pi.zero_def] using hy
      have hAz : A (z : E) = 0 := by
        have hmem : A (z : E) ∈ S.map A ⊓ Cᗮ :=
          ⟨Submodule.mem_map_of_mem z.2, by simpa using Cᗮ.neg_mem hPG.orth⟩
        rwa [h.disjoint.eq_bot, Submodule.mem_bot] at hmem
      have hz0 : z = 0 := hf (Subtype.ext (by simpa [f] using hAz))
      have hcoords := congrArg s.equivFun hz0
      change s.equivFun (s.equivFun.symm y) = s.equivFun 0 at hcoords
      rwa [s.equivFun.apply_symm_apply, map_zero] at hcoords
    apply Matrix.mulVec_injective_iff_isUnit.1
    intro x y hxy
    apply sub_eq_zero.1
    exact hnull (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])

/-- For coercive $A$ on a finite-dimensional inner product space, $AS$ and $S^\perp$
are complementary. -/
theorem isCompl_map_orthogonal_of_isCoercive [FiniteDimensional 𝕜 E]
    {A : E →ₗ[𝕜] E} (hA : A.IsCoercive) (S : Submodule 𝕜 E) :
    IsCompl (S.map A) Sᗮ := by
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).2
  · rw [disjoint_iff_inf_le]
    rintro _ ⟨himg, hort⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 himg
    rw [Submodule.mem_bot, eq_zero_of_isCoercive_of_apply_mem_orthogonal S hA hz hort, map_zero]
  · rw [LinearMap.finrank_map_of_injective A hA.injective,
      Submodule.finrank_add_eq_of_isCompl S.isCompl_orthogonal]

/-- For bijective symmetric $A$ on a finite-dimensional inner product space, $AS$ and
$(A^{-1}S)^\perp$ are complementary. -/
theorem isCompl_map_orthogonal_comap_of_isSymmetric [FiniteDimensional 𝕜 E]
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hAi : Function.Bijective A)
    (S : Submodule 𝕜 E) : IsCompl (S.map A) (S.comap A)ᗮ := by
  let e := LinearEquiv.ofBijective A hAi
  have hmap : (S.comap A).map A = S := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro x hx
      obtain ⟨y, rfl⟩ := hAi.surjective x
      exact Submodule.mem_map_of_mem hx
  have hdim : Module.finrank 𝕜 (S.map A) = Module.finrank 𝕜 (S.comap A) := by
    rw [LinearMap.finrank_map_of_injective A hAi.injective,
      ← LinearMap.finrank_map_of_injective A hAi.injective (S.comap A), hmap]
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).2
  · rw [disjoint_iff_inf_le]
    rintro _ ⟨himg, hort⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 himg
    let w := e.symm z
    have hw : A w = z := e.apply_symm_apply z
    have hzero : inner 𝕜 z z = 0 := by
      have hinner := (Submodule.mem_orthogonal _ _).1 hort w
        (show A w ∈ S from hw.symm ▸ hz)
      rw [← hA, hw] at hinner
      exact hinner
    rw [Submodule.mem_bot, inner_self_eq_zero.1 hzero, map_zero]
  · rw [hdim, Submodule.finrank_add_eq_of_isCompl (S.comap A).isCompl_orthogonal]
