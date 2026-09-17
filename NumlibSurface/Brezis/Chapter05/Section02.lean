import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint

/-!
# Brezis §5.2: the dual space of a Hilbert space

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §5.2, over a real Hilbert space `H`. The Riesz–Fréchet
theorem is Mathlib's isometry `InnerProductSpace.toDual ℝ H : H ≃ₗᵢ⋆[ℝ] StrongDual ℝ H`; Remark 3,
the pivot-space triple `V ⊂ H ⊂ V*`, is stated with chapter 2's Banach adjoint
`ContinuousLinearMap.strongDualMap` (the restriction of functionals along the injection
`i : V → H`); Remark 5 identifies the book's two readings of `M^⊥` — as a subspace of `H*`
(chapter 1's `Submodule.strongDualAnnihilator`) and as a subspace of `H` (Mathlib's
`Submodule.orthogonal`, `Mᗮ`) — through `toDual`.

## Main results

* `theorem_5_5` — the Riesz–Fréchet representation theorem: every `φ ∈ H*` is `u ↦ (f, u)` for a
  unique `f ∈ H`, and `|f| = ‖φ‖`.
* `remark_5_3`, `remark_5_3_pairing` — the triple `V ⊂ H ⊂ V*`: the restriction map
  `T : H* → V*` is bounded by the norm of the injection, injective, has dense range when `V` is
  reflexive, and `⟨T f, v⟩ = (f, v)` for `f ∈ H` identified with `H*`.
* `remark_5_4` — Hilbert spaces are reflexive, by the Riesz–Fréchet isomorphism used twice.
* `remark_5_5`, `remark_5_5_annihilator` — `M ∩ M^⊥ = {0}`, `M + M^⊥ = H` for closed `M`,
  `f - P_M f = P_{M^⊥} f`, every closed subspace is complemented; and the annihilator of §1.3 is
  carried onto `Mᗮ` by the Riesz isometry.

The weighted-`ℓ²` example inside Remark 3 is not stated.
-/

open InnerProductSpace NormedSpace
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Theorem 5.5 (Riesz–Fréchet representation theorem).** Given any `φ ∈ H*` there is a unique
`f ∈ H` with `⟨φ, u⟩ = (f, u)` for all `u ∈ H`; moreover `|f| = ‖φ‖`. The representative is
`(InnerProductSpace.toDual ℝ H).symm φ`. -/
theorem theorem_5_5 (φ : StrongDual ℝ H) :
    ∃! f : H, (∀ u, φ u = ⟪f, u⟫_ℝ) ∧ ‖f‖ = ‖φ‖ := by
  refine ⟨(toDual ℝ H).symm φ, ⟨fun u => ?_, ?_⟩, ?_⟩
  · rw [toDual_symm_apply]
  · exact LinearIsometryEquiv.norm_map _ _
  · rintro g ⟨hg, -⟩
    apply (toDual ℝ H).injective
    ext u
    rw [toDual_apply_apply, ← hg, LinearIsometryEquiv.apply_symm_apply]

/-! ### Remark 3: the triple `V ⊂ H ⊂ V*` -/

section Pivot

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace H] [CompleteSpace V] in
/-- **Remark 3, the triple `V ⊂ H ⊂ V*` with `H` as pivot space.** For a Banach space `V`
continuously and densely injected into `H` by `i : V →L[ℝ] H` (the book's `V ⊂ H` with
`|v| ≤ C ‖v‖`, `C = ‖i‖`), the canonical map `T : H* → V*`, `⟨T φ, v⟩ = ⟨φ, i v⟩` — the
restriction of functionals to `V`, chapter 2's `i.strongDualMap` — satisfies
(i) `‖T φ‖ ≤ ‖i‖ ‖φ‖`, (ii) `T` is injective, (iii) `R(T)` is dense in `V*` if `V` is reflexive.
The footnote — `T` is not surjective in general — is not stated. Neither completeness is used:
reflexivity of `V` is the hypothesis of (iii), and `H` enters only through its dual. -/
theorem remark_5_3 (i : V →L[ℝ] H) (hi : Function.Injective i) (hd : DenseRange i) :
    (∀ φ : StrongDual ℝ H, ‖i.strongDualMap φ‖ ≤ ‖i‖ * ‖φ‖) ∧
      Function.Injective i.strongDualMap ∧
      (IsReflexive ℝ V → DenseRange i.strongDualMap) := by
  refine ⟨fun φ => ?_, ?_, fun hV => ?_⟩
  · -- (i): `‖T‖ = ‖i‖`
    calc ‖i.strongDualMap φ‖ ≤ ‖i.strongDualMap‖ * ‖φ‖ := i.strongDualMap.le_opNorm φ
      _ = ‖i‖ * ‖φ‖ := by rw [ContinuousLinearMap.opNorm_strongDualMap]
  · -- (ii): a functional vanishing on the dense range of `i` vanishes
    refine (injective_iff_map_eq_zero _).2 fun φ hφ => ?_
    have h : (⇑φ : H → ℝ) = ⇑(0 : StrongDual ℝ H) :=
      hd.equalizer φ.continuous continuous_const (funext fun v => by
        have := congrArg (fun ψ : StrongDual ℝ V => ψ v) hφ
        simpa [ContinuousLinearMap.strongDualMap_apply] using this)
    exact DFunLike.coe_injective h
  · -- (iii): a functional on `V*` vanishing on `R(T)` is `J v` with `i v = 0`
    by_contra hnot
    rw [denseRange_iff_closure_range] at hnot
    obtain ⟨ψ, hψ⟩ : ∃ ψ : StrongDual ℝ V, ψ ∉ closure (Set.range i.strongDualMap) := by
      by_contra h
      exact hnot (Set.eq_univ_of_forall fun ψ => not_not.1 fun h' => h ⟨ψ, h'⟩)
    set N : Submodule ℝ (StrongDual ℝ V) :=
      (LinearMap.range (i.strongDualMap : StrongDual ℝ H →ₗ[ℝ] StrongDual ℝ V)).topologicalClosure
      with hN
    have hNcl : IsClosed (N : Set (StrongDual ℝ V)) := Submodule.isClosed_topologicalClosure _
    have hψN : ψ ∉ N := by
      rw [hN, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range]
      exact hψ
    obtain ⟨ξ, hξ1, hξN, hξψ⟩ := N.exists_dual_eq_zero_of_notMem hNcl hψN
    obtain ⟨v, rfl⟩ := hV.surjective_inclusionInDoubleDual ξ
    have hv : i v = 0 := by
      refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun φ => ?_
      have := hξN (i.strongDualMap φ) (Submodule.le_topologicalClosure _ ⟨φ, rfl⟩)
      rwa [dual_def, ContinuousLinearMap.strongDualMap_apply] at this
    have hv0 : v = 0 := hi (by rw [hv, map_zero])
    rw [hv0, map_zero] at hξ1
    simp at hξ1

omit [CompleteSpace V] in
/-- **Remark 3, the identification of the pairings**: `⟨f, v⟩_{V*, V} = (f, v)` for `f ∈ H` and
`v ∈ V`, where `f ∈ H` is read in `H*` by Riesz–Fréchet and then in `V*` by `T`. -/
theorem remark_5_3_pairing (i : V →L[ℝ] H) (f : H) (v : V) :
    i.strongDualMap (toDual ℝ H f) v = ⟪f, i v⟫_ℝ := by
  rw [ContinuousLinearMap.strongDualMap_apply, toDual_apply_apply]

end Pivot

/-- **Remark 4.** Hilbert spaces are reflexive, without the theory of uniformly convex spaces:
the backbone instance `NormedSpace.instIsReflexiveOfInnerProductSpace` is the Riesz–Fréchet
isomorphism used twice, from `H` onto `H*` and then from `H*` onto `H**`. -/
theorem remark_5_4 : IsReflexive ℝ H := inferInstance

/-- **Remark 5, the orthogonal complement in `H`.** For a closed subspace `M` and `f ∈ H`:
`M ∩ M^⊥ = {0}`, `M + M^⊥ = H`, `f - P_M f = P_{M^⊥} f`, and `M` has a complement in the sense
of §2.4 (`M.ClosedComplemented`). -/
theorem remark_5_5 (M : Submodule ℝ H) (hM : IsClosed (M : Set H)) (f : H) :
    M ⊓ Mᗮ = ⊥ ∧ M ⊔ Mᗮ = ⊤ ∧
      (haveI := hM.completeSpace_coe; f - M.starProjection f = Mᗮ.starProjection f) ∧
      M.ClosedComplemented := by
  have := hM.completeSpace_coe
  exact ⟨M.inf_orthogonal_eq_bot, Submodule.sup_orthogonal_of_hasOrthogonalProjection,
    (M.starProjection_orthogonal_val f).symm, M.isTopCompl_orthogonal.closedComplemented⟩

/-- **Remark 5, first sentence.** The annihilator `M^⊥ ⊆ H*` of §1.3 "may now be considered as a
subspace of `H`": under the Riesz isometry, `φ ∈ M^⊥` (chapter 1's `M.strongDualAnnihilator`)
exactly when its representative lies in `Mᗮ = {u ∈ H | (u, v) = 0 ∀ v ∈ M}`. -/
theorem remark_5_5_annihilator (M : Submodule ℝ H) (φ : StrongDual ℝ H) :
    φ ∈ M.strongDualAnnihilator ↔ (toDual ℝ H).symm φ ∈ Mᗮ := by
  rw [Submodule.mem_strongDualAnnihilator, Submodule.mem_orthogonal]
  refine forall₂_congr fun u _ => ?_
  rw [real_inner_comm, toDual_symm_apply]

end Brezis.Chapter05

end
