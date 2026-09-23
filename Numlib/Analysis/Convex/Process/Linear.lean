import Numlib.Analysis.Convex.Process.Basic

/-!
# Linear transformations inside the convex algebra

A linear transformation is a single-valued convex process, and `ConvexProcess.ofLinearMap` is that
embedding. Every operation of the convex algebra restricts along it to the corresponding operation
on linear maps: the image of a set is the linear image, composition is composition, the image of a
function under the associated bifunction is `mapLin`, and the adjoint of the process is a transpose
of the linear map.

## Implementation notes

The adjoints of a convex process, bifunction and function are defined outright from a pair of
pairings; none mentions a linear map. A transpose enters only here, as the hypothesis
`IsAdjointPair Bu Bx T T'` — between arbitrarily paired spaces a linear map need not have a
transpose at all, and when it does it is unique only if `Bu` is right-separating.

`adjointProcess` and `coadjointProcess` must be kept apart on a general process, but on a linear one
the graph is a *subspace*, so the defining inequality at `-u` reverses the one at `u` and both
collapse to `⟨T u, y⟩ = ⟨u, v⟩`. It is right-separation of `Bu`, not of `Bx`, that pins the answer:
without it the adjoint process is single-valued only up to the annihilator of `U` in `V`.

## References

* [rockafellar1970convex] §39.
-/

open Set

namespace ConvexAnalysis

namespace ConvexProcess

/-! ### The set-level dictionary -/

section Sets

variable {U X Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Z] [Module ℝ Z]

theorem image_ofLinearMap (T : U →ₗ[ℝ] X) (C : Set U) : (ofLinearMap T).image C = T '' C := by
  ext x
  constructor
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, (mem_graph_ofLinearMap.1 hx).symm⟩
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, mem_graph_ofLinearMap.2 hx.symm⟩

theorem range_ofLinearMap (T : U →ₗ[ℝ] X) : (ofLinearMap T).range = Set.range T := by
  rw [← image_univ, image_ofLinearMap, Set.image_univ]

theorem comp_ofLinearMap (S : X →ₗ[ℝ] Z) (T : U →ₗ[ℝ] X) :
    (ofLinearMap S).comp (ofLinearMap T) = ofLinearMap (S ∘ₗ T) := by
  ext p
  constructor
  · rintro ⟨x, hx, hz⟩
    exact (mem_graph_ofLinearMap.1 hz).trans (congrArg S (mem_graph_ofLinearMap.1 hx))
  · intro h
    exact ⟨T p.1, rfl, mem_graph_ofLinearMap.2 (mem_graph_ofLinearMap.1 h)⟩

theorem ofLinearMap_injective :
    Function.Injective (ofLinearMap : (U →ₗ[ℝ] X) → ConvexProcess U X) := fun T S h => by
  ext u
  have hu : (u, T u) ∈ (ofLinearMap S).graph := h ▸ mem_graph_ofLinearMap.2 rfl
  exact mem_graph_ofLinearMap.1 hu

end Sets

/-! ### The image of a function under a linear process -/

section Image

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

/-- **`Ff` at the indicator bifunction of a linear `T` is the image `mapLin T f`.** The hypothesis
that `f` is nowhere `⊥` is not a convenience: off the fibre of `T` the summand is `⊤`, and
`⊥ + ⊤ = ⊥` would drag the infimum to `⊥` at every point of `X`. -/
theorem imageBifun_indicatorBifun_ofLinearMap (T : U →ₗ[ℝ] X) {f : U → EReal}
    (hbf : ∀ u, f u ≠ ⊥) :
    imageBifun (ofLinearMap T).indicatorBifun f = mapLin T f := by
  funext x
  rw [imageBifun_apply]
  refine le_antisymm (le_mapLin fun u hu => ?_) (le_iInf fun u => ?_)
  · refine (iInf_le _ u).trans (le_of_eq ?_)
    rw [indicatorBifun_apply, eval_ofLinearMap,
      indicatorFn_of_mem (Set.mem_singleton_iff.2 hu.symm), add_zero]
  · by_cases h : T u = x
    · rw [indicatorBifun_apply, eval_ofLinearMap,
        indicatorFn_of_mem (Set.mem_singleton_iff.2 h.symm), add_zero]
      exact mapLin_le h
    · rw [indicatorBifun_apply, eval_ofLinearMap,
        indicatorFn_of_notMem fun hc => h (Set.mem_singleton_iff.1 hc).symm,
        EReal.add_top_of_ne_bot (hbf u)]
      exact le_top

end Image

/-! ### The adjoint of a linear process -/

section Adjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {T : U →ₗ[ℝ] X} {T' : Y →ₗ[ℝ] V}
  {y : Y} {v : V}

/-- On a linear process the adjoint condition is an *equation*, the graph being a subspace. -/
private theorem pairing_eq_of_forall_le (h : ∀ u : U, Bx (T u) y ≤ Bu u v) (u : U) :
    Bx (T u) y = Bu u v := by
  refine le_antisymm (h u) ?_
  have hn := h (-u)
  simp only [map_neg, LinearMap.neg_apply] at hn
  linarith

private theorem eq_of_forall_pairing_eq (hB : Bu.SeparatingRight)
    (hA : IsAdjointPair Bu Bx T T') (h : ∀ u : U, Bx (T u) y = Bu u v) : v = T' y := by
  refine sub_eq_zero.1 (hB _ fun u => ?_)
  rw [map_sub (Bu u) v (T' y), sub_eq_zero, ← hA u y, h u]

/-- **The adjoint of a linear process is a transpose of the linear map.** `Bu.SeparatingRight` is
what makes the answer unique, as it is for the transpose itself. -/
theorem adjointProcess_ofLinearMap (hB : Bu.SeparatingRight) (hA : IsAdjointPair Bu Bx T T') :
    adjointProcess Bu Bx (ofLinearMap T) = ofLinearMap T' := by
  ext q
  constructor
  · intro h
    exact eq_of_forall_pairing_eq hB hA
      (pairing_eq_of_forall_le fun u => h (u, T u) (mem_graph_ofLinearMap.2 rfl))
  · intro h p hp
    have hp' : p.2 = T p.1 := mem_graph_ofLinearMap.1 hp
    have hq : q.2 = T' q.1 := mem_graph_ofLinearMap.1 h
    rw [hp', hq, hA p.1 q.1]

/-- **The infimum-oriented adjoint of a linear process is the same transpose**: it is
`adjointProcess_ofLinearMap` at the negated pairings, for which `T'` is still a transpose. -/
theorem coadjointProcess_ofLinearMap (hB : Bu.SeparatingRight) (hA : IsAdjointPair Bu Bx T T') :
    coadjointProcess Bu Bx (ofLinearMap T) = ofLinearMap T' := by
  rw [coadjointProcess_eq_adjointProcess_neg]
  refine adjointProcess_ofLinearMap (fun v hv => hB v fun u => ?_) fun u y => ?_
  · simpa using hv u
  · simp only [LinearMap.neg_apply, hA u y]

end Adjoint

end ConvexProcess

end ConvexAnalysis
