import Numlib.Analysis.Convex.Recession.Closedness

/-!
# Sums of finitely many convex sets

A sum `C₁ + ⋯ + Cₘ` of subsets of `E` is the image of the product set `∏ Cᵢ ⊆ ι → E` under the
sum map `(xᵢ) ↦ ∑ xᵢ`, so every question about the closure and the recession cone of a finite sum
becomes a question about a linear *image*, which the recession calculus of a linear map answers.
`Convex.isClosed_sum`, `Convex.closure_sum_eq` and `Convex.recessionCone_sum` are the `m`-ary
statements: closure and recession cone both distribute over a finite sum of convex sets.

The cancellation hypothesis is genuinely `m`-ary: a sum of `m` directions of recession can vanish
without any two of them cancelling, so it is stated on the family, and the two-set results of
`Recession/Closedness.lean` are kept separately rather than derived from these.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §9.
-/

open Set

open scoped Pointwise

namespace ConvexAnalysis

section Defs

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- **The sum map** `(x₁, …, xₘ) ↦ x₁ + ⋯ + xₘ` of a finite product, as a linear map: the `m`-ary
codiagonal. -/
def piSum : (ι → E) →ₗ[ℝ] E where
  toFun x := ∑ i, x i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum]

@[simp] theorem piSum_apply (x : ι → E) : (piSum : (ι → E) →ₗ[ℝ] E) x = ∑ i, x i := rfl

/-- **A sum of finitely many sets is the image of their product under the sum map**: what turns
a question about a finite sum into a question about a linear image. -/
theorem image_piSum_univ_pi (C : ι → Set E) :
    (piSum : (ι → E) →ₗ[ℝ] E) '' univ.pi C = ∑ i, C i := by
  ext y
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, fun i => hx i (mem_univ i), rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, fun i _ => hg i, rfl⟩

end Defs

section Sum

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {C : ι → Set E}

omit [FiniteDimensional ℝ E] in
/-- The cancellation hypothesis for a family, transported to the product set. -/
theorem forall_mem_linealitySpace_pi (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (closure (C i))) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (closure (C i))) :
    ∀ p ∈ recessionCone (closure (univ.pi C)), (piSum : (ι → E) →ₗ[ℝ] E) p = 0 →
      p ∈ linealitySpace (closure (univ.pi C)) := by
  have hpine : (univ.pi fun i => closure (C i)).Nonempty :=
    Set.univ_pi_nonempty_iff.2 fun i => (hne i).closure
  intro p hp hzero
  rw [closure_pi_set, recessionCone_pi hpine] at hp
  rw [closure_pi_set, linealitySpace_pi hpine]
  exact fun i _ => h p (fun i => hp i (mem_univ i)) hzero i

/-- **Closedness of a finite sum**: a finite sum of closed convex sets is closed as soon as the
only way finitely many directions of recession can sum to zero is inside the lineality
spaces. -/
theorem Convex.isClosed_sum (hC : ∀ i, Convex ℝ (C i)) (hCc : ∀ i, IsClosed (C i))
    (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (C i)) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (C i)) :
    IsClosed (∑ i, C i) := by
  have hcl : ∀ i, closure (C i) = C i := fun i => (hCc i).closure_eq
  have hkey := forall_mem_linealitySpace_pi hne (by simp only [hcl]; exact h)
  have hmain := Convex.isClosed_image_closure (convex_pi fun i _ => hC i) piSum hkey
  rw [closure_pi_set] at hmain
  simp only [hcl] at hmain
  rwa [image_piSum_univ_pi] at hmain

/-- **Closure distributes over a finite sum**: `cl (C₁ + ⋯ + Cₘ) = cl C₁ + ⋯ + cl Cₘ`. -/
theorem Convex.closure_sum_eq (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (closure (C i))) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (closure (C i))) :
    closure (∑ i, C i) = ∑ i, closure (C i) := by
  have hmain := Convex.closure_image_eq (convex_pi fun i _ => hC i) piSum
    (forall_mem_linealitySpace_pi hne h)
  rwa [image_piSum_univ_pi, closure_pi_set, image_piSum_univ_pi] at hmain

/-- **The recession cone of a finite sum of closed convex sets**:
`0⁺(cl C₁ + ⋯ + cl Cₘ) = 0⁺(cl C₁) + ⋯ + 0⁺(cl Cₘ)`. -/
theorem Convex.recessionCone_sum (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (closure (C i))) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (closure (C i))) :
    recessionCone (∑ i, closure (C i)) = ∑ i, recessionCone (closure (C i)) := by
  have hpine : (univ.pi fun i => closure (C i)).Nonempty :=
    Set.univ_pi_nonempty_iff.2 fun i => (hne i).closure
  have hmain := Convex.recessionCone_image_closure (convex_pi fun i _ => hC i)
    (Set.univ_pi_nonempty_iff.2 hne) piSum (forall_mem_linealitySpace_pi hne h)
  rwa [closure_pi_set, image_piSum_univ_pi, recessionCone_pi hpine,
    image_piSum_univ_pi] at hmain

end Sum

end ConvexAnalysis
