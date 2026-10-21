import Numlib.Optimization.TargetResidualJets

/-!
# Uniform first-order jets of affine maps

Affine maps have constant first derivatives, so the derivative norm itself is a global
bound and the first jet has Lipschitz constant zero.
-/

noncomputable section
namespace Optimization.ConstrainedTaylorCriticality
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An affine map has bounded constant first jets on the whole space. -/
theorem affine_hasBoundedLipschitzJets_one (L : E →L[ℝ] F) (a : F) :
    HasBoundedLipschitzJets (fun x => L x + a) 1 Set.univ ‖L‖ 0 := by
  refine ⟨isOpen_univ, convex_univ, (L.contDiff.add contDiff_const).contDiffOn,
    norm_nonneg _, le_rfl, ?_, ?_⟩
  · intro j hj x _
    have hj1 : j = 1 := by have := Finset.mem_Icc.mp hj; omega
    subst j
    rw [norm_iteratedFDeriv_one, (L.hasFDerivAt.add_const a).fderiv]
  · intro j hj x _ y _
    have hj1 : j = 1 := by have := Finset.mem_Icc.mp hj; omega
    subst j
    have he : iteratedFDeriv ℝ 1 (fun z => L z + a) y =
        iteratedFDeriv ℝ 1 (fun z => L z + a) x := by
      ext v
      simp only [iteratedFDeriv_one_apply, (L.hasFDerivAt.add_const a).fderiv]
    rw [he, sub_self, norm_zero, zero_mul]

end Optimization.ConstrainedTaylorCriticality
