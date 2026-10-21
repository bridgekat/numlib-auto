import Numlib.Analysis.InnerProductSpace.CompactSpectral.Basis

/-!
# Variational spectral endpoints and perturbation bounds

The infimum and supremum of the Rayleigh quotient over nonzero vectors are defined without
symmetry or finite dimensionality. Both vary by at most the norm of an operator perturbation.
For symmetric operators in finite dimension they are actual extremal eigenvalues.
-/

noncomputable section
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The infimum of the real Rayleigh quotient over the nonzero vectors. -/
def rayleighInfimum (T : E →L[𝕜] E) : ℝ :=
  ⨅ x : {x : E // x ≠ 0}, T.rayleighQuotient x

/-- The supremum of the real Rayleigh quotient over the nonzero vectors. -/
def rayleighSupremum (T : E →L[𝕜] E) : ℝ :=
  ⨆ x : {x : E // x ≠ 0}, T.rayleighQuotient x

/-- Every nonzero Rayleigh quotient lies above its variational lower endpoint. -/
theorem rayleighInfimum_le (T : E →L[𝕜] E) {x : E} (hx : x ≠ 0) :
    T.rayleighInfimum ≤ T.rayleighQuotient x :=
  ciInf_le (bddBelow_rayleighQuotient_subtype T) ⟨x, hx⟩

/-- Every nonzero Rayleigh quotient lies below its variational upper endpoint. -/
theorem le_rayleighSupremum (T : E →L[𝕜] E) {x : E} (hx : x ≠ 0) :
    T.rayleighQuotient x ≤ T.rayleighSupremum :=
  le_ciSup (bddAbove_rayleighQuotient_subtype T) ⟨x, hx⟩

variable [Nontrivial E]

/-- Lower variational endpoints can be compared by comparing all Rayleigh quotients. -/
theorem le_rayleighInfimum_iff (T : E →L[𝕜] E) (a : ℝ) :
    a ≤ T.rayleighInfimum ↔ ∀ x : E, x ≠ 0 → a ≤ T.rayleighQuotient x := by
  have : Nonempty {x : E // x ≠ 0} := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨⟨x, hx⟩⟩
  simp only [rayleighInfimum, le_ciInf_iff (bddBelow_rayleighQuotient_subtype T)]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.property⟩

/-- Upper variational endpoints can be compared by comparing all Rayleigh quotients. -/
theorem rayleighSupremum_le_iff (T : E →L[𝕜] E) (a : ℝ) :
    T.rayleighSupremum ≤ a ↔ ∀ x : E, x ≠ 0 → T.rayleighQuotient x ≤ a := by
  have : Nonempty {x : E // x ≠ 0} := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨⟨x, hx⟩⟩
  simp only [rayleighSupremum, ciSup_le_iff (bddAbove_rayleighQuotient_subtype T)]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.property⟩

/-- The two variational endpoints are ordered in a nontrivial space. -/
theorem rayleighInfimum_le_rayleighSupremum (T : E →L[𝕜] E) :
    T.rayleighInfimum ≤ T.rayleighSupremum := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact (T.rayleighInfimum_le hx).trans (T.le_rayleighSupremum hx)

/-- A perturbation changes the lower variational endpoint by at most its operator norm. -/
theorem abs_rayleighInfimum_sub_le (T S : E →L[𝕜] E) :
    |T.rayleighInfimum - S.rayleighInfimum| ≤ ‖T - S‖ := by
  have bound (A B : E →L[𝕜] E) : A.rayleighInfimum - ‖A - B‖ ≤ B.rayleighInfimum := by
    apply (le_rayleighInfimum_iff B _).mpr
    intro x hx
    have h := (abs_le.mp ((A - B).rayleighQuotient_le_norm x)).2
    have he : (A - B).rayleighQuotient x = A.rayleighQuotient x - B.rayleighQuotient x := by
      simp [sub_eq_add_neg, rayleighQuotient_add]
    rw [he] at h
    linarith [A.rayleighInfimum_le hx]
  have h₁ := bound T S
  have h₂ := bound S T
  rw [norm_sub_rev S T] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A perturbation changes the upper variational endpoint by at most its operator norm. -/
theorem abs_rayleighSupremum_sub_le (T S : E →L[𝕜] E) :
    |T.rayleighSupremum - S.rayleighSupremum| ≤ ‖T - S‖ := by
  have bound (A B : E →L[𝕜] E) : A.rayleighSupremum ≤ B.rayleighSupremum + ‖A - B‖ := by
    apply (rayleighSupremum_le_iff A _).mpr
    intro x hx
    have h := (abs_le.mp ((A - B).rayleighQuotient_le_norm x)).2
    have he : (A - B).rayleighQuotient x = A.rayleighQuotient x - B.rayleighQuotient x := by
      simp [sub_eq_add_neg, rayleighQuotient_add]
    rw [he] at h
    linarith [B.le_rayleighSupremum hx]
  have h₁ := bound T S
  have h₂ := bound S T
  rw [norm_sub_rev S T] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- In finite dimension the lower variational endpoint of a symmetric operator is an eigenvalue. -/
theorem IsSymmetric.hasEigenvalue_rayleighInfimum [FiniteDimensional 𝕜 E]
    {T : E →L[𝕜] E} (hT : T.IsSymmetric) :
    Module.End.HasEigenvalue T.toLinearMap (T.rayleighInfimum : 𝕜) := by
  simpa [rayleighInfimum, rayleighQuotient, reApplyInnerSelf_apply] using
    hT.hasEigenvalue_iInf_of_finiteDimensional

/-- In finite dimension the upper variational endpoint of a symmetric operator is an eigenvalue. -/
theorem IsSymmetric.hasEigenvalue_rayleighSupremum [FiniteDimensional 𝕜 E]
    {T : E →L[𝕜] E} (hT : T.IsSymmetric) :
    Module.End.HasEigenvalue T.toLinearMap (T.rayleighSupremum : 𝕜) := by
  simpa [rayleighSupremum, rayleighQuotient, reApplyInnerSelf_apply] using
    hT.hasEigenvalue_iSup_of_finiteDimensional

end ContinuousLinearMap
