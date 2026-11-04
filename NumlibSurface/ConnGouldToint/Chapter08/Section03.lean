/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! # Rayleigh infima in Hilbert spaces -/

open Set
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter08

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Rayleigh infimum (8.3.3) of a bounded operator on a real inner
product space. In infinite dimensions it need not be an eigenvalue. -/
noncomputable def hilbertRayleighFloor (H : E →L[ℝ] E) : ℝ :=
  ⨅ d : {d : E // d ≠ 0}, H.rayleighQuotient d

private theorem bddBelow_nonzero_rayleigh (H : E →L[ℝ] E) :
    BddBelow (range fun d : {d : E // d ≠ 0} ↦ H.rayleighQuotient d) := by
  refine ⟨-‖H‖, ?_⟩
  rintro _ ⟨d, rfl⟩
  exact (neg_le_neg (H.rayleighQuotient_le_norm d)).trans (neg_abs_le _)

private theorem rayleighQuotient_real (H : E →L[ℝ] E) (d : E) :
    H.rayleighQuotient d = ⟪d, H d⟫ / ‖d‖ ^ 2 := by
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
  simp [real_inner_comm (H d) d]

/-- A uniform quadratic-form lower bound is equivalent to a lower
bound on the Rayleigh infimum. -/
theorem hilbertRayleighFloor_le_iff [Nontrivial E] (H : E →L[ℝ] E) (a : ℝ) :
    a ≤ hilbertRayleighFloor H ↔ ∀ d, a * ‖d‖ ^ 2 ≤ ⟪d, H d⟫ := by
  let : Nonempty {d : E // d ≠ 0} := by
    obtain ⟨d, hd⟩ := exists_ne (0 : E)
    exact ⟨⟨d, hd⟩⟩
  rw [hilbertRayleighFloor, le_ciInf_iff (bddBelow_nonzero_rayleigh H)]
  constructor
  · intro h d
    by_cases hd : d = 0
    · simp [hd]
    have hd₂ := sq_pos_of_pos (norm_pos_iff.mpr hd)
    have hq := h ⟨d, hd⟩
    rw [rayleighQuotient_real] at hq
    exact (le_div_iff₀ hd₂).mp hq
  · intro h d
    rw [rayleighQuotient_real]
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr d.property))).mpr (h d)

/-- A strict threshold above the Rayleigh infimum is reached by a unit
direction. This provides negative curvature without an attaining eigenvector. -/
theorem exists_unit_direction_below_of_hilbertRayleighFloor_lt [Nontrivial E]
    (H : E →L[ℝ] E) {a : ℝ} (ha : hilbertRayleighFloor H < a) :
    ∃ d, ‖d‖ = 1 ∧ ⟪d, H d⟫ < a := by
  have ha' : (⨅ d : Metric.sphere (0 : E) 1, H.rayleighQuotient d) < a := by
    rwa [← H.iInf_rayleigh_eq_iInf_rayleigh_sphere zero_lt_one]
  let : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  obtain ⟨d, hd⟩ := exists_lt_of_ciInf_lt ha'
  have hn : ‖(d : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using d.property
  rw [rayleighQuotient_real, hn, one_pow, div_one] at hd
  exact ⟨d, hn, hd⟩

end ConnGouldToint.Chapter08
