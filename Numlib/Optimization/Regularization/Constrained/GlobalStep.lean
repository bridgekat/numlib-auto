import Numlib.Optimization.Regularization.GlobalStep

/-!
# Positive global-gap model steps on feasible displacements

Only actual feasible model values occur in the fraction-of-global-gap rule.
A zero return with positive fraction makes zero a genuine constrained minimum;
no criticality certificate is encoded in the step predicate.
-/

namespace ModelDecrease
open Set
variable {E : Type*} [NormedAddCommGroup E]

/-- A feasible step attains a fraction of every actual feasible model decrease. -/
def ApproximateGlobalStepOn (m : E → ℝ) (C : Set E) (μ : ℝ) (s : E) : Prop :=
  s ∈ C ∧ ∀ t ∈ C, μ * (m 0 - m t) ≤ m 0 - m s

/-- At a genuine constrained global minimizer, primitive feasible comparisons
are equivalent to the standard fraction of optimal model gap. -/
theorem approximateGlobalStepOn_iff_of_isMinOn {m : E → ℝ} {C : Set E}
    {μ : ℝ} (hμ : 0 ≤ μ) {s tstar : E} (hstar : tstar ∈ C)
    (hmin : IsMinOn m C tstar) :
    ApproximateGlobalStepOn m C μ s ↔
      s ∈ C ∧ μ * (m 0 - m tstar) ≤ m 0 - m s := by
  refine ⟨fun h => ⟨h.1, h.2 tstar hstar⟩, fun h => ⟨h.1, fun t ht => ?_⟩⟩
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left (hmin ht) _) hμ).trans h.2

/-- Feasibility of zero makes every primitive global-gap step nonincreasing. -/
theorem ApproximateGlobalStepOn.nonincrease {m : E → ℝ} {C : Set E} {μ : ℝ} {s : E}
    (h : ApproximateGlobalStepOn m C μ s) (hzero : (0 : E) ∈ C) : m s ≤ m 0 := by
  have hz := h.2 0 hzero
  simpa only [sub_self, mul_zero, sub_nonneg] using hz

/-- Positive fraction and zero model decrease imply actual constrained global
minimality of zero, rather than merely a stationary-point condition. -/
theorem ApproximateGlobalStepOn.isMinOn_zero {m : E → ℝ} {C : Set E} {μ : ℝ} {s : E}
    (h : ApproximateGlobalStepOn m C μ s) (hμ : 0 < μ) (hz : m 0 = m s) :
    IsMinOn m C 0 := by
  intro t ht
  have hh := h.2 t ht
  rw [←hz, sub_self] at hh
  by_contra hn
  have hp := mul_pos hμ (sub_pos.mpr (lt_of_not_ge hn))
  linarith

/-- Any genuinely improving feasible comparison forces strict model decrease
in a positive-fraction global-gap return. -/
theorem ApproximateGlobalStepOn.strict_decrease {m : E → ℝ} {C : Set E}
    {μ : ℝ} {s d : E} (h : ApproximateGlobalStepOn m C μ s) (hμ : 0 < μ)
    (hd : d ∈ C) (hbetter : m d < m 0) : m s < m 0 := by
  have hp := mul_pos hμ (sub_pos.mpr hbetter)
  have hh := h.2 d hd
  linarith

end ModelDecrease
