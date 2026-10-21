import Numlib.Optimization.TaylorCriticality
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Criticality on bounded feasible displacements

A linear functional is tested against feasible displacements of norm at most one. The resulting
criticality is a compact optimality gap. Closedness provides compactness in finite dimension;
convexity and smoothness are not required for these elementary comparison results.
-/

noncomputable section

namespace Optimization.FeasibleCriticality

open Optimization.TaylorCriticality

variable {E : Type*} [NormedAddCommGroup E]

/-- Feasible displacements of norm at most one from `x` into `C`. -/
def unitFeasibleSteps (C : Set E) (x : E) : Set E := {d | x + d ∈ C ∧ ‖d‖ ≤ 1}

@[simp] theorem mem_unitFeasibleSteps {C : Set E} {x d : E} :
    d ∈ unitFeasibleSteps C x ↔ x + d ∈ C ∧ ‖d‖ ≤ 1 := Iff.rfl

@[simp] theorem zero_mem_unitFeasibleSteps {C : Set E} {x : E} :
    (0 : E) ∈ unitFeasibleSteps C x ↔ x ∈ C := by simp [unitFeasibleSteps]

variable [NormedSpace ℝ E]

/-- Closed constraints give a compact set of bounded feasible steps in finite dimension. -/
theorem isCompact_unitFeasibleSteps [FiniteDimensional ℝ E] {C : Set E} (hC : IsClosed C)
    (x : E) : IsCompact (unitFeasibleSteps C x) := by
  have heq : unitFeasibleSteps C x = (fun d => x + d) ⁻¹' C ∩ Metric.closedBall 0 1 := by
    ext d
    simp [unitFeasibleSteps]
  rw [heq]
  exact (isCompact_closedBall (0 : E) 1).inter_left
    (hC.preimage (continuous_const.add continuous_id))

/-- The maximal decrease of the linear model over the unit feasible displacements. -/
def feasibleCriticality (C : Set E) (x : E) (A : E →L[ℝ] ℝ) : ℝ :=
  gapOn (fun d => -A d) (unitFeasibleSteps C x)

/-- The feasible criticality is exactly the existing scalar-decrement gap. -/
theorem feasibleCriticality_eq_gapOn (C : Set E) (x : E) (A : E →L[ℝ] ℝ) :
    feasibleCriticality C x A = gapOn (fun d => -A d) (unitFeasibleSteps C x) := rfl

variable [FiniteDimensional ℝ E] {C : Set E} {x : E}

/-- A feasible unit step attains the criticality, equivalently minimizing the linear model. -/
theorem exists_eq_feasibleCriticality (hC : IsClosed C) (hx : x ∈ C) (A : E →L[ℝ] ℝ) :
    ∃ d ∈ unitFeasibleSteps C x, -A d = feasibleCriticality C x A :=
  exists_eq_gapOn (isCompact_unitFeasibleSteps hC x)
    ⟨0, zero_mem_unitFeasibleSteps.mpr hx⟩ A.continuous.neg.continuousOn

/-- The negative of criticality is an attained minimum of the linear functional. -/
theorem exists_isLeast_feasibleCriticality (hC : IsClosed C) (hx : x ∈ C)
    (A : E →L[ℝ] ℝ) :
    ∃ d ∈ unitFeasibleSteps C x, A d = -feasibleCriticality C x A ∧
      IsLeast (A '' unitFeasibleSteps C x) (A d) := by
  obtain ⟨d, hd, heq⟩ := exists_eq_feasibleCriticality hC hx A
  refine ⟨d, hd, by linarith, Set.mem_image_of_mem A hd, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have hb := le_gapOn (isCompact_unitFeasibleSteps hC x) A.continuous.neg.continuousOn he
  change -A e ≤ feasibleCriticality C x A at hb
  linarith

/-- Equivalence with the negative-infimum convention for criticality. -/
theorem feasibleCriticality_eq_neg_sInf (hC : IsClosed C) (hx : x ∈ C)
    (A : E →L[ℝ] ℝ) :
    feasibleCriticality C x A = -sInf (A '' unitFeasibleSteps C x) := by
  obtain ⟨d, _, heq, hmin⟩ := exists_isLeast_feasibleCriticality hC hx A
  rw [hmin.csInf_eq]
  linarith

/-- Each feasible linear decrease is below the criticality. -/
theorem neg_apply_le_feasibleCriticality (hC : IsClosed C) (A : E →L[ℝ] ℝ)
    {d : E} (hd : d ∈ unitFeasibleSteps C x) : -A d ≤ feasibleCriticality C x A :=
  le_gapOn (isCompact_unitFeasibleSteps hC x) A.continuous.neg.continuousOn hd

/-- A bound on criticality is equivalent to bounding every feasible linear decrease. -/
theorem feasibleCriticality_le_iff (hC : IsClosed C) (hx : x ∈ C) (A : E →L[ℝ] ℝ)
    {c : ℝ} : feasibleCriticality C x A ≤ c ↔
      ∀ d ∈ unitFeasibleSteps C x, -A d ≤ c :=
  gapOn_le_iff (isCompact_unitFeasibleSteps hC x)
    ⟨0, zero_mem_unitFeasibleSteps.mpr hx⟩ A.continuous.neg.continuousOn

/-- Criticality is nonnegative at every feasible point. -/
theorem feasibleCriticality_nonneg (hC : IsClosed C) (hx : x ∈ C) (A : E →L[ℝ] ℝ) :
    0 ≤ feasibleCriticality C x A := by
  simpa using neg_apply_le_feasibleCriticality hC A (zero_mem_unitFeasibleSteps.mpr hx)

/-- Zero criticality means all feasible unit directional derivatives are nonnegative. -/
theorem feasibleCriticality_eq_zero_iff (hC : IsClosed C) (hx : x ∈ C)
    (A : E →L[ℝ] ℝ) : feasibleCriticality C x A = 0 ↔
      ∀ d ∈ unitFeasibleSteps C x, 0 ≤ A d := by
  simpa only [feasibleCriticality, neg_nonpos] using
    (gapOn_eq_zero_iff (Δ := fun d => -A d) (isCompact_unitFeasibleSteps hC x)
      A.continuous.neg.continuousOn (zero_mem_unitFeasibleSteps.mpr hx) (by simp))

/-- Positive homogeneity in the derivative, including multiplication by zero. -/
theorem feasibleCriticality_smul (hC : IsClosed C) (hx : x ∈ C)
    (A : E →L[ℝ] ℝ) {a : ℝ} (ha : 0 ≤ a) :
    feasibleCriticality C x (a • A) = a * feasibleCriticality C x A := by
  obtain ⟨d, hd, heq⟩ := exists_eq_feasibleCriticality hC hx A
  apply le_antisymm
  · apply (feasibleCriticality_le_iff hC hx (a • A)).mpr
    intro e he
    have hb := mul_le_mul_of_nonneg_left (neg_apply_le_feasibleCriticality hC A he) ha
    simpa using hb
  · have hb := neg_apply_le_feasibleCriticality hC (a • A) hd
    simpa [← heq] using hb

/-- Division of derivative data by a positive number divides its criticality. -/
theorem feasibleCriticality_inv_smul (hC : IsClosed C) (hx : x ∈ C)
    (A : E →L[ℝ] ℝ) {a : ℝ} (ha : 0 < a) :
    feasibleCriticality C x (a⁻¹ • A) = feasibleCriticality C x A / a := by
  simpa [div_eq_mul_inv, mul_comm] using
    feasibleCriticality_smul hC hx A (inv_nonneg.mpr ha.le)

/-- Perturbing the derivative changes criticality by at most its operator norm error. -/
theorem feasibleCriticality_lipschitz_derivative (hC : IsClosed C) (hx : x ∈ C)
    (A B : E →L[ℝ] ℝ) :
    |feasibleCriticality C x A - feasibleCriticality C x B| ≤ ‖A - B‖ := by
  apply abs_gapOn_sub_le (isCompact_unitFeasibleSteps hC x)
    ⟨0, zero_mem_unitFeasibleSteps.mpr hx⟩
    A.continuous.neg.continuousOn B.continuous.neg.continuousOn
  intro d hd
  have hb := (A - B).le_opNorm d
  have hn : ‖(A - B) d‖ ≤ ‖A - B‖ :=
    hb.trans (mul_le_of_le_one_right (norm_nonneg _) hd.2)
  have heq : -A d - -B d = -((A - B) d) := by simp only [sub_apply]; ring
  change |-A d - -B d| ≤ ‖A - B‖
  rw [heq, abs_neg]
  simpa only [Real.norm_eq_abs] using hn

end Optimization.FeasibleCriticality
