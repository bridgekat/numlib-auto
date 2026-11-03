import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.PiL2
import NumlibSurface.ConnGouldToint.Chapter12.Section03

/-! # Smooth constraints with a degenerate remote active set

The nonnegative orthant in the first two coordinates admits smooth inequalities
that agree with the coordinate inequalities near the origin and have just one
active constraint at a remote point of their common boundary.
-/

open Set Filter Topology
open scoped ContDiff RealInnerProductSpace

namespace ConnGouldToint.Chapter12.ConstraintExample

/-- The two constrained coordinates and one free coordinate. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Continuous coordinate projections. -/
def coordinate (i : Fin 3) : Space →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i

private noncomputable def firstCut (z : Space) : ℝ := Real.smoothTransition (-4 * z 2 - 1)

private noncomputable def secondCut (z : Space) : ℝ := Real.smoothTransition (-4 * z 2 - 2)

private noncomputable def penalty (z : Space) : ℝ := expNegInvGlue (-z 0) + expNegInvGlue (-z 1)

/-- Two inequalities whose feasible set is the product of a quadrant with the
real line. The first inequality takes over enforcement of both signs before
the second inequality becomes strictly positive on the quadrant. -/
noncomputable def constraints (i : Fin 2) (z : Space) : ℝ :=
  if i = 0 then (1 - firstCut z) * z 0 - firstCut z * penalty z
  else (1 - secondCut z) * z 1 + secondCut z

private theorem penalty_nonneg (z : Space) : 0 ≤ penalty z :=
  add_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

private theorem penalty_eq_zero (z : Space) : penalty z = 0 ↔ 0 ≤ z 0 ∧ 0 ≤ z 1 := by
  rw [penalty, add_eq_zero_iff_of_nonneg (expNegInvGlue.nonneg _)
    (expNegInvGlue.nonneg _), expNegInvGlue.zero_iff_nonpos,
    expNegInvGlue.zero_iff_nonpos, neg_nonpos, neg_nonpos]

/-- The feasible set is exactly the quadrant in the first two coordinates. -/
theorem feasible_iff (z : Space) : (∀ i, 0 ≤ constraints i z) ↔ 0 ≤ z 0 ∧ 0 ≤ z 1 := by
  have hA : 0 ≤ firstCut z := Real.smoothTransition.nonneg _
  have hA' : 0 ≤ 1 - firstCut z := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hB : 0 ≤ secondCut z := Real.smoothTransition.nonneg _
  have hB' : 0 ≤ 1 - secondCut z := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  constructor
  · intro h
    have h₀ := h 0
    have h₁ := h 1
    change 0 ≤ constraints 0 z at h₀
    simp only [constraints] at h₀
    simp only [constraints, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h₁
    by_cases hb : secondCut z = 0
    · have hy : 0 ≤ z 1 := by simpa [hb] using h₁
      refine ⟨?_, hy⟩
      by_contra! hx
      have hp : 0 < penalty z :=
        add_pos_of_pos_of_nonneg (expNegInvGlue.pos_of_pos (neg_pos.mpr hx))
          (expNegInvGlue.nonneg _)
      rcases hA.eq_or_lt with ha | ha
      · rw [← ha, sub_zero, one_mul, zero_mul, sub_zero] at h₀
        exact (not_lt_of_ge h₀) hx
      · have hn := sub_neg.mpr
          ((mul_nonpos_of_nonneg_of_nonpos hA' hx.le).trans_lt (mul_pos ha hp))
        exact (not_lt_of_ge h₀) hn
    · have ht : 0 < -4 * z 2 - 2 :=
        lt_of_not_ge fun h ↦ hb (Real.smoothTransition.zero_of_nonpos h)
      have ha : firstCut z = 1 := Real.smoothTransition.one_of_one_le (by linarith)
      rw [ha, sub_self, zero_mul, one_mul, zero_sub] at h₀
      exact (penalty_eq_zero z).mp (le_antisymm (neg_nonneg.mp h₀) (penalty_nonneg z))
  · intro hz i
    fin_cases i
    · simpa [constraints, (penalty_eq_zero z).mpr hz] using mul_nonneg hA' hz.1
    · simpa [constraints] using add_nonneg (mul_nonneg hB' hz.2) hB

/-- Near and above height zero, the inequalities are the two coordinates. -/
theorem constraints_of_height_ge (z : Space) (hz : -(1 / 4 : ℝ) ≤ z 2) :
    constraints 0 z = z 0 ∧ constraints 1 z = z 1 := by
  have ha : firstCut z = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  have hb : secondCut z = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  norm_num [constraints, ha, hb]

/-- At the remote boundary point of height minus one, only the first
inequality is active. -/
theorem constraints_at_remote :
    constraints 0 (WithLp.toLp 2 ![0, 0, -1]) = 0 ∧
    constraints 1 (WithLp.toLp 2 ![0, 0, -1]) = 1 := by
  let w : Space := WithLp.toLp 2 ![0, 0, -1]
  have ha : firstCut w = 1 := Real.smoothTransition.one_of_one_le (by norm_num [w])
  have hb : secondCut w = 1 := Real.smoothTransition.one_of_one_le (by norm_num [w])
  change constraints 0 w = 0 ∧ constraints 1 w = 1
  norm_num [constraints, ha, hb, penalty, w, expNegInvGlue.zero]

/-- Both inequalities are infinitely differentiable. -/
theorem contDiff_constraints (i : Fin 2) : ContDiff ℝ ∞ (constraints i) := by
  have hcoord (j : Fin 3) : ContDiff ℝ ∞ (fun z : Space ↦ z j) := (coordinate j).contDiff
  have ha : ContDiff ℝ ∞ firstCut := Real.smoothTransition.contDiff.comp
    (((contDiff_const : ContDiff ℝ ∞ (fun _ : Space ↦ (-4 : ℝ))).mul (hcoord 2)).sub contDiff_const)
  have hb : ContDiff ℝ ∞ secondCut := Real.smoothTransition.contDiff.comp
    (((contDiff_const : ContDiff ℝ ∞ (fun _ : Space ↦ (-4 : ℝ))).mul (hcoord 2)).sub contDiff_const)
  have hp : ContDiff ℝ ∞ penalty :=
    (expNegInvGlue.contDiff.comp (hcoord 0).neg).add
      (expNegInvGlue.contDiff.comp (hcoord 1).neg)
  have hone : ContDiff ℝ ∞ (fun _ : Space ↦ (1 : ℝ)) := contDiff_const
  by_cases hi : i = 0
  · have he : constraints i = fun z ↦ (1 - firstCut z) * z 0 - firstCut z * penalty z :=
      funext fun z ↦ ite_eq_left hi
    rw [he]
    exact ((hone.sub ha).mul (hcoord 0)).sub (ha.mul hp)
  · have he : constraints i = fun z ↦ (1 - secondCut z) * z 1 + secondCut z :=
      funext fun z ↦ ite_eq_right hi
    rw [he]
    exact ((hone.sub hb).mul (hcoord 1)).add hb

/-- At the origin, the two constraint gradients are the first two coordinate
covectors. -/
theorem fderiv_constraints_zero :
    fderiv ℝ (constraints 0) 0 = coordinate 0 ∧
    fderiv ℝ (constraints 1) 0 = coordinate 1 := by
  have hopen : {z : Space | -(1 / 4 : ℝ) < z 2} ∈ 𝓝 (0 : Space) := by
    apply (isOpen_lt continuous_const (coordinate 2).continuous).mem_nhds
    norm_num [coordinate, PiLp.zero_apply]
  have h0 : constraints 0 =ᶠ[𝓝 (0 : Space)] coordinate 0 :=
    Filter.mem_of_superset hopen fun z hz ↦ (constraints_of_height_ge z hz.le).1
  have h1 : constraints 1 =ᶠ[𝓝 (0 : Space)] coordinate 1 :=
    Filter.mem_of_superset hopen fun z hz ↦ (constraints_of_height_ge z hz.le).2
  exact ⟨h0.fderiv_eq.trans (coordinate 0).hasFDerivAt.fderiv,
    h1.fderiv_eq.trans (coordinate 1).hasFDerivAt.fderiv⟩


/-- Both inequalities are active at the origin. -/
theorem active_at_zero : activeConstraintSet constraints (0 : Space) = univ := by
  have h := constraints_of_height_ge (0 : Space) (by norm_num [PiLp.zero_apply])
  ext i
  fin_cases i <;> simp [activeConstraintSet, h.1, h.2, PiLp.zero_apply]

/-- Only index zero is active at the remote point. -/
theorem active_at_remote :
    activeConstraintSet constraints (WithLp.toLp 2 ![0, 0, -1]) = {0} := by
  ext i
  fin_cases i <;> simp [activeConstraintSet, constraints_at_remote.1, constraints_at_remote.2]

/-- The sole remote active constraint has zero derivative. -/
theorem fderiv_active_constraint_at_remote :
    fderiv ℝ (constraints 0) (WithLp.toLp 2 ![0, 0, -1]) = 0 := by
  let w : Space := WithLp.toLp 2 ![0, 0, -1]
  have hnear : {z : Space | z 2 < -(1 / 2 : ℝ)} ∈ 𝓝 w := by
    apply (isOpen_lt (coordinate 2).continuous continuous_const).mem_nhds
    norm_num [w, coordinate]
  have hmax : IsLocalMax (constraints 0) w := by
    refine Filter.mem_of_superset hnear fun z hz ↦ ?_
    change constraints 0 z ≤ constraints 0 w
    have ha : firstCut z = 1 := Real.smoothTransition.one_of_one_le (by
      change z 2 < -(1 / 2 : ℝ) at hz
      linarith)
    rw [show constraints 0 w = 0 from constraints_at_remote.1]
    simp only [constraints, ite_true, ha, sub_self, zero_mul, one_mul, zero_sub, neg_nonpos]
    exact penalty_nonneg z
  exact hmax.hasFDerivAt_eq_zero
    ((contDiff_constraints 0).differentiable (by simp) w).hasFDerivAt

/-- The inward normals at the origin are the first two standard basis vectors. -/
theorem gradient_constraints_zero (i : Fin 2) :
    gradient (constraints i) 0 = EuclideanSpace.single (Fin.castLE (by decide : 2 ≤ 3) i) 1 := by
  have hf (j : Fin 2) : fderiv ℝ (constraints j) 0 = coordinate (Fin.castLE (by decide : 2 ≤ 3) j) := by
    fin_cases j
    · exact fderiv_constraints_zero.1
    · exact fderiv_constraints_zero.2
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, hf, EuclideanSpace.inner_single_left]
  simp [coordinate]

/-- The active normals at the origin are linearly independent. -/
theorem independent_active_at_zero :
    LinearIndependent ℝ (fun i : activeConstraintSet constraints (0 : Space) ↦
      gradient (constraints i) 0) := by
  simp only [gradient_constraints_zero]
  apply (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)).linearIndependent.comp
  intro i j h
  apply Subtype.ext
  exact Fin.ext (congrArg (fun v : Fin 3 ↦ v.val) h)

/-- The inward normal sum with both multipliers equal to one is (1,1,0). -/
theorem strict_multipliers_at_zero :
    HasStrictActiveMultipliers constraints (fun i ↦ gradient (constraints i))
      (fun _ ↦ (WithLp.toLp 2 ![1, 1, 0] : Space)) 0 := by
  refine ⟨fun _ ↦ 1, ?_, fun _ _ ↦ zero_lt_one, ?_⟩
  · ext j
    fin_cases j <;> simp [Fin.sum_univ_two, gradient_constraints_zero,
      PiLp.add_apply]
  · simp [active_at_zero]

open Optimization in
/-- The orthant satisfies the geometric strict-complementarity condition at
the origin for gradient (1,1,0). -/
theorem ao4b_at_zero :
    -(WithLp.toLp 2 ![1, 1, 0] : Space) ∈ intrinsicInterior ℝ
      (normalDirections {v : Space | 0 ≤ v 0 ∧ 0 ≤ v 1} (0 : Space)) := by
  let C : Set Space := {v | 0 ≤ v 0 ∧ 0 ≤ v 1}
  have hC : Chapter03.AC2 C := by
    have hx : (0 : Space) ∈ C := by simp [C, PiLp.zero_apply]
    refine ⟨⟨0, hx⟩, ?_, ?_⟩
    · exact (isClosed_le continuous_const (coordinate 0).continuous).inter
        (isClosed_le continuous_const (coordinate 1).continuous)
    · exact (convex_halfSpace_ge (coordinate 0).toLinearMap.isLinear 0).inter
        (convex_halfSpace_ge (coordinate 1).toLinearMap.isLinear 0)
  have hset : Chapter03.AC7 C constraints := by
    ext z
    exact (feasible_iff z).symm
  have hx : (0 : Space) ∈ C := by simp [C, PiLp.zero_apply]
  have hc (i : Fin 2) : HasStrictFDerivAt (constraints i) (fderiv ℝ (constraints i) 0) 0 :=
    (contDiff_constraints i).contDiffAt.hasStrictFDerivAt (by simp)
  exact (strictActiveMultipliers_iff_mem_relint_normalDirections hC hset hx
    (activeLinearizedConeMatches_of_activeGradient_independent hset hx hc
      independent_active_at_zero)).mp strict_multipliers_at_zero

end ConnGouldToint.Chapter12.ConstraintExample
