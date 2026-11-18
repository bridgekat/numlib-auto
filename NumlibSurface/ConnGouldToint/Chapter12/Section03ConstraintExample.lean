/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.PiL2
import NumlibSurface.ConnGouldToint.Chapter12.Section03

/-!
# Conn, Gould and Toint, Section 12.3: smooth constraints with a degenerate remote active set

This module builds the constraints that the counterexample
`ConnGouldToint.Chapter12.theorem_12_3_8_iterate_identification_counterexample` to Lemma 12.3.7 and
Theorem 12.3.8 of [conn2000trust] uses. In $\mathbb{R}^3$ with coordinates $z = (z_0, z_1, z_2)$,
the feasible set is the product $Q = \{z : z_0 \ge 0, z_1 \ge 0\}$ of a quadrant with the real line.
The module gives two infinitely differentiable inequalities $c_0(z) \ge 0$ and $c_1(z) \ge 0$ whose
feasible set is exactly $Q$. For $z_2 \ge -1/4$ they are the coordinate inequalities $z_0 \ge 0$ and
$z_1 \ge 0$, so at the origin both constraints are active and their gradients are independent. At
the remote boundary point $(0, 0, -1)$ only $c_0$ is active, and its gradient there is zero.

## Main definitions

* `ConnGouldToint.Chapter12.ConstraintExample.constraints`: the two smooth inequalities $c_0$ and
  $c_1$.

## Main results

* `ConnGouldToint.Chapter12.ConstraintExample.feasible_iff`: $c_0(z) \ge 0$ and $c_1(z) \ge 0$ if
  and only if $z_0 \ge 0$ and $z_1 \ge 0$.
* `ConnGouldToint.Chapter12.ConstraintExample.contDiff_constraints`: both constraints are infinitely
  differentiable.
* `ConnGouldToint.Chapter12.ConstraintExample.independent_active_at_zero`: both constraints are
  active at the origin, with linearly independent gradients.
* `ConnGouldToint.Chapter12.ConstraintExample.ao4b_at_zero`: at the origin, $-(1, 1, 0)$ lies in the
  relative interior of the normal cone of $Q$.
* `ConnGouldToint.Chapter12.ConstraintExample.active_at_remote`: at $(0, 0, -1)$ only $c_0$ is
  active.
* `ConnGouldToint.Chapter12.ConstraintExample.fderiv_active_constraint_at_remote`: the derivative of
  $c_0$ at $(0, 0, -1)$ is zero.

## Implementation notes

* Let $\theta$ be the smooth transition function `Real.smoothTransition`, which is $0$ on
  $(-\infty, 0]$ and $1$ on $[1, \infty)$, and let $\psi$ be `expNegInvGlue`, with
  $\psi(t) = e^{-1/t}$ for $t > 0$ and $\psi(t) = 0$ for $t \le 0$. With the cut-offs
  $\theta_1(z) = \theta(-4 z_2 - 1)$ and $\theta_2(z) = \theta(-4 z_2 - 2)$ and the penalty
  $p(z) = \psi(-z_0) + \psi(-z_1)$, the constraints are $c_0 = (1 - \theta_1) z_0 - \theta_1 p$ and
  $c_1 = (1 - \theta_2) z_1 + \theta_2$.
* The cut-off $\theta_1$ equals $1$ for $z_2 \le -1/2$, where $c_1$ is still the coordinate $z_1$.
  Hence $c_0$ enforces both sign conditions before $c_1$ becomes positive on the quadrant.
-/

open Set Filter Topology
open scoped ContDiff RealInnerProductSpace

namespace ConnGouldToint.Chapter12.ConstraintExample

/-- The space $\mathbb{R}^3$ with the Euclidean inner product, in which the first two coordinates
are constrained and the third is free. This is the space of the counterexample to Theorem 12.3.8
of [conn2000trust]. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The coordinate projection $z \mapsto z_i$ on $\mathbb{R}^3$, as a continuous linear functional,
for $i \in \{0, 1, 2\}$. -/
def coordinate (i : Fin 3) : Space →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i

private noncomputable def firstCut (z : Space) : ℝ := Real.smoothTransition (-4 * z 2 - 1)

private noncomputable def secondCut (z : Space) : ℝ := Real.smoothTransition (-4 * z 2 - 2)

private noncomputable def penalty (z : Space) : ℝ := expNegInvGlue (-z 0) + expNegInvGlue (-z 1)

/-- The two inequality constraints of the counterexample to Theorem 12.3.8 of [conn2000trust]. With
the cut-offs $\theta_1(z) = \theta(-4 z_2 - 1)$ and $\theta_2(z) = \theta(-4 z_2 - 2)$ built
from the smooth transition function $\theta$, and the penalty $p(z) = \psi(-z_0) + \psi(-z_1)$
built from $\psi(t) = e^{-1/t}$ for $t > 0$, $\psi(t) = 0$ for $t \le 0$,
$$c_0(z) = (1 - \theta_1(z))\, z_0 - \theta_1(z)\, p(z), \qquad c_1(z) = (1 - \theta_2(z))\,
  z_1 + \theta_2(z).$$

The functions $\theta$ and $\psi$ are `Real.smoothTransition` and `expNegInvGlue`. The penalty
$p$ vanishes exactly on the quadrant $z_0, z_1 \ge 0$. The constraint $c_0$ takes over both sign
conditions (for $z_2 \le -1/2$) before $c_1$ becomes strictly positive on the quadrant (for
$z_2 < -1/2$). -/
noncomputable def constraints (i : Fin 2) (z : Space) : ℝ :=
  if i = 0 then (1 - firstCut z) * z 0 - firstCut z * penalty z
  else (1 - secondCut z) * z 1 + secondCut z

private theorem penalty_nonneg (z : Space) : 0 ≤ penalty z :=
  add_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

private theorem penalty_eq_zero (z : Space) : penalty z = 0 ↔ 0 ≤ z 0 ∧ 0 ≤ z 1 := by
  rw [penalty, add_eq_zero_iff_of_nonneg (expNegInvGlue.nonneg _)
    (expNegInvGlue.nonneg _), expNegInvGlue.zero_iff_nonpos,
    expNegInvGlue.zero_iff_nonpos, neg_nonpos, neg_nonpos]

/-- The feasible set of the constraints `ConnGouldToint.Chapter12.ConstraintExample.constraints` is
the quadrant in the first two coordinates: for $z \in \mathbb{R}^3$,
$$c_0(z) \ge 0 \text{ and } c_1(z) \ge 0 \iff z_0 \ge 0 \text{ and } z_1 \ge 0.$$
This supports the counterexample to Theorem 12.3.8 of [conn2000trust]. -/
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

/-- If $z_2 \ge -1/4$, then the constraints of the counterexample to Theorem 12.3.8 of
[conn2000trust] are the coordinates: $c_0(z) = z_0$ and $c_1(z) = z_1$. -/
theorem constraints_of_height_ge (z : Space) (hz : -(1 / 4 : ℝ) ≤ z 2) :
    constraints 0 z = z 0 ∧ constraints 1 z = z 1 := by
  have ha : firstCut z = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  have hb : secondCut z = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  norm_num [constraints, ha, hb]

/-- At the remote boundary point $(0, 0, -1)$, the constraints of the counterexample to Theorem
12.3.8 of [conn2000trust] take the values $c_0 = 0$ and $c_1 = 1$. So only the first inequality
is active there. -/
theorem constraints_at_remote :
    constraints 0 (WithLp.toLp 2 ![0, 0, -1]) = 0 ∧
    constraints 1 (WithLp.toLp 2 ![0, 0, -1]) = 1 := by
  let w : Space := WithLp.toLp 2 ![0, 0, -1]
  have ha : firstCut w = 1 := Real.smoothTransition.one_of_one_le (by norm_num [w])
  have hb : secondCut w = 1 := Real.smoothTransition.one_of_one_le (by norm_num [w])
  change constraints 0 w = 0 ∧ constraints 1 w = 1
  norm_num [constraints, ha, hb, penalty, w, expNegInvGlue.zero]

/-- Both constraints $c_0$ and $c_1$ of the counterexample to Theorem 12.3.8 of [conn2000trust] are
infinitely differentiable on $\mathbb{R}^3$. -/
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

/-- At the origin, the derivatives of the constraints of the counterexample to Theorem 12.3.8 of
[conn2000trust] are the first two coordinate functionals: $Dc_0(0) = (z \mapsto z_0)$ and
$Dc_1(0) = (z \mapsto z_1)$. -/
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


/-- Both constraints of the counterexample to Theorem 12.3.8 of [conn2000trust] are active at the
origin: the active set $\{i : c_i(0) = 0\}$ is $\{0, 1\}$. -/
theorem active_at_zero : activeConstraintSet constraints (0 : Space) = univ := by
  have h := constraints_of_height_ge (0 : Space) (by norm_num [PiLp.zero_apply])
  ext i
  fin_cases i <;> simp [activeConstraintSet, h.1, h.2, PiLp.zero_apply]

/-- At the remote point $(0, 0, -1)$, the active set of the constraints of the counterexample to
Theorem 12.3.8 of [conn2000trust] is $\{0\}$. -/
theorem active_at_remote :
    activeConstraintSet constraints (WithLp.toLp 2 ![0, 0, -1]) = {0} := by
  ext i
  fin_cases i <;> simp [activeConstraintSet, constraints_at_remote.1, constraints_at_remote.2]

/-- At the remote point $(0, 0, -1)$, the derivative of the only active constraint $c_0$ of the
counterexample to Theorem 12.3.8 of [conn2000trust] is zero. So the active gradient there is
degenerate. -/
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

/-- At the origin, the gradients of the constraints of the counterexample to Theorem 12.3.8 of
[conn2000trust] are the first two standard basis vectors: $\nabla c_0(0) = e_0$ and
$\nabla c_1(0) = e_1$. These are the inward normals of the quadrant. -/
theorem gradient_constraints_zero (i : Fin 2) :
    gradient (constraints i) 0 = EuclideanSpace.single (Fin.castLE (by decide : 2 ≤ 3) i) 1 := by
  have hf (j : Fin 2) :
      fderiv ℝ (constraints j) 0 = coordinate (Fin.castLE (by decide : 2 ≤ 3) j) := by
    fin_cases j
    · exact fderiv_constraints_zero.1
    · exact fderiv_constraints_zero.2
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, hf, EuclideanSpace.inner_single_left]
  simp [coordinate]

/-- At the origin, the gradients of the active constraints of the counterexample to Theorem 12.3.8
of [conn2000trust] are linearly independent. -/
theorem independent_active_at_zero :
    LinearIndependent ℝ (fun i : activeConstraintSet constraints (0 : Space) ↦
      gradient (constraints i) 0) := by
  simp only [gradient_constraints_zero]
  apply (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)).linearIndependent.comp
  intro i j h
  apply Subtype.ext
  exact Fin.ext (congrArg (fun v : Fin 3 ↦ v.val) h)

/-- At the origin, the vector $g = (1, 1, 0)$ has strictly positive multipliers on the active
constraints of the counterexample to Theorem 12.3.8 of [conn2000trust]: $g = 1 \cdot \nabla
c_0(0) + 1 \cdot \nabla c_1(0)$, in the sense of
`ConnGouldToint.Chapter12.HasStrictActiveMultipliers` for the constant field $g$. -/
theorem strict_multipliers_at_zero :
    HasStrictActiveMultipliers constraints (fun i ↦ gradient (constraints i))
      (fun _ ↦ (WithLp.toLp 2 ![1, 1, 0] : Space)) 0 := by
  refine ⟨fun _ ↦ 1, ?_, fun _ _ ↦ zero_lt_one, ?_⟩
  · ext j
    fin_cases j <;> simp [Fin.sum_univ_two, gradient_constraints_zero,
      PiLp.add_apply]
  · simp [active_at_zero]

open Optimization in
/-- The quadrant $Q = \{v \in \mathbb{R}^3 : v_0 \ge 0, v_1 \ge 0\}$ satisfies the geometric strict
complementarity condition AO.4b of [conn2000trust] at the origin for the gradient $(1, 1, 0)$:
the vector $-(1, 1, 0)$ lies in the relative interior of the normal cone of $Q$ at $0$. This
supports the counterexample to Theorem 12.3.8.

The normal cone is `Optimization.normalDirections` and the relative interior is
`intrinsicInterior ℝ`. -/
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
