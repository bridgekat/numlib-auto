import Numlib.Optimization.Subproblem.Model
import Numlib.Analysis.InnerProductSpace.BoxProjection
import Mathlib.Data.Finset.Sort

/-! # The generalized Cauchy point on a box -/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter17

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic model (17.3.1), including its constant term. -/
noncomputable def cauchyQuadratic (f : ℝ) (g : E) (H : E →L[ℝ] E) (s : E) : ℝ :=
  f + Subproblem.quadModel g H s

/-- The projected Cauchy path (17.3.2) for a box in displacement coordinates. -/
noncomputable def projectedCauchyPath {ι : Type*} [Fintype ι] (l u : ι → EReal)
    (d : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
  bestApprox (euclideanBox l u) (t • d)

/-- The affine segment (17.3.3) after a breakpoint. -/
def cauchySegment (s d : E) (t : ℝ) : E :=
  s + t • d

/-- The expansion (17.3.4)–(17.3.5) along an affine segment. -/
theorem cauchyQuadratic_on_segment (f : ℝ) (g s d : E) {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (t : ℝ) :
    cauchyQuadratic f g H (cauchySegment s d t) =
      cauchyQuadratic f g H s + t * (⟪g, d⟫ + ⟪s, H d⟫) +
        (1 / 2 : ℝ) * t ^ 2 * ⟪d, H d⟫ := by
  have hcross : ⟪d, H s⟫ = ⟪s, H d⟫ := (hH d s).symm.trans (real_inner_comm _ _)
  simp only [cauchyQuadratic, cauchySegment, Subproblem.quadModel_def, map_add, map_smul,
    inner_add_right, inner_add_left, inner_smul_right, real_inner_smul_left, hcross]
  ring

/-- A coordinate breakpoint in Algorithm 17.3.1. The bounds are relative
to the base point, and the radius clips them to finite real values. -/
noncomputable def boxedCauchyBreakpoint (l u : EReal) (Δ d : ℝ) : ℝ :=
  if 0 < d then (min u (Δ : EReal)).toReal / d
  else if d < 0 then (max l ((-Δ : ℝ) : EReal)).toReal / d
  else 0

/-- A zero slope with strictly negative curvature gives a strict decrease
on the outgoing segment, so Step 3 must continue in this case. -/
theorem cauchyQuadratic_lt_on_negative_stationary_segment (f : ℝ) (g s d : E)
    {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (hSlope : ⟪g, d⟫ + ⟪s, H d⟫ = 0) (hCurv : ⟪d, H d⟫ < 0)
    {t : ℝ} (ht : t ≠ 0) :
    cauchyQuadratic f g H (cauchySegment s d t) < cauchyQuadratic f g H s := by
  rw [cauchyQuadratic_on_segment f g s d hH, hSlope, mul_zero, add_zero]
  exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg (by positivity) hCurv)

private noncomputable def cauchyFrozenDirection {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (d : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if b i = t then d i else 0

private noncomputable def cauchyScan {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (g d : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    List ℝ → ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → ℝ →
      EuclideanSpace ℝ ι → ℝ × EuclideanSpace ℝ ι
  | [], t, s, _, _, _ => (t, s)
  | next :: tail, t, s, v, gv, Hv =>
    let slope := gv + ⟪s, Hv⟫
    let curvature := ⟪v, Hv⟫
    let step := -slope / curvature
    if 0 < slope ∨ (slope = 0 ∧ 0 ≤ curvature) then (t, s)
    else if 0 < curvature ∧ step < next - t then
      (t + step, cauchySegment s v step)
    else
      let e := cauchyFrozenDirection b d next
      cauchyScan b g d H tail next (cauchySegment s v (next - t))
        (v - e) (gv - ⟪g, e⟫) (Hv - H e)

/-- Corrected Algorithm 17.3.1 on a box containing the zero displacement.
The first component is the parameter at the returned point. Equal
breakpoints are grouped, and the terminal constant interval returns its
left endpoint without requesting another breakpoint. A zero slope stops
only if the outgoing curvature is nonnegative. -/
noncomputable def generalizedCauchyPoint {ι : Type*} [Fintype ι]
    (l u : ι → EReal) (Δ : ℝ) (g d : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    ℝ × EuclideanSpace ℝ ι :=
  let b := fun i ↦ boxedCauchyBreakpoint (l i) (u i) Δ (d i)
  let times := (Finset.univ.image b).filter (fun t ↦ 0 < t)
  let v := d - cauchyFrozenDirection b d 0
  cauchyScan b g d H times.sort 0 0 v ⟪g, v⟫ (H v)

/-- With no positive breakpoint the initial interval is already terminal. -/
theorem generalizedCauchyPoint_eq_zero_of_no_positive_breakpoint {ι : Type*} [Fintype ι]
    (l u : ι → EReal) (Δ : ℝ) (g d : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hb : ∀ i, boxedCauchyBreakpoint (l i) (u i) Δ (d i) ≤ 0) :
    generalizedCauchyPoint l u Δ g d H = (0, 0) := by
  unfold generalizedCauchyPoint
  have hempty : ((Finset.univ.image (fun i ↦ boxedCauchyBreakpoint (l i) (u i) Δ (d i))).filter
      (fun t ↦ 0 < t)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨h, hpos⟩ := Finset.mem_filter.mp ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact (hb i).not_gt hpos
  simp [hempty, cauchyScan]

/-- The radius-zero trust box returns the initial displacement, even when
the search direction itself is nonzero. -/
theorem generalizedCauchyPoint_zero_radius {ι : Type*} [Fintype ι]
    (l u : ι → EReal) (g d : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hl : ∀ i, l i ≤ 0) (hu : ∀ i, 0 ≤ u i) :
    generalizedCauchyPoint l u 0 g d H = (0, 0) := by
  apply generalizedCauchyPoint_eq_zero_of_no_positive_breakpoint
  intro i
  simp [boxedCauchyBreakpoint, min_eq_right (hu i), max_eq_right (hl i)]

end ConnGouldToint.Chapter17
