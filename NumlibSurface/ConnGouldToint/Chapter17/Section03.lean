import Numlib.Optimization.Subproblem.Model
import Numlib.Analysis.InnerProductSpace.BoxProjection

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

end ConnGouldToint.Chapter17
