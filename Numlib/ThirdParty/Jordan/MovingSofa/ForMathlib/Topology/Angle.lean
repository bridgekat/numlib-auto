/-
Vendored from Dean Cureton and contributors, https://github.com/deancureton/MovingSofa,
revision 4d5569131940815f47a9ccf3e90a4c5043c56127, path MovingSofa/ForMathlib/Topology/Angle.lean.
The original work is distributed under Apache-2.0.
Local changes are documented in Attribution.md.
-/
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

open scoped unitInterval

namespace Real.Angle

/-- A continuous angle path starting at zero has a continuous real lift starting at zero. -/
theorem exists_continuous_lift_zero (θ : I → Real.Angle) (hθ : Continuous θ)
    (hzero : θ 0 = 0) :
    ∃ α : I → ℝ, Continuous α ∧ α 0 = 0 ∧ ∀ t, (α t : Real.Angle) = θ t := by
  have hcov : IsCoveringMap ((↑) : ℝ → Real.Angle) := AddCircle.isCoveringMap_coe (2 * Real.pi)
  obtain ⟨α, hα, hα0⟩ := hcov.exists_path_lifts
    (⟨θ, hθ⟩ : C(I, Real.Angle)) (0 : ℝ) (by simpa using hzero)
  exact ⟨α, α.continuous, hα0, fun t ↦ congrFun hα t⟩

end Real.Angle
