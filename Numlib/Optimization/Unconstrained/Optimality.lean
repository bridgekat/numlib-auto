import Numlib.Optimization.Descent
import Numlib.Analysis.Calculus.LocalExtr.ThirdOrder
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Tactic

/-!
# Higher-order necessary and sufficient optimality conditions

Affine-line restrictions identify second and third scalar derivatives with the Hessian
and third derivative tensor. At a local minimum, the third tensor vanishes in directions
where the Hessian quadratic form vanishes. In finite-dimensional inner product spaces,
positive definiteness of the actual Hessian yields coercivity and a strict local minimum.
All derivatives are the Fréchet derivatives of the specified function.
-/

open Set Filter Topology

namespace Descent

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second derivative along an affine line is the Hessian applied twice to its direction. -/
theorem iteratedDeriv_two_affineLine {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have hline : ContDiff ℝ 2 (fun t : ℝ => x + t • v) := by fun_prop
  have hd : deriv (fun t : ℝ => x + t • v) 0 = v := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x).deriv
  have htwo : iteratedDeriv 2 (fun t : ℝ => x + t • v) 0 = 0 := by
    rw [iteratedDeriv_const_add (by decide), iteratedDeriv_smul_const contDiff_id.contDiffAt]
    simp [iteratedDeriv_succ]
  have h := iteratedDeriv_vcomp_two (g := f) (f := fun t : ℝ => x + t • v)
    (x := 0) (by simpa using hf.contDiffAt) hline.contDiffAt
  simpa [Function.comp_def, hd, htwo, iteratedFDeriv_two_apply] using h

/-- The third derivative along an affine line is the third derivative tensor applied
three times to its direction. -/
theorem iteratedDeriv_three_affineLine {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x v : E) :
    iteratedDeriv 3 (fun t : ℝ => f (x + t • v)) 0 =
      iteratedFDeriv ℝ 3 f x (fun _ => v) := by
  have hline : ContDiff ℝ 3 (fun t : ℝ => x + t • v) := by fun_prop
  have h := iteratedDeriv_vcomp_three (g := f) (f := fun t : ℝ => x + t • v)
    (x := 0) (by simpa using hf.contDiffAt) hline.contDiffAt
  have hd : deriv (fun t : ℝ => x + t • v) 0 = v := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x).deriv
  have htwo : iteratedDeriv 2 (fun t : ℝ => x + t • v) 0 = 0 := by
    rw [iteratedDeriv_const_add (by decide), iteratedDeriv_smul_const contDiff_id.contDiffAt]
    simp [iteratedDeriv_succ]
  have hthree : iteratedDeriv 3 (fun t : ℝ => x + t • v) 0 = 0 := by
    rw [iteratedDeriv_const_add (by decide), iteratedDeriv_smul_const contDiff_id.contDiffAt]
    simp [iteratedDeriv_succ]
  have hzleft : iteratedFDeriv ℝ 2 f x ![0,v] = 0 :=
    (iteratedFDeriv ℝ 2 f x).map_coord_zero (i := 0) (by simp)
  have hzright : iteratedFDeriv ℝ 2 f x ![v,0] = 0 :=
    (iteratedFDeriv ℝ 2 f x).map_coord_zero (i := 1) (by simp)
  simpa [Function.comp_def, hd, htwo, hthree, hzleft, hzright] using h

/-- At a local minimum of a `C³` function, the third directional derivative
vanishes in any direction where the Hessian quadratic form vanishes. -/
theorem third_apply_eq_zero_of_isLocalMin {f : E → ℝ} {x : E}
    (hmin : IsLocalMin f x) (hf : ContDiff ℝ 3 f) (v : E)
    (hv : fderiv ℝ (fderiv ℝ f) x v v = 0) :
    iteratedFDeriv ℝ 3 f x (fun _ => v) = 0 := by
  have hline : ContDiff ℝ 3 (fun t : ℝ => x + t • v) := by fun_prop
  have hmline : IsLocalMin (fun t : ℝ => f (x + t • v)) 0 := by
    simpa [Function.comp_def] using
      (show IsLocalMin f (x + (0 : ℝ) • v) by simpa using hmin).comp_continuous
        (g := fun t : ℝ => x + t • v) (b := 0)
        hline.continuous.continuousAt
  have hfline : ContDiff ℝ 3 (fun t : ℝ => f (x + t • v)) := hf.comp hline
  have hsline : iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 = 0 := by
    rw [iteratedDeriv_two_affineLine (hf.of_le (by norm_num)) x v, hv]
  rw [← iteratedDeriv_three_affineLine hf x v]
  exact hmline.iteratedDeriv_three_eq_zero hfline hsline

/-- The `C²` form of the second-order necessary condition, using the actual Hessian. -/
theorem hessian_nonneg_of_isLocalMin {f : E → ℝ} {x : E}
    (hmin : IsLocalMin f x) (hf : ContDiff ℝ 2 f) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  exact nonneg_apply_apply_of_isLocalMin hmin
    (Filter.Eventually.of_forall (fun y => (hf.differentiable (by norm_num) y).hasFDerivAt))
    (((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable
      (by norm_num) x).hasFDerivAt) v
end Normed

section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A positive definite continuous bilinear form in finite dimension has a uniform
positive lower bound on the squared norm. -/
theorem exists_pos_mul_sq_norm_le (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v ≠ 0, 0 < H v v) :
    ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ H v v := by
  let A : E →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.comp H
  have hA (v : E) : inner ℝ (A v) v = H v v := by simp [A]
  have hcoer : (A : E →ₗ[ℝ] E).IsCoercive :=
    (LinearMap.isCoercive_iff_forall_pos _).mpr (by simpa [hA] using hpos)
  obtain ⟨c,hc,hbound⟩ := hcoer
  refine ⟨c,hc,?_⟩
  intro v
  simpa [LinearMap.IsCoerciveWith, hA] using hbound v

/-- The positive definite Hessian test for a strict local minimum in finite dimension. -/
theorem strict_local_min_of_pos_hessian {f : E → ℝ} {x : E}
    (hf : ContDiff ℝ 2 f) (hcrit : fderiv ℝ f x = 0)
    (hpos : ∀ v ≠ 0, 0 < fderiv ℝ (fderiv ℝ f) x v v) :
    ∃ δ > 0, ∀ y ∈ Metric.ball x δ, y ≠ x → f x < f y := by
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hf'' : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := hf'.fderiv_right (by norm_num)
  obtain ⟨c,hc,hbound⟩ := exists_pos_mul_sq_norm_le (fderiv ℝ (fderiv ℝ f) x) hpos
  exact isLocalMin_of_coercive_second (r := 1) (by norm_num) hc
    (fun y _ => (hf.differentiable (by norm_num) y).hasFDerivAt)
    (fun y _ => (hf'.differentiable (by norm_num) y).hasFDerivAt)
    hf''.continuous.continuousAt hcrit hbound
end FiniteDimensional
end Descent
