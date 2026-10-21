import Numlib.Optimization.Constrained
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Derivatives of quadratic penalties and logarithmic barriers

Quadratic penalties and augmented Lagrangians use the existing bundled objective
definitions. The finite logarithmic barrier keeps its positive domain explicit.
-/

noncomputable section
namespace Constrained

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {f : E → ℝ} {c : E → F} {x : E} {f' : E →L[ℝ] ℝ} {c' : E →L[ℝ] F}

/-- The derivative of a quadratic penalty uses the actual constraint residual. -/
theorem penalized_hasFDerivAt (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x)
    (a : ℝ) : HasFDerivAt (penalized f c a)
      (f' + a • (innerSL ℝ (c x)).comp c') x := by
  convert hf.add (hc.norm_sq.const_mul (1 / 2 * a)) using 1
  · rfl
  · ext v
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring

/-- The augmented Lagrangian derivative combines its multiplier and penalty residual. -/
theorem augmented_hasFDerivAt (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x)
    (a : ℝ) (l : F) : HasFDerivAt (augmented f c a l)
      (f' + (innerSL ℝ (l + a • c x)).comp c') x := by
  have hi := (innerSL ℝ l).hasFDerivAt.comp x hc
  convert (hf.add hi).add (hc.norm_sq.const_mul (1 / 2 * a)) using 1
  · rfl
  · ext v
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      inner_add_left, real_inner_smul_left, smul_eq_mul]
    ring

section Barrier
variable {ι : Type*} [Fintype ι]

/-- The strict domain of a finite family of logarithmic barriers. -/
def barrierDomain (g : ι → E → ℝ) : Set E := {x | ∀ i, 0 < g i x}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] in
/-- Membership exposes every strict scalar domain condition. -/
@[simp] theorem mem_barrierDomain {g : ι → E → ℝ} :
    x ∈ barrierDomain g ↔ ∀ i, 0 < g i x := Iff.rfl

/-- A logarithmic barrier with the minus multiplier convention. Its mathematical domain
is `barrierDomain g`, even though the real logarithm has a totalized Lean definition. -/
def logarithmicBarrier (f : E → ℝ) (g : ι → E → ℝ) (a : ℝ) (x : E) : ℝ :=
  f x - a * ∑ i, Real.log (g i x)

/-- On its strict domain the barrier derivative is the corresponding Lagrangian derivative. -/
theorem logarithmicBarrier_hasFDerivAt (hf : HasFDerivAt f f' x)
    {g : ι → E → ℝ} {g' : ι → E →L[ℝ] ℝ}
    (hg : ∀ i, HasFDerivAt (g i) (g' i) x) (hx : x ∈ barrierDomain g) (a : ℝ) :
    HasFDerivAt (logarithmicBarrier f g a)
      (f' - ∑ i, (a / g i x) • g' i) x := by
  have hl : ∀ i, HasFDerivAt (fun z => Real.log (g i z))
      ((g i x)⁻¹ • g' i) x := fun i => (hg i).log (ne_of_gt (hx i))
  convert hf.sub ((HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hl i).const_mul a)
    using 1
  · rfl
  · simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv]

end Barrier
end Constrained
