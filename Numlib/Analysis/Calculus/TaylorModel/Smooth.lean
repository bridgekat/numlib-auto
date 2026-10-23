import Numlib.Analysis.Calculus.TaylorModel
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of finite Taylor polynomials

A finite multilinear jet defines a smooth polynomial regardless of compatibility
with derivatives of an underlying function.
-/

open scoped ContDiff
namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every finite jet polynomial is smooth to arbitrary order, independently
of whether its supplied coefficients are derivatives of a function. -/
theorem contDiff_ofJet (A : FormalMultilinearSeries ℝ E F) (p : ℕ) (n : ℕ∞ω) :
    ContDiff ℝ n (ofJet A p) := by
  have heq : ofJet A p = fun s => ∑ i ∈ Finset.range (p + 1),
      ((i.factorial : ℝ)⁻¹) • A i (fun _ => s) := funext (ofJet_eq_sum A p)
  rw [heq]
  apply ContDiff.sum
  intro i hi
  apply ContDiff.const_smul
  exact (A i).contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_id))

/-- An actual finite Taylor polynomial is smooth in its displacement even when
no regularity of its coefficient-generating function is postulated. -/
theorem contDiff_eval (f : E → F) (p : ℕ) (x : E) (n : ℕ∞ω) :
    ContDiff ℝ n (eval f p x) := contDiff_ofJet _ _ _

end TaylorModel
