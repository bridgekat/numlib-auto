import Numlib.Optimization.RegularizedTaylorModel
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Linear operations on actual Taylor models

Finite Taylor sums commute with continuous linear maps and with subtraction of smooth
functions. These identities keep vector-valued constraints and scalar objectives connected
through their actual Taylor polynomials.
-/

noncomputable section
namespace Optimization.RegularizedTaylorModel
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous linear map commutes with the actual finite Taylor polynomial. -/
theorem taylorModel_comp_continuousLinearMap {f : E → F} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) (L : F →L[ℝ] G) (d : E) :
    taylorModel (L ∘ f) p x d = L (taylorModel f p x d) := by
  simp only [taylorModel, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [L.iteratedFDeriv_comp_left hf (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  rfl

/-- Subtraction of smooth functions commutes with the actual finite Taylor polynomial. -/
theorem taylorModel_sub {f g : E → F} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) (hg : ContDiffAt ℝ p g x) (d : E) :
    taylorModel (f - g) p x d = taylorModel f p x d - taylorModel g p x d := by
  simp only [taylorModel, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hip : (i : WithTop ℕ∞) ≤ p := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [iteratedFDeriv_sub_apply (hf.of_le hip) (hg.of_le hip)]
  simp only [sub_apply, smul_sub]

end Optimization.RegularizedTaylorModel
