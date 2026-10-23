import Mathlib.Order.Filter.Extr
import Mathlib.Algebra.Group.Basic

/-!
# Restricting a modified objective to a feasible set

If a correction vanishes on the feasible points, minimizing the corrected objective on
an ambient set suffices to minimize the original objective on its feasible subset.
No smoothness, convexity or topology is needed.
-/

namespace Constrained

/-- A minimizer of `f - price ∘ c` minimizes `f` on the zero fiber of `c`, whenever
`price 0 = 0` and the minimizer itself is feasible. -/
theorem isMinOn_of_sub_comp_eq_zero {E F β : Type*} [Zero F] [AddGroup β] [Preorder β]
    {f : E → β} {c : E → F} {price : F → β} {S : Set E} {x : E}
    (hprice : price 0 = 0) (hc : c x = 0)
    (hmin : IsMinOn (fun z => f z - price (c z)) S x) :
    IsMinOn f {z ∈ S | c z = 0} x := by
  intro z hz
  have h := hmin hz.1
  simpa [hc, hz.2, hprice] using h

end Constrained
