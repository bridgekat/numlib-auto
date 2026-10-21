import Numlib.Optimization.Constrained

/-!
# Restricting Lagrangian minimizers to the feasible set

The equality Lagrangian agrees with the objective on the feasible set, so any of its global
or local minimizers restricts to an objective minimizer there. No regularity is required.
-/

open Set Filter Topology

namespace Constrained

variable {E ι : Type*} [Fintype ι] {f : E → ℝ} {h : ι → E → ℝ}
  {S : Set E} {x : E} {l : ι → ℝ}

/-- A Lagrangian minimizer satisfying the equalities minimizes the objective on their
intersection with the original minimizing set. -/
theorem isMinOn_of_isMinOn_lagrangian (hx : x ∈ feasibleEq h)
    (hmin : IsMinOn (fun z => lagrangian f h z l) S x) :
    IsMinOn f (S ∩ feasibleEq h) x := by
  intro z hz
  have hm : lagrangian f h x l ≤ lagrangian f h z l := hmin hz.1
  rw [lagrangian_eq_of_mem hx l, lagrangian_eq_of_mem hz.2 l] at hm
  exact hm

/-- Local Lagrangian minimizers likewise restrict to objective minimizers on the feasible
subset, without closedness or differentiability hypotheses. -/
theorem isLocalMinOn_of_isLocalMinOn_lagrangian [TopologicalSpace E]
    (hx : x ∈ S ∩ feasibleEq h)
    (hmin : IsLocalMinOn (fun z => lagrangian f h z l) S x) :
    IsLocalMinOn f (S ∩ feasibleEq h) x := by
  apply (hmin.mono inter_subset_left).congr ?_ hx
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact lagrangian_eq_of_mem hz.2 l

end Constrained
