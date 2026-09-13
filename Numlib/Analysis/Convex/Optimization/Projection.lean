import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Optimization.Minimum
import Numlib.Analysis.Convex.Optimization.Prox
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.Analysis.Normed.Module.BestApprox

/-!
# The metric projection onto a convex set as a proximal mapping

The bridge between `IsBestApprox K u v` of `Numlib/Analysis/Normed/Module/BestApprox` — `v ∈ K`
minimises `‖u - ·‖` over `K`, in any seminormed space — and the convex-analytic reading of the same
point in a real inner-product space: `v` is the projection of `u` onto the convex `K` exactly when
`u - v` is normal to `K` at `v`, and, for `K` closed and `V` finite-dimensional, exactly when `v`
is the proximal point of `u` for the indicator function `δ(· | K)`. Neither notion subsumes the
other — `IsBestApprox` lives in every (semi)normed space and every dimension, `prox` is defined for
every closed proper convex function — so both stay and this module is their dictionary.

## Main results

* `isBestApprox_iff_sub_mem_normalCone` — for convex `K`, `IsBestApprox K u v ↔ v ∈ K ∧
  u - v ∈ N_K(v)`, the normal cone taken for the pairing `innerₗ V`. This is
  `isBestApprox_iff_inner_le_zero`, `⟪u - v, w - v⟫ ≤ 0` for all `w ∈ K`, read as a set
  membership.
* `isBestApprox_iff_prox_eq` — for `K` nonempty, closed and convex in a finite-dimensional real
  inner-product space, `IsBestApprox K u v ↔ prox (innerₗ V) (indicatorFn K) u = v`: the metric
  projection is the proximal mapping of the indicator. It is `prox_eq_iff`, `prox (u | δ_K) = v ↔
  u - v ∈ ∂δ_K(v)`, together with `∂δ_K(v) = N_K(v)` at points of `K`.

The projection theorem of Hilbert space — existence and uniqueness of the best approximation from a
nonempty closed convex set — is Mathlib's `exists_norm_eq_iInf_of_complete_convex`; the
finite-dimensional hypothesis here comes from `prox`, whose attainment argument is
finite-dimensional, not from the projection.

Sources: [rockafellar1970convex] §27 (the nearest-point problem as the first application of
Theorem 27.4: `a - x` is normal to `C` at `x`) and §31 (the remark following Theorem 31.5: for the
indicator of a nonempty closed convex set `C`, `prox (z | f)` is the point of `C` nearest to `z`);
Atkinson–Han, *Theoretical Numerical Analysis*, Lemma 3.4.1.
-/

open ConvexAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {K : Set V} {u v : V}

/-- **The projection onto a convex set is characterised by a normal cone.** In a real
inner-product space, `v` is a best approximation of `u` from the convex `K` if and only if `v ∈ K`
and `u - v` is normal to `K` at `v`: `⟪w - v, u - v⟫ ≤ 0` for every `w ∈ K`. -/
theorem isBestApprox_iff_sub_mem_normalCone (hK : Convex ℝ K) :
    IsBestApprox K u v ↔ v ∈ K ∧ u - v ∈ normalCone (innerₗ V) K v := by
  constructor
  · intro h
    refine ⟨h.1, fun w hw => ?_⟩
    rw [innerₗ_apply_apply, real_inner_comm]
    exact (isBestApprox_iff_inner_le_zero hK h.1).1 h w hw
  · rintro ⟨hv, h⟩
    refine (isBestApprox_iff_inner_le_zero hK hv).2 fun w hw => ?_
    have hw' := h w hw
    rwa [innerₗ_apply_apply, real_inner_comm] at hw'

/-- **The metric projection is the proximal mapping of the indicator.** For `K` nonempty, closed
and convex in a finite-dimensional real inner-product space, `v` is a best approximation of `u`
from `K` if and only if `v` is the proximal point of `u` for `δ(· | K)`. -/
theorem isBestApprox_iff_prox_eq [FiniteDimensional ℝ V] (hK : Convex ℝ K) (hKc : IsClosed K)
    (hne : K.Nonempty) :
    IsBestApprox K u v ↔ prox (innerₗ V) (indicatorFn K) u = v := by
  rw [prox_eq_iff (closedProperConvexFn_indicatorFn hK hKc hne),
    mem_subdifferential_indicatorFn_iff hne, isBestApprox_iff_sub_mem_normalCone hK]
