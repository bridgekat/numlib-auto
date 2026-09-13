import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.Recession.Cone

/-!
# The barrier cone and the recession cone

The **barrier cone** of a set `C` is `dom (δ*(· ∣ C))`, the set of directions in which the pairing
is bounded above on `C`. For a nonempty closed convex set it is polar to the recession cone.

## Main results

* `polarCone_dom_supportFn` — the polar of the barrier cone of a nonempty closed convex set is
  its recession cone (Corollary 14.2.1 in [^1]).

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §14.
-/

open Set

namespace ConvexAnalysis

section Barrier

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

/-- The polar of the barrier cone of a nonempty closed convex set is its recession cone.

Nonemptiness matters: for `C = ∅` the barrier cone is all of `F` and its polar is the kernel of the
pairing, while `0⁺∅` is everything. -/
theorem polarCone_dom_supportFn [IsCompatiblePairing B] (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCne : C.Nonempty) :
    polarCone B.flip (dom (supportFn B C)) = recessionCone C := by
  ext v
  constructor
  · intro hv
    rw [mem_recessionCone]
    intro x hx a ha
    have hmem : x + a • v ∈ closure (convexHull ℝ C) := by
      rw [mem_closure_convexHull_iff_le_supportFn (B := B)]
      intro y
      by_cases hy : y ∈ dom (supportFn B C)
      · have hvy : B v y ≤ 0 := hv y hy
        have hval : B (x + a • v) y = B x y + a * B v y := by
          rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
        have hle : B (x + a • v) y ≤ B x y := by
          rw [hval]
          nlinarith
        exact le_trans (by exact_mod_cast hle) (le_supportFn hx y)
      · rw [mem_dom, not_lt, top_le_iff] at hy
        rw [hy]
        exact le_top
    rwa [hC.convexHull_eq, hCcl.closure_eq] at hmem
  · intro hv y hy
    obtain ⟨x, hx⟩ := hCne
    obtain ⟨c, hc⟩ := supportFn_lt_top_iff.1 (mem_dom.1 hy)
    by_contra hcon
    have hpos : 0 < B v y := by
      have hne : ¬ (B v y ≤ 0) := hcon
      linarith [not_le.1 hne]
    set a : ℝ := (c - B x y) / (B v y) + 1 with ha
    have hmem : x + (max 0 a) • v ∈ C :=
      add_smul_mem_of_mem_recessionCone hv hx (le_max_left _ _)
    have hle := hc _ hmem
    have hval : B (x + (max 0 a) • v) y = B x y + (max 0 a) * B v y := by
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hval] at hle
    have h1 : (c - B x y) / (B v y) * B v y = c - B x y := div_mul_cancel₀ _ hpos.ne'
    have h2 : a * B v y ≤ (max 0 a) * B v y :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le
    have h3 : a * B v y = (c - B x y) + B v y := by rw [ha, add_mul, h1, one_mul]
    linarith

end Barrier

end ConvexAnalysis
