import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Continuous quantities near a compact minimum

A continuous quantity that vanishes at every minimizer is uniformly small near the minimum
objective value on a compact set. The minimum need not be unique.
-/

open Set

/-- On a compact set, a continuous quantity vanishing at every minimizer is uniformly small
at every point whose objective value is sufficiently close to the minimum. -/
theorem IsCompact.exists_pos_forall_lt_of_near_minimum
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {m g : X → ℝ} (hm : Continuous m) (hg : Continuous g)
    {z : X} (hmin : ∀ x ∈ K, m z ≤ m x)
    (hzero : ∀ x ∈ K, m x = m z → g x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, m x ≤ m z + η → g x < ε := by
  let B := K ∩ {x | ε ≤ g x}
  have hB : IsCompact B := hK.inter_right (isClosed_le continuous_const hg)
  by_cases hne : B.Nonempty
  · obtain ⟨y, hy, hym⟩ := hB.exists_isMinOn hne hm.continuousOn
    have hstrict : m z < m y := by
      apply lt_of_le_of_ne (hmin y hy.1)
      intro heq
      have hz := hzero y hy.1 heq.symm
      have hyε := hy.2
      change ε ≤ g y at hyε
      linarith
    refine ⟨(m y - m z) / 2, by linarith, fun x hx hxval => ?_⟩
    by_contra hxg
    have hxb : x ∈ B := ⟨hx, le_of_not_gt hxg⟩
    have : m y ≤ m x := hym hxb
    linarith
  · refine ⟨1, by norm_num, fun x hx _ => ?_⟩
    by_contra hxg
    exact hne ⟨x, hx, le_of_not_gt hxg⟩
