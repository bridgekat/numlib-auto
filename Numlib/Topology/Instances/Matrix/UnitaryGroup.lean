/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.Instances.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix

/-!
# Compactness of the unitary and orthogonal groups

Over `ℝ` or `ℂ` (any `RCLike` field) the unitary group `Matrix.unitaryGroup n 𝕜` of square
matrices is compact: it is closed (`Matrix.isClosed_unitaryGroup`, the preimage of `1` under
`U ↦ Uᴴ U`), and its entries lie in the closed unit ball
(`Matrix.norm_apply_le_one_of_mem_unitaryGroup`, the columns being unit vectors), so it sits in a
compact product of balls (`Matrix.isCompact_unitaryGroup`). The orthogonal group is the real case
(`Matrix.isClosed_orthogonalGroup`, `Matrix.abs_apply_le_one_of_mem_orthogonalGroup`,
`Matrix.isCompact_orthogonalGroup`).

Compactness is what lets limiting arguments extract convergent subsequences of unitary or
orthogonal factors, as in the proofs of the generalized and periodic Schur forms of singular
pencils.
-/

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The unitary group is a closed subset of the matrices: it is the preimage of `1` under the
continuous maps `U ↦ star U * U` and `U ↦ U * star U` (Mathlib's `isClosed_unitary`). -/
theorem isClosed_unitaryGroup :
    IsClosed ((unitaryGroup n 𝕜 : Submonoid _) : Set (Matrix n n 𝕜)) :=
  isClosed_unitary

/-- The entries of a unitary matrix have norm at most `1`: the columns are unit vectors. -/
theorem norm_apply_le_one_of_mem_unitaryGroup {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜)
    (i j : n) : ‖U i j‖ ≤ 1 := by
  have h := congrFun (congrFun (mem_unitaryGroup_iff'.1 hU) j) j
  rw [mul_apply, one_apply_eq] at h
  simp only [star_apply, RCLike.star_def] at h
  have hsum : ∑ k, ‖U k j‖ ^ 2 = 1 := by
    have : ((∑ k, ‖U k j‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      rw [← h]
      exact Finset.sum_congr rfl fun k _ => (RCLike.conj_mul _).symm
    exact_mod_cast this
  have hsq : ‖U i j‖ ^ 2 ≤ 1 := hsum ▸
    Finset.single_le_sum (f := fun k => ‖U k j‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg (U i j)]

/-- **The unitary group is compact**, over `ℝ` or `ℂ`: closed, and contained in the product of
closed unit balls, one for each entry. `Matrix.isCompact_orthogonalGroup` is its real case. -/
theorem isCompact_unitaryGroup :
    IsCompact ((unitaryGroup n 𝕜 : Submonoid _) : Set (Matrix n n 𝕜)) := by
  have hcube : IsCompact (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : 𝕜) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hcube.of_isClosed_subset isClosed_unitaryGroup fun U hU => ?_
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => norm_apply_le_one_of_mem_unitaryGroup hU i j

/-- The orthogonal group is a closed subset of the matrices, the real case of
`Matrix.isClosed_unitaryGroup`. -/
theorem isClosed_orthogonalGroup :
    IsClosed ((orthogonalGroup n ℝ : Submonoid _) : Set (Matrix n n ℝ)) :=
  isClosed_unitaryGroup

/-- The entries of an orthogonal matrix are bounded by `1`: the columns are unit vectors. The real
case of `Matrix.norm_apply_le_one_of_mem_unitaryGroup`. -/
theorem abs_apply_le_one_of_mem_orthogonalGroup {U : Matrix n n ℝ}
    (hU : U ∈ orthogonalGroup n ℝ) (i j : n) : |U i j| ≤ 1 :=
  Real.norm_eq_abs (U i j) ▸ norm_apply_le_one_of_mem_unitaryGroup hU i j

/-- **The orthogonal group is compact**, the real case of `Matrix.isCompact_unitaryGroup`. -/
theorem isCompact_orthogonalGroup :
    IsCompact ((orthogonalGroup n ℝ : Submonoid _) : Set (Matrix n n ℝ)) :=
  isCompact_unitaryGroup

end Matrix
