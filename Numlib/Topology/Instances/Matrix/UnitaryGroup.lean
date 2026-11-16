/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.Instances.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix

/-!
# Compactness of the unitary and orthogonal groups

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ (any `RCLike` field). This file proves that the
unitary group $U(n) = \{U \in \mathbb{K}^{n \times n} : U^H U = U U^H = I\}$ is compact. It is
closed, because it is the preimage of $I$ under the continuous maps $U \mapsto U^H U$ and
$U \mapsto U U^H$. Its entries have modulus at most $1$, because its columns are unit vectors. So it
is a closed subset of a compact product of closed unit balls. The orthogonal group is the real case.
Compactness lets limiting arguments extract convergent subsequences of unitary or orthogonal
factors, as in the proofs of the generalized and periodic Schur forms of singular pencils.

## Main results

* `Matrix.isClosed_unitaryGroup`: the unitary group is closed.
* `Matrix.norm_apply_le_one_of_mem_unitaryGroup`: the entries of a unitary matrix have modulus at
  most $1$.
* `Matrix.isCompact_unitaryGroup`: the unitary group is compact.
* `Matrix.isClosed_orthogonalGroup`: the orthogonal group is closed.
* `Matrix.abs_apply_le_one_of_mem_orthogonalGroup`: the entries of an orthogonal matrix have
  absolute value at most $1$.
* `Matrix.isCompact_orthogonalGroup`: the orthogonal group is compact.

## Implementation notes

* The groups are `Matrix.unitaryGroup n 𝕜` and `Matrix.orthogonalGroup n ℝ`, seen as subsets of
  `Matrix n n 𝕜` with the product topology on the entries. The index type $n$ is finite.
-/

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, the unitary group is a closed subset of
$\mathbb{K}^{n \times n}$. It is the set of matrices $U$ with $U^H U = I$ and $U U^H = I$, and
the maps $U \mapsto U^H U$ and $U \mapsto U U^H$ are continuous.

The proof is Mathlib's `isClosed_unitary`. -/
theorem isClosed_unitaryGroup :
    IsClosed ((unitaryGroup n 𝕜 : Submonoid _) : Set (Matrix n n 𝕜)) :=
  isClosed_unitary

/-- Over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, every entry of a unitary matrix
$U \in \mathbb{K}^{n \times n}$ satisfies $|U_{ij}| \le 1$, because the columns of $U$ are unit
vectors.

This is Mathlib's `entry_norm_bound_of_unitary`, restated under a name that follows the Mathlib
naming convention. -/
theorem norm_apply_le_one_of_mem_unitaryGroup {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜)
    (i j : n) : ‖U i j‖ ≤ 1 :=
  entry_norm_bound_of_unitary hU i j

/-- **The unitary group is compact.** Over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, the unitary
group is a compact subset of $\mathbb{K}^{n \times n}$.

The group is closed (`Matrix.isClosed_unitaryGroup`) and lies in the product of the closed unit
balls of $\mathbb{K}$, one for each entry (`Matrix.norm_apply_le_one_of_mem_unitaryGroup`). The
real case is `Matrix.isCompact_orthogonalGroup`. -/
theorem isCompact_unitaryGroup :
    IsCompact ((unitaryGroup n 𝕜 : Submonoid _) : Set (Matrix n n 𝕜)) := by
  have hcube : IsCompact (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : 𝕜) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hcube.of_isClosed_subset isClosed_unitaryGroup fun U hU => ?_
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => norm_apply_le_one_of_mem_unitaryGroup hU i j

/-- The orthogonal group $\{U \in \mathbb{R}^{n \times n} : U^T U = U U^T = I\}$ is a closed subset
of $\mathbb{R}^{n \times n}$. This is the real case of `Matrix.isClosed_unitaryGroup`. -/
theorem isClosed_orthogonalGroup :
    IsClosed ((orthogonalGroup n ℝ : Submonoid _) : Set (Matrix n n ℝ)) :=
  isClosed_unitaryGroup

/-- Every entry of an orthogonal matrix $U \in \mathbb{R}^{n \times n}$ satisfies $|U_{ij}| \le 1$,
because the columns of $U$ are unit vectors. This is the real case of
`Matrix.norm_apply_le_one_of_mem_unitaryGroup`. -/
theorem abs_apply_le_one_of_mem_orthogonalGroup {U : Matrix n n ℝ}
    (hU : U ∈ orthogonalGroup n ℝ) (i j : n) : |U i j| ≤ 1 :=
  Real.norm_eq_abs (U i j) ▸ norm_apply_le_one_of_mem_unitaryGroup hU i j

/-- **The orthogonal group is compact.** The orthogonal group is a compact subset of
$\mathbb{R}^{n \times n}$. This is the real case of `Matrix.isCompact_unitaryGroup`. -/
theorem isCompact_orthogonalGroup :
    IsCompact ((orthogonalGroup n ℝ : Submonoid _) : Set (Matrix n n ℝ)) :=
  isCompact_unitaryGroup

end Matrix
