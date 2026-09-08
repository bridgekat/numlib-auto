import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Subspace

/-!
# Krylov subspaces of a matrix

The one lemma that reads a Krylov subspace of `Matrix.toEuclideanLin A` as the span of the columns
`A^i v`, `i < m`, which is how every matrix-level statement of a Krylov method meets the backbone
definition `Krylov.subspace`.

It lives here, and not in `Numlib.Analysis.Matrix.ToEuclideanLin`, because that module is an
upstreaming candidate and so may not depend on `Numlib.Krylov.Subspace`; and not in
`Numlib.Krylov.Subspace`, because the Krylov layer imports the matrix glue rather than the other
way round. This module is the meet of the two.
-/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Krylov subspaces of a matrix are spanned by the columns `A^i v`. -/
theorem krylov_subspace_toEuclideanLin (A : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) (m : ℕ) :
    Krylov.subspace (toEuclideanLin A) v m =
      Submodule.span 𝕜 (Set.range fun i : Fin m => toEuclideanLin (A ^ (i : ℕ)) v) := by
  simp only [Krylov.subspace, toEuclideanLin_pow]

end Matrix
