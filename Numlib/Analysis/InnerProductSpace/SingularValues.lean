/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.SingularValues`, beside Mathlib's
`LinearMap.singularValues`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Singular values of a linear map

Facts about Mathlib's `LinearMap.singularValues` of a linear map `T : E →ₗ[𝕜] F` between
finite-dimensional inner product spaces, and about the sorted orthonormal eigenbasis of `T† T` they
are read from, stated coordinate-free. Mathlib's `LinearMap.singularValues` is the `ℕ`-indexed
sequence of the square roots of the eigenvalues of `T† T`, sorted decreasingly and zero from
`finrank E` on.

## Main results

* `LinearMap.IsSymmetric.eigenvalues_eq_of_antitone`: the sorted eigenvalues of a symmetric
  operator are determined by its characteristic polynomial — an antitone list whose values are the
  roots is the list of sorted eigenvalues. It is how a spectrum computed in any orthonormal
  basis is recognized as `LinearMap.IsSymmetric.eigenvalues`.
* `LinearMap.inner_apply_eigenvectorBasis_adjoint_comp_self` and
  `LinearMap.norm_apply_eigenvectorBasis_adjoint_comp_self`: `T` maps the sorted eigenbasis `v` of
  `T† T` to a pairwise orthogonal family with `‖T v_j‖ = σ_j`, the half of the singular value
  decomposition that needs no completion.
* `LinearMap.singularValues_of_finrank_codomain_le`: the singular values also vanish from the
  dimension of the codomain on.

## Implementation notes

The module is the coordinate-free rung of the library's singular-value theory: it imports nothing
from the matrix layer, and the matrix singular value decomposition
(`Numlib/LinearAlgebra/Matrix/SVD`) imports it.
-/

open Module

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The sorted eigenvalues of a symmetric operator are determined by its characteristic
polynomial**: if the roots of `T.charpoly` are the values of an antitone `d : Fin n → ℝ`, then
`hT.eigenvalues hn = d`. This is `LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues` read
backwards. -/
theorem IsSymmetric.eigenvalues_eq_of_antitone {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) {n : ℕ} (hn : finrank 𝕜 E = n) {d : Fin n → ℝ} (hd : Antitone d)
    (hroots : T.charpoly.roots = Multiset.map (RCLike.ofReal ∘ d) Finset.univ.val) :
    hT.eigenvalues hn = d := by
  rw [← List.ofFn_inj, ← hT.sort_roots_charpoly_eq_eigenvalues hn, hroots]
  simp_rw [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Function.comp_def, RCLike.ofReal_re,
    Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hd.sortedGE_ofFn

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- The images under `T` of the sorted orthonormal eigenbasis of `T† T` are pairwise orthogonal,
with squared norms the squared singular values. -/
theorem inner_apply_eigenvectorBasis_adjoint_comp_self {n : ℕ} (hn : finrank 𝕜 E = n)
    (i j : Fin n) :
    inner 𝕜 (T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i))
        (T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j))
      = if i = j then ((T.singularValues j ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [← adjoint_inner_right, ← comp_apply, T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis,
    inner_smul_right,
    orthonormal_iff_ite.1 (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).orthonormal i j,
    ← T.sq_singularValues_fin hn j]
  split_ifs <;> simp

/-- The image under `T` of the `j`-th vector of the sorted eigenbasis of `T† T` has norm the `j`-th
singular value. -/
theorem norm_apply_eigenvectorBasis_adjoint_comp_self {n : ℕ} (hn : finrank 𝕜 E = n) (j : Fin n) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j)‖ = T.singularValues j := by
  have h := T.inner_apply_eigenvectorBasis_adjoint_comp_self hn j j
  rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j)‖ ^ 2
      = T.singularValues j ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (T.singularValues_nonneg j) two_ne_zero).1 h2

/-- The singular values vanish from the dimension of the *codomain* on, as they do from the
dimension of the domain on (`LinearMap.singularValues_of_finrank_le`): only `rank T` of them are
nonzero. -/
theorem singularValues_of_finrank_codomain_le {i : ℕ} (hi : finrank 𝕜 F ≤ i) :
    T.singularValues i = 0 :=
  T.singularValues_eq_zero_iff_le_finrank_range.2 ((Submodule.finrank_le _).trans hi)

end LinearMap
