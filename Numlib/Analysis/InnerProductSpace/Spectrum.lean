/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Spectrum`, beside
`LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The sorted eigenvalues of a symmetric operator from its characteristic polynomial

Mathlib's `LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues` says that the eigenvalues
`hT.eigenvalues hn` of a symmetric operator are the sorted roots of its characteristic polynomial.
Read backwards (`LinearMap.IsSymmetric.eigenvalues_eq_of_antitone`), it identifies the eigenvalues
with any antitone list of the roots, which is how a spectrum computed by other means (for instance
the squares of the singular values from a matrix SVD) is matched with Mathlib's.
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

end LinearMap
