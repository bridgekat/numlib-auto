/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $T$ be a symmetric operator on a finite-dimensional inner product space $E$ of dimension $n$
over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Mathlib lists the eigenvalues of $T$ in decreasing
order as `LinearMap.IsSymmetric.eigenvalues`, and
`LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues` says that this list is the sorted list of
the roots of the characteristic polynomial of $T$. This file reads that theorem backwards: any
decreasing $d_1 \ge \dots \ge d_n$ whose values are the roots of the characteristic polynomial, with
multiplicity, is the list of eigenvalues. So a spectrum that is computed by other means, for
instance the squares of the singular values from a matrix singular value decomposition, can be
matched with the eigenvalues of Mathlib. The file also states that the eigenspaces of $T$ span $E$.

## Main results

* `LinearMap.IsSymmetric.eigenvalues_eq_of_antitone`: a decreasing list of the roots of the
  characteristic polynomial is the list of eigenvalues.
* `LinearMap.IsSymmetric.iSup_eigenspace_eq_top`: the eigenspaces of a symmetric operator span the
  space.
-/

open Module

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The sorted eigenvalues of a symmetric operator are determined by its characteristic
polynomial.** Let $T$ be a symmetric operator on a finite-dimensional inner product space $E$ of
dimension $n$, and let $d : \{0, \dots, n - 1\} \to \mathbb{R}$ be decreasing,
$d_0 \ge d_1 \ge \dots \ge d_{n-1}$. If the roots of the characteristic polynomial of $T$,
counted with multiplicity, are the numbers $d_0, \dots, d_{n-1}$, then $d$ is the list of
eigenvalues of $T$ in decreasing order.

The roots are compared as multisets in $\mathbb{K}$, with each $d_i$ embedded in $\mathbb{K}$.
The list of eigenvalues is `LinearMap.IsSymmetric.eigenvalues`. The theorem is
`LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues` read backwards. -/
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

/-- **The eigenspaces of a symmetric operator on a finite-dimensional space span it.** Let $T$ be a
symmetric operator on a finite-dimensional inner product space $E$. Then the sum of the
eigenspaces $\ker(T - \mu I)$ over all $\mu \in \mathbb{K}$ is $E$.

This is the form with `⊤` of
`LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot` in Mathlib. -/
theorem IsSymmetric.iSup_eigenspace_eq_top {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    (⨆ μ : 𝕜, Module.End.eigenspace T μ) = ⊤ :=
  Submodule.orthogonal_eq_bot_iff.1 hT.orthogonalComplement_iSup_eigenspaces_eq_bot

end LinearMap
