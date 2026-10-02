import NumlibSurface.GolubVanLoan.Chapter12.Section01
import NumlibSurface.GolubVanLoan.Chapter12.Section02
import NumlibSurface.GolubVanLoan.Chapter12.Section03
import NumlibSurface.GolubVanLoan.Chapter12.Section04
import NumlibSurface.GolubVanLoan.Chapter12.Section05

/-!
# Golub–Van Loan, Chapter 12: special topics

The surface of Chapter 12 of Golub and Van Loan, *Matrix Computations* (4th edition): displacement
structure (§12.1), structured-rank matrices (§12.2), Kronecker product computations (§12.3), tensor
unfoldings and contractions (§12.4), tensor decompositions and iterations (§12.5). Namespace
`GolubVanLoan.Chapter12`, one module per section; this module imports the sections.

## Conventions of the chapter

* Real matrices `Matrix (Fin m) (Fin n) ℝ`, 0-based: the book's `a_{ij}` is `A (i-1) (j-1)`,
  `A(i₁:i₂, j₁:j₂)` is `A.toBlock (· ∈ Set.Icc …) (· ∈ Set.Icc …)` or a `submatrix`, and `B(r)` with
  `r ∈ ℝ^{n−1}` is `Matrix.unitBidiagonal n r` with `r : ℕ → ℝ` (entries past `n − 2` unused). The
  book's MATLAB `tril`, `triu` are `Matrix.strictLower`, `Matrix.strictUpper` plus
  `Matrix.diagPart`; `.*` is `⊙`.
* Kronecker products are Mathlib's typed `B ⊗ₖ C` and, where the book's `Fin (m₁ m₂)` layout matters
  (perfect shuffles, `vec`, `reshape`), chapter 1's `Matrix.kroneckerFin` and `Matrix.vecFin` (the
  `finProdFinEquiv` flattening).
* Tensors are `RTensor n = Tensor (fun k : Fin d => Fin (n k)) ℝ`, entries `A i` with
  `i : ∀ k, Fin (n k)`; the book's `col(i, n)` is `finPiFinEquiv` (0-based), and every flattened
  statement carries the Kronecker products in the book's reversed order `M_d ⊗ ⋯ ⊗ M_1` through
  `Matrix.piKronecker_reindex_finPiFinEquiv`. Statements are typed first; a statement about the
  book's flattened unfoldings (`modalUnfolding`, `generalUnfolding`) is given where the book's
  display is about the flattened object. Frobenius norms through the scoped `Matrix.Norms.Frobenius`
  and the global Frobenius norm of `Tensor`.
* **Algorithms** (12.1.1, 12.1.2, 12.2.1, 12.2.2) are monadic programs
  `algorithm_12_M_K {M} [Monad M] (rnd : ℝ → M ℝ) …` in the book's operation order, every arithmetic
  result through `rnd`, dot products as chapter 1's `FloatingPoint.dotAccum`, loops as
  `List.foldlM` over `List.finRange` (`vecLoop`); `LUdisp` and `LUdispPiv` recurse structurally on
  the size `N + 1`. Their `_spec` theorems are about `Id.run (algorithm_12_M_K pure …)`. The book
  analyses no rounding errors in this chapter (it cites Gu (1998) for the stability of
  `LUdispPiv`), so there are no rounding nodes.
* The book's misprinted statements are formalized in corrected form, each saying so: (12.4.17),
  (12.5.11) (`∑_k` for `min_k`), the §12.3.5 perfect-shuffle factorization, Lemma 12.3.2's
  `rank = 1`, Lemma 12.3.3's `rank ≤ 2`, the LU claim of §12.2.5, (12.2.8), (12.2.11)'s
  `A_L(n, 1) ≠ 0`, (12.2.18)'s positive subdiagonal, even order and `det = 1`, Algorithm 12.2.1's
  `u_k ≠ 0`, Algorithm 12.2.2's `g_k`, §12.1.8's `X_G⁻¹ G X_G`, §12.3.8's algebraic (not modulus)
  eigenvalue, (12.3.9)'s `X ∈ ℝ^{n₂×n₁}`, (12.5.3)'s square, (12.5.5)'s `U_kᵀ` and (12.5.24)'s
  factor `d`.

## Backbone correspondence

§12.1 → `Numlib/LinearAlgebra/Matrix/Displacement` (on chapter 7's `Matrix.sylvesterMap`); §12.2 →
`…/Matrix/Semiseparable` (on the nullity theorem of `Rank`); §12.3 → `…/Matrix/KroneckerApprox`,
`…/Matrix/Kronecker` and `…/Matrix/Kronecker/Spectral`; §12.4–12.5 → `Numlib/LinearAlgebra/Tensor/`
(`Basic`, `Unfolding`, `MultilinearProduct`, `HOSVD`, `Tucker`, `CP`, `SingularValue`, `Train`):
the rectangular mode product of §12.4 is `Tensor.rectModeProd`, the HOSVD truncation of §12.5 is
`Tensor.truncatedHOSVDOf` in the factors of the SVDs of Theorem 12.5.1. The backbone's
Eckart–Young–Mirsky for competitors of rank at most `r̃`
(`Matrix.isLeast_frobenius_norm_sub_of_rank_le`, with `Matrix.svdTruncation_eq_sum`) carries the
nearest-Kronecker statements (chapter 2's restatement compares only ranks equal to `k < rank(A)`),
the Ky Fan principle the Tucker updates. Earlier
chapters' restatements are used where they apply: Theorem 3.2.1 for the LU existence of §12.1,
Lemma 7.1.5 for the Sylvester operators of §12.1.7.

## Not formalized

* Operation, flop, storage and data-sparsity counts; numerical examples (the `n = 4` Cauchy update
  of §12.1.3, the `2 × 2 × 3 × 4` unfolding of §12.4.1, the vec and transposition examples of
  §12.4.3–12.4.4 and (12.4.7)); MATLAB fragments; the Notes and References.
* The non-recursive sketch of Algorithm 12.1.1, the pivoting variant of Algorithm 12.2.1 (described
  in words only), and the "Steps 1–4" framework of §12.1.8 beyond its correctness statement.
* §12.2.8's misprinted `{p, q}`-semiseparable definition, the extended, sequentially semiseparable
  and hierarchical classes ((12.2.17) is a shape), and §12.2.9 (prose with citations).
* Fact 3 of §12.2.10: it names neither the perfect shuffles nor the positions of the bidiagonal
  blocks, and the book proves nothing.
* §12.3.7 (constrained nearest Kronecker products: the structure of `B_opt`, `C_opt` is cited
  without proof; the Toeplitz-constrained reduction is a method sketch).
* The multipass-transposition discussion of §12.3.5 beyond the two-pass identity, and the
  dynamic-programming remark of §12.3.10 beyond the reshaping identity.
* The space–time contraction example of §12.4.12 (flop counts; its index bookkeeping is misprinted).
* The "Repeat" iterations of §12.5 (Tucker-ALS, CP-ALS, the higher-order power methods): what each
  step solves is stated.
* The TT-SVD procedure (12.5.29) is not programmed (a deviation from the convention that
  algorithm-shaped displays get a program): its ranks `r_k = rank(M_k)` are data-dependent, so the
  carriages' shapes depend on the run. What the procedure computes is stated instead: a tensor train
  `𝒜 = trainOfCarriages d 𝒢` with `r_k = rank 𝒜_{[1:k] × [k+1:d]}` exists (`equation_12_5_29`),
  each step being the factorization (12.5.26)–(12.5.28) (`equation_12_5_28`).
* "The truncated HOSVD does not solve the Tucker problem" (§12.5.3): a negative claim with no
example.
* Complications 1–6 of §12.5.5 (NP-hardness, maximal and typical ranks, real versus complex rank,
  degenerate tensors, non-nestedness): cited results.
-/
