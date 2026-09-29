import NumlibSurface.GolubVanLoan.Chapter07.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section02
import NumlibSurface.GolubVanLoan.Chapter07.Section03
import NumlibSurface.GolubVanLoan.Chapter07.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section05
import NumlibSurface.GolubVanLoan.Chapter07.Section06
import NumlibSurface.GolubVanLoan.Chapter07.Section07
import NumlibSurface.GolubVanLoan.Chapter07.Section08
import NumlibSurface.GolubVanLoan.Chapter07.Section09

/-!
# Golub–Van Loan, Chapter 7: unsymmetric eigenvalue problems

The surface of Chapter 7 of Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th
edition [golub2013matrix]: §7.1 properties and decompositions (Schur, Jordan, block
diagonalization), §7.2 perturbation theory, §7.3 power iterations, §7.4 Hessenberg and real Schur
forms, §7.5 the practical QR algorithm, §7.6 invariant subspace computations, §7.7 the generalized
eigenvalue problem and QZ, §7.8 Hamiltonian and product eigenvalue problems, §7.9 pseudospectra.
One module per section, `NumlibSurface/GolubVanLoan/Chapter07/SectionMM.lean`, namespace
`GolubVanLoan.Chapter07`; this module imports the sections and adds nothing of its own.

## Conventions

* **Scalars.** The theory of §7.1–7.3 and §7.9 is complex, `Matrix (Fin n) (Fin n) ℂ`,
  `λ(A) = spectrum ℂ A`, eigenvalues with multiplicity `A.charpoly.roots`, unitary
  `Q ∈ Matrix.unitaryGroup` with `Qᴴ = star Q`. The algorithms of §7.4–7.7 and §7.8 are real,
  `Matrix (Fin n) (Fin n) ℝ`, `Matrix.orthogonalGroup`, and the complex eigenvalues of a real matrix
  are those of `Matrix.complexify`. The power method and orthogonal iteration of §7.3 are stated
  over any `RCLike` field, so that chapter 8 instantiates them at `ℝ`.
* **Indices.** The book is 1-based with colon notation; Lean is 0-based on `Fin n`: `H(k+1, k)`,
  `k = 1:n-1`, is `H ⟨k+1, _⟩ ⟨k, _⟩`, `k < n - 1`. Block partitions `[T₁₁ T₁₂; 0 T₂₂]` are
  `Matrix.fromBlocks` on `Fin p ⊕ Fin q`, reindexed by `finSumFinEquiv` where the book's matrix is
  one `n × n` array, or a block index `b : Fin n → Fin q` with `Matrix.BlockTriangular` and
  `Matrix.toSquareBlock` for the `q`-block partitions (7.1.9).
* **Norms.** `‖·‖₂` is Mathlib's scoped `Matrix.Norms.L2Operator`, `‖·‖_F` the scoped
  `Matrix.Norms.Frobenius` (never both open in one proof), `‖·‖_p` and `κ_p` the backbone's
  `Matrix.lpOpNorm`, `Matrix.condNumberLp`; `σ_min(A) = ⨅ i, A.colSingularValues i`. The distance
  of two subspaces, `dist(S₁, S₂) = ‖P₁ - P₂‖₂` of §2.5.3, is the backbone's `Submodule.gap`.
* **Algorithms.** The numbered conventions 1–14 of `NumlibSurface.GolubVanLoan` (those of
  `Numlib/FloatingPoint/Program`) govern every program of the chapter.

## Correspondence with the backbone

`Numlib/LinearAlgebra/Matrix/{Schur,Jordan,Similar,Sylvester,RealSchur,UnreducedHessenberg,
KrylovDecomposition,GeneralizedSchur,Hamiltonian}`, `Numlib/Eigen/{Normal,NumericalRange,
Perturbation,InvariantSubspace,PowerMethod,QRAlgorithm,Pencil,Pseudospectrum,HamiltonianSchur,
PeriodicSchur}`, and `Numlib/Analysis/Matrix/Function/Sign` for §7.6's matrix sign function.
Quarteroni–Sacco–Saleri Chapter 5 restates much of the same backbone; the two surfaces share it and
not each other.

## Not formalized (by decision; each section lists its instances)

* operation counts, flop and level-3/BLAS discussions (§7.4.4 entirely), balancing (§7.5.7);
* numerical examples, figures and MATLAB-style illustrations;
* the Notes and References;
* roundoff claims stated with `≈` and no derivation: (7.1.14)–(7.1.15), the backward stability of
  the QR algorithm (§7.5.6), of Schur reordering and block diagonalization (§7.6.2–7.6.3), of QZ
  (§7.7.7);
* heuristics without a precise claim, results quoted without proof and with no construction
  (Wilkinson's nearest multiple eigenvalue bound, Stewart's chordal-metric bound, the Kronecker
  canonical form), and (7.8.7) and the convergence of the QR, QZ and product iterations (not proved
  by the book).

## Book errors found

Theorem 7.3.1 is false as printed (the hypothesis must bound the distance to `D_r(Aᴴ)`, not to
`D_r(A)`); Theorem 7.1.6 prints `λ(T_ij)` for `λ(T_ii)`; (7.1.3)'s maximum index is misprinted;
§7.6.3's `κ_F(Y_ij) = n_i² + n_j² + ‖Z‖_F²` should be `n_i + n_j + ‖Z‖_F²`; the generalized inverse
iteration's `λ^(k) = qᴴAq/qᴴAq`; the `2 × 2` power bound "for any `ε > 0`" (needs `ε ≤ M`); the
cross-reference slips "Theorem 7.4.3 (the implicit Q theorem)" and "Lemma 7.3.1"; typos in the
proofs of Lemma 7.3.2 and Theorems 7.9.1–7.9.2; the `F`/`G` labelling of (7.8.1) against Figure
7.8.1.
-/
