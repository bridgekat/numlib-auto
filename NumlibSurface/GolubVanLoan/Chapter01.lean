import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter01.Section03
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter01.Section05
import NumlibSurface.GolubVanLoan.Chapter01.Section06

/-!
# Golub–Van Loan, Chapter 1: matrix multiplication

The surface of Chapter 1 of Golub and Van Loan, *Matrix Computations* (4th edition): real matrices
`Matrix (Fin m) (Fin n) ℝ` and vectors `Fin n → ℝ` (`ℂ` in §1.4's transforms), in the namespace
`GolubVanLoan.Chapter01`, one module per section. This module imports the sections.

## Conventions of the chapter

* Indices are 0-based `Fin n`: the book's 1-based `i` is `i − 1`, a colon range `p:q` is a
  filtered `List.finRange n` inside algorithms and a `submatrix` along an explicit embedding in
  statements; each section states the translation where it matters.
* **Algorithms.** Every numbered algorithm is a definition
  `algorithm_1_M_K {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) …` (`rnd : ℂ → M ℂ` for the
  FFT-based ones of §1.4) following the algorithm conventions of `NumlibSurface.GolubVanLoan`;
  recursive algorithms (Strassen, the FFT, the Haar transform) recurse on `q`/`t` with `n = 2^q`.
  Its specification `algorithm_1_M_K_spec` says that the exact run `Id.run (algorithm_1_M_K pure …)`
  is Mathlib's product (`x ⬝ᵥ y`, `y + a • x`, `y + A *ᵥ x`, `C + A * B`) or the backbone
  transform. Data come in BLAS order (`a x y`, `A x y`, `A B C`).
* **Floating point.** The book analyses the algorithms of §1.1 in §2.7; the run characterizations
  (`…_mem_run`) and bridges (`…_rounds`, to `FloatingPoint.RoundsDot`/`RoundsMul`) chapter 2 needs
  are in §1.1, beside the algorithms, and the exact specifications of §1.1 are read off them at the
  exact model. The `0 + fl(x₁y₁)` mismatch between the book's loops and `RoundsSum` is resolved by
  the hypothesis `fp.IsIdempotent`, assumed only by the bridges that need the book's `γ_n`.
* **Shared helpers.** The rounded entrywise operations `vecAdd`, `vecSub`, `vecPointwiseMul`
  (§1.4, any hook `rnd : K → M K`) and `matrixAdd`, `matrixSub` (§1.3, rectangular), each with its
  `_spec`, are the ones every later chapter calls (the root module's shared-helper list).
* Kronecker products, `vec` and the perfect shuffle are the positional backbone forms
  `Matrix.kroneckerFin`, `Matrix.vecFin`, `Matrix.perfectShuffle` (row `(i₁ − 1) m₂ + i₂` of
  `B ⊗ C` is `finProdFinEquiv (i₁, i₂)`); permutation matrices `I_n(v,:)` are Mathlib's
  `v.permMatrix ℝ`. Hamiltonian and symplectic matrices live on `Fin n ⊕ Fin n`, where Mathlib's
  `J` is the negative of the book's.

## Backbone correspondence

`Numlib/FloatingPoint/Program` (the program semantics), `Numlib/LinearAlgebra/Matrix/Band`
(bandwidth), `…/Block` (block multiplication, Theorem 1.3.1), `…/Permutation` (exchange, downshift,
perfect shuffle), `…/Kronecker` (§1.3.6–1.3.7), `…/Hamiltonian` (§1.3.10),
`Numlib/Analysis/Fourier/DFT` and `…/SineCosineTransform` (§1.4).

## Not formalized

* Operation counts and flop, memory and communication analyses everywhere (§1.1.15–1.1.16,
  Tables 1.1.1–1.1.2, §1.2.4, the counts after Algorithms 1.2.2, 1.3.1, 1.4.1–1.4.4, Strassen's
  `n^{log₂ 7}`, the `6n⁴` Kronecker count).
* §1.5 (vectorization, stride, cache blocking, (1.5.1)–(1.5.6)) as a whole.
* §1.6 (parallel matrix multiplication) except Cannon's identity (1.6.16) and its shift relations.
* The BLAS "level" discussion (§1.1.17) and storage schemes as such: (1.2.1) and (1.2.2) enter only
  as hypotheses of the specifications of Algorithms 1.2.2–1.2.3.
* Notation-only displays ((1.1.1)–(1.1.3), (1.4.1)–(1.4.2), (1.4.6), (1.4.9), (1.4.11) are
  definitions, given as definitions where an object is needed), the numerical examples, the
  MATLAB `reshape` example.
* Unnumbered prose remarks without a later citation: band inheritance of `B ⊗ C`, the real form of
  complex multiplication (§1.3.9), the multiple-Kronecker reshaping of §1.3.8, the DST-II embedding
  remark after (1.4.12); the DST-II … DCT-IV definitions of (1.4.12) are left to chapter 4.
* The "Notes and References" of every section.
-/
