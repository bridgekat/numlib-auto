import NumlibSurface.GolubVanLoan.Chapter09.Section01
import NumlibSurface.GolubVanLoan.Chapter09.Section02
import NumlibSurface.GolubVanLoan.Chapter09.Section03
import NumlibSurface.GolubVanLoan.Chapter09.Section04

/-!
# Golub–Van Loan, Chapter 9: functions of matrices

The surface of Chapter 9 of Golub and Van Loan, *Matrix Computations* (4th edition): §9.1
eigenvalue methods, §9.2 approximation methods, §9.3 the matrix exponential, §9.4 the sign, square
root and logarithm of a matrix and the polar decomposition; in the namespace
`GolubVanLoan.Chapter09`, one module per section. This module imports the sections.

## Conventions of the chapter

* `f(A)` is the backbone's primary functional calculus `pfc f A` for
  `A : Matrix (Fin n) (Fin n) ℂ` and `f : ℂ → ℂ` (Hermite interpolation of `f` and its derivatives
  on the roots of the minimal polynomial). The book *defines* `f(A)` through the Jordan form
  ((9.1.1)–(9.1.4)); here that is a theorem (`equation_9_1_3`), whose right side is thereby
  independent of the Jordan decomposition chosen. "`f(A)` is defined" is a hypothesis only where a
  proof uses it; `pfc` is total.
* The book's `e^A` is Mathlib's `NormedSpace.exp A`, equal to `pfc Complex.exp A`
  (`taylor_exp`). §9.3 is stated for real `A : Matrix (Fin n) (Fin n) ℝ` where the book is real,
  and for complex `A` where it uses the Schur form. The named functions of §9.4 are the backbone's
  `Matrix.matrixSign`, `Matrix.principalSqrt`, `Matrix.principalLog`.
* Indices are `0`-based: the book's `t_ij`, `1 ≤ i, j ≤ n`, is `T i j` with `i j : Fin n`; the
  superdiagonal loops of Algorithm 9.1.1 run `p = 1, …, n-1`, `i = 0, …, n-1-p`, `j = i + p`.
  Upper triangular is `Matrix.IsUpperTriangular`. The strictly increasing sequences `S_ij` of
  Theorem 9.1.4 are the lists `Matrix.path i s j`, `s ⊆ Finset.Ioo i j`.
* Norms: `‖·‖₂` is Mathlib's scoped `Matrix.Norms.L2Operator`, `‖·‖_F` the scoped
  `Matrix.Norms.Frobenius`, `‖·‖_∞` the scoped `Matrix.Norms.Operator`.
* Algorithms follow the numbered conventions of `NumlibSurface.GolubVanLoan`: `algorithm_9_M_K`
  is a monadic program with a rounding hook, `algorithm_9_M_K_spec` its exact-arithmetic
  specification at `Id`. Algorithm 9.1.1 (Schur–Parlett) is over any field; Algorithms 9.2.1,
  9.2.2 and 9.3.1 are real and compute every matrix product by chapter 1's `algorithm_1_1_5`. The
  book analyses no algorithm of this chapter's rounding errors rigorously, so there are no `SetM`
  theorems.

## Backbone correspondence

`Numlib/Analysis/Normed/Algebra/PrimaryFunctionalCalculus/{Basic,Analytic,Cauchy}` (`pfc`,
`hasSum_pfc`, `pfc_comp`, `norm_pfc_sub_sum_le`, `pfc_eq_circleIntegral`);
`Numlib/Analysis/Matrix/Function/{Basic,Triangular,CFC,Exp,Pade,Sign,Sqrt,Log}`;
`Numlib/Analysis/Calculus/{HermiteInterpolation,HermiteGenocchi}` (divided differences and the
bound (9.2.1)); `Numlib/Analysis/Normed/Algebra/{Exponential,Logarithm,SpectralRadius}` (the
Fréchet derivative of the exponential, `ν(A, t)`, the resolvent bound, the spectral abscissa).

## Not formalized

* Operation counts (`2n³/3` flops, `O(2ⁿ)`, the numbers of matrix multiplications), storage
  remarks, and the choice `s = ⌊√q⌋` as minimizing work.
* Numerical examples: §9.1.3 (the `1 ± 10⁻⁵` matrix), the `3 × 3` example after Theorem 9.2.2,
  the `[-49 24; -64 31]` example of §9.2.3, the `q = 9` Paterson–Stockmeyer instance, Figure 9.3.1,
  the four square roots of `[4 10; 0 9]`, the `3 × 3` illustration of Theorem 9.1.4.
* Heuristic claims: the forward stability of block Schur–Parlett (§9.1.6); "a matrix `E` for which
  … `≈`" (§9.3.2); the rounding estimate `γ = u‖G²‖‖G⁴‖⋯` and "numerical experiments suggest"
  (§9.3.4); the accuracy comparisons of §9.1.3 and §9.2.3.
* Algorithmic outlines without a number and without a precise claim: the clustering step of block
  Schur–Parlett, the sin/cos scaling loop of §9.2.3 (its exact content is the double-angle
  formulas), QR with column pivoting on `(I + sign A)/2`, the scaled Newton iteration (9.4.6), the
  inverse-scaling-and-squaring loop (its identity is formalized), the Newton–Schulz motivation.
* The general closed contour of (9.2.8): it is stated for circles.
* The Problems, and the Notes and References.

## Errata

Corrected in the statements: (9.1.8) with `X`, `X⁻¹` exchanged; the sign of the `log(I - A)`
series (§9.1.2); Theorem 9.2.1's `max` over `1 ≤ i ≤ p` (read `q`); the missing `A⁴` in (9.2.7);
Theorem 9.2.2's `δ_r` needs `Ω` bounded; (9.2.4) applies a real mean-value remainder to complex
entries; the scaling exponent of Algorithm 9.3.1 (`j = 1 + ⌊log₂ ‖A‖_∞⌋` only gives
`‖A/2^j‖_∞ < 1`, not `≤ 1/2`); (9.3.2)'s `e^{α t M_S(t)}` for `e^{αt} M_S(t)`; §9.3.2's "equality
for all `t` iff `A` normal" is false in the "only if" direction; (9.3.6) cites "(7.8.8)" for
(7.9.8); §9.4.1's "Theorem 9.1.1" and `S² = S` (read `S² = I`); the principal square root needs no
eigenvalue on `(-∞, 0]`; the body of (9.4.11), lost in the source, is reconstructed from (9.4.12).

## The outline

| § | module | subject |
|---|---|---|
| 9.1 | `Chapter09.Section01` | Eigenvalue methods |
| 9.2 | `Chapter09.Section02` | Approximation methods |
| 9.3 | `Chapter09.Section03` | The matrix exponential |
| 9.4 | `Chapter09.Section04` | The sign, square root, and log of a matrix |
-/
