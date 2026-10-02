import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter03.Section02
import NumlibSurface.GolubVanLoan.Chapter03.Section03
import NumlibSurface.GolubVanLoan.Chapter03.Section04
import NumlibSurface.GolubVanLoan.Chapter03.Section05
import NumlibSurface.GolubVanLoan.Chapter03.Section06

/-!
# Golub–Van Loan, Chapter 3: General Linear Systems

Surface of [golub2013matrix] Chapter 3: triangular systems (§3.1), the LU factorization and its
algorithms (§3.2), their rounding errors (§3.3), pivoting (§3.4), improving and estimating accuracy
(§3.5), parallel LU (§3.6, precise statements only). One module per section,
`NumlibSurface/GolubVanLoan/Chapter03/SectionMM.lean`, namespace `GolubVanLoan.Chapter03`. Real
square systems `A : Matrix (Fin n) (Fin n) ℝ`, `b : Fin n → ℝ`; rectangular
`Matrix (Fin m) (Fin n) ℝ` in §3.1.6, §3.2.10 and §3.6.

## Conventions

* Indices are 0-based: the book's `A(i:j, k:l)` is a `Matrix.submatrix`/`Matrix.toBlock`, its
  "`A(1:k,1:k)` nonsingular for `k = 1:n-1`" is a statement about
  `A.strictLeadingPrincipalSubmatrix k` for `k : Fin n` (`k = 0` is the empty block), its step
  `k = 1:n-1` is `k : Fin n` with a harmless empty last step, and its `A^{(k)}` is
  `Matrix.gemStage A (k - 1)` in (3.2.3) but the stage after `k` steps in §3.4 (the book changes
  convention). Block partitions are `Matrix.fromBlocks` over `Fin r ⊕ Fin s` read on `Fin (r + s)`
  through `finSumFinEquiv`.
* Norms: `‖·‖_∞` is Mathlib's scoped `Matrix.Norms.Operator` norm (`= Matrix.lpOpNorm ⊤`),
  `κ_∞ = Matrix.condNumberLp ⊤`; entrywise `|·|` and `≤` on matrices are `Matrix.abs` and `≤ₑ`.
* Floating point: the book's `fl`, `u` are `fp : FloatingPoint.RoundingModel ℝ` and `fp.u`; its
  first-order bounds `c n u (…) + O(u²)` are stated in the rigorous `γ` forms
  (`FloatingPoint.gamma fp.u k`), which imply them.
* **Algorithms** follow the numbered conventions of `NumlibSurface/GolubVanLoan` (the same list
  heads `Numlib/FloatingPoint/Program`): every numbered algorithm is a program generic in a monad
  `M` and a rounding hook `rnd : ℝ → M ℝ`, in the book's operation order; displays that write out a
  complete procedure are content-named programs (`blockForwardElim` (3.1.4), `solveMultipleRHS`
  (3.4.12), `solvePowerSystem` (3.4.13), `iterativeImprovementStep` (3.5.4),
  `mixedPrecisionImprovement` (3.5.5)). The algorithms the book analyses — 3.1.1–3.1.4, 3.2.1,
  3.2.2, 3.4.1, 3.4.2 — carry a bridge `_rounds` into the backbone's relational predicates
  (`RoundsForwardSubst(Dot)`, `RoundsBackSubst(Dot)`, `RoundsLU` on `P A`), an exact specification
  `_spec` read off the bridge at the exact model `FloatingPoint.RoundingModel.exact ℝ` (with
  `roundsForwardSubst_exact_iff`, `roundsLU_exact_iff`), and the book's backward error bound
  (§3.1, §3.3, (3.4.6)–(3.4.9) for both partial pivoting algorithms). The others
  (`blockForwardElim`, `tallOuterProductLU`, Algorithms 3.2.3, 3.2.4, 3.4.3, 3.5.1 and the solves
  of §3.4–3.5) have exact specifications proved at `Id` and no bridge. The pivoting algorithms keep
  the book's guard
  `if A(k,k) ≠ 0`; its exact specification is read off the invariant of its bridge (a zero pivot of
  partial pivoting comes with a zero column, so in exact arithmetic the skipped update is an
  update).
* Chapter-specific readings of the conventions: a pivot search compares exact absolute values of
  computed entries (`Matrix.partialPivotRow`); unit triangular solves inside factorizations do not
  divide by the unit diagonal (`unitForwardSubstColOn` in Algorithms 3.2.3–3.2.4, `gaxpyColumn` in
  Algorithms 3.2.2 and 3.4.2); a level-3 update `B − L X` (in (3.1.4), Algorithms 3.2.3 and 3.2.4)
  is carried out entrywise as running differences (`FloatingPoint.runningDiff`), the order of the
  backbone's `RoundsRunningDiff`; `fp.IsIdempotent` is never assumed — the inner-product relations
  absorb the `0 + p` rounding; the relational model bounds computed multipliers of partial
  pivoting by `1 + u`, not `1`.

## Not formalized

Operation counts, flop tables and level-3 fractions; numerical examples and their tables; the
proof-internal displays (3.3.3)–(3.3.13) (the backbone proves [higham2002accuracy] Theorem 9.3
entrywise); the rectangular remark after Theorem 3.3.1; heuristics with no rigorous reading beyond
the planned nodes ((3.5.1) as an approximation, Heuristics II and III, the Forsythe–Moler
estimate, the average-case growth `n^{2/3}`, "`ρ = 10`", the reliability of rook pivoting, Skeel's
criterion, simple row scaling); the "LU mentality" Example 3 and the vocabulary of §3.4.10; the five
unwritten loop orders of §3.2.9 and P3.4.5's algorithm behind (3.4.11); the backward stability of
complete pivoting (§3.4.6, §3.4.10: Algorithm 3.4.3 has an exact specification only, no rounding
bridge); §3.6 except (3.6.2) and (3.6.5).
-/
