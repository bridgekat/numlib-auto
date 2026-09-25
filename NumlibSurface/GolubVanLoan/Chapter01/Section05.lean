import Mathlib.Init

/-!
# Golub–Van Loan §1.5: vectorization and locality

Surface file for §1.5 of Golub and Van Loan, *Matrix Computations* (4th edition). The section has
no formal content, and this module declares nothing.

## Not formalized here

The section is a qualitative performance model: pipelined vector processing and the cycle counts
`N_arith`, `N_data` of the strip-mined loop (1.5.1), the load/store counts of the gaxpy versus the
outer product (§1.5.2), stride (§1.5.3), and cache blocking (§1.5.4) with the capacity constraint
(1.5.5) and the Lagrange-multiplier heuristic `q_opt = p_opt = r_opt ≈ √(n²/3M)` (1.5.6). None of
these is a mathematical proposition about the computed quantities: the counts are statements about
a machine model the book itself calls "qualitative … not necessarily good predictors of
performance", and (1.5.6) is an `≈` without a rigorous reading (it rounds a continuous optimum and
ignores non-divisibility, as the text says). The blocked update (1.5.4) computes `C + AB` by
Theorem 1.3.1 (`GolubVanLoan.Chapter01.theorem_1_3_1`); it is an unnumbered code fragment, not an
Algorithm.
-/
