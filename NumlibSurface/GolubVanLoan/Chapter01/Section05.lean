/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Init

/-!
# Golub and Van Loan, Section 1.5: Vectorization and locality

Section 1.5 of [golub2013matrix] describes how the speed of a matrix computation depends on the
machine: pipelined vector operations, the movement of data between memory and registers, stride, and
cache blocking. The section has no formal content, and this module declares nothing. The blocked
update (1.5.4) computes $C + AB$ block by block; its correctness is Theorem 1.3.1,
`GolubVanLoan.Chapter01.theorem_1_3_1`. The update is an unnumbered code fragment of the source, not
an Algorithm.

## Not formalized

* **Pipelined vector processing and the cycle counts $N_{\mathrm{arith}}$ and $N_{\mathrm{data}}$ of
  the strip-mined loop (1.5.1).** They describe a machine model, not the computed quantities.
* **The load and store counts of the gaxpy and the outer product (§1.5.2).** They describe a machine
  model.
* **Stride (§1.5.3).** It describes a machine model.
* **Cache blocking (§1.5.4) with the capacity constraint (1.5.5).** It describes a machine model.
  The source itself calls these models qualitative and "not necessarily good predictors of
  performance".
* **The heuristic optimum $q_{\mathrm{opt}} = p_{\mathrm{opt}} = r_{\mathrm{opt}} \approx
  \sqrt{n^2/3M}$ (1.5.6).** It is an approximate equality without a rigorous reading: it rounds a
  continuous optimum, obtained with Lagrange multipliers, and it ignores non-divisibility, as the
  source says.
-/
