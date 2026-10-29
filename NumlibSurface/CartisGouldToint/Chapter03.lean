import NumlibSurface.CartisGouldToint.Chapter03.Section01
import NumlibSurface.CartisGouldToint.Chapter03.Section02
import NumlibSurface.CartisGouldToint.Chapter03.Section03
import NumlibSurface.CartisGouldToint.Chapter03.Section04
import NumlibSurface.CartisGouldToint.Chapter03.Section05

/-!
# Cartis–Gould–Toint, Chapter 3: Methods Using Second Derivatives

Surface of [cartis2022evaluation] Chapter 3: the slowness of Newton's method, the second-order
trust-region and adaptive-regularization methods TR2 and AR2, the `O(ε^{-3/2})` methods TRε and
iRN, and the lower bound `⌈ε^{-3/2}⌉` for the class `𝓜` of second-order methods. This module
imports the section modules and adds nothing of its own.

* §3.1, `Chapter03.Section01`: f.C2, f.HL; Newton's method (Algorithm 3.1.1), Theorem 3.1.1
* §3.2, `Chapter03.Section02`: TR2 (Algorithm 3.2.1); Theorems 3.2.1–3.2.2, Lemmas 3.2.3–3.2.5,
  Theorems 3.2.6–3.2.7
* §3.3, `Chapter03.Section03`: AR2 (Algorithm 3.3.1); Lemmas 3.3.1–3.3.4, 3.3.7–3.3.8, Theorems
  3.3.5–3.3.6, 3.3.9–3.3.10
* §3.4, `Chapter03.Section04`: TRε (Algorithm 3.4.1) and iRN (Algorithm 3.4.2); Lemmas 3.4.1–3.4.4,
  3.4.7–3.4.10, Theorems 3.4.5–3.4.6, 3.4.11–3.4.12
* §3.5, `Chapter03.Section05`: the class `𝓜`; Lemmas 3.5.1–3.5.3, Theorem 3.5.4, Corollary 3.5.5

The tolerance `ε₂` is an `Option ℝ`, `none` standing for `ε₂ = +∞`; the termination test
`stopTest` of TR2 and AR2 subsumes the book's separate "strict local minimizer" branch. Appendix B's
Lemma B.3.1 is in `AppendixB.Chapter03`; the appendix proofs of Theorems 3.4.11–3.4.12 and §3.5
belong to the results above.

## Deviations from the book

* Theorem 3.2.6: the printed constant `κ^F_TR2` lacks a `|log ·|`; the proof's constant is
  `kappaFTR2`, bounded by the repaired book constant (`kappaFTR2_le_book`).
* Theorem 3.2.2 (and the Newton example of Theorem 3.1.1): with the data (3.1.4) the claim
  `‖∇f(x_k)‖ > ε₁` can fail at `k = k_ε`; the example prescribes `∇f(x_{k_ε}) = 0`, so that the run
  terminates exactly at `k_ε = ⌈ε₁⁻²⌉`.
* (3.3.30): the additive `+ 1` is false; the bound holds with `+ 2`.
* Theorems 3.4.6 and 3.4.12: the counting arguments are wrong (a successful iteration without the
  required decrease is only followed by one with it); the bounds hold with a factor `2` on the
  leading terms (`Optimization.card_successSet_le_two_mul_add_one`). Theorems 3.4.11–3.4.12 get
  corrected constants `κ^A = κ^S (M + 1)`, `κ^B = M + 2`, `κ^D = 2M + 3`.
* Lemma 3.4.3 (misprinted quadratic and root), Lemma 3.4.4 (swapped case labels), Lemma 3.5.1
  (self-referential constant, read `κ_λ = 2√(κ̄_λ(1 + κ_rg))`) and the sign of (3.5.17) are
  repaired.
* Theorems 3.3.6, 3.3.10 (proofs deferred by the book to §12.2.2.4) are proved here from the
  one-dimensional data of Theorem 12.2.15.
* Corollary 3.5.5: the AR2 example is that of Theorem 3.3.6; for iRN the ratio (3.4.35) is not
  scale invariant and the data (3.5.12) must be rescaled to `c G(x/c)`, `c = min(1, (2η)^{-1/2})`.
* Several hypotheses the proofs do not use are dropped (in Lemmas 3.5.1–3.5.3, Theorem 3.2.6's
  `ε₁ ≤ 1`); each section module lists them.

## Not formalized

Every numbered result of the chapter is formalized.
-/
