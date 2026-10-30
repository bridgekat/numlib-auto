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

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* Theorem 3.2.2 (and the Newton example of Theorem 3.1.1): **false** claim `‖∇f(x_k)‖ > ε₁` at
  `k = k_ε` for the data (3.1.4); the example prescribes `∇f(x_{k_ε}) = 0` and terminates exactly
  at `k_ε = ⌈ε₁⁻²⌉` (`theorem_3_2_2`, `theorem_3_1_1`).
* Theorem 3.2.6: **typo**, `κ^F_TR2` lacks a `|log ·|`; the proof's constant `kappaFTR2` is
  bounded by the repaired book constant (`kappaFTR2_le_book`); `ε₁ ≤ 1` is dropped
  (`theorem_3_2_6`).
* (3.2.25): **typo**, `x_k = k ε`; the claim `f_{k_ε} ≥ 0` needs `ε⁻³` integral (**gap**, only
  boundedness is used) (`theorem_3_2_7`).
* §3.2.1: **reading**, the trust-region constraints `x_k - t g ∈ 𝓡_k`, `x_k + t u ∈ 𝓑_{Δ_k}` on
  the Cauchy and eigenpoint steps are `‖t g‖ ≤ Δ_k`, `‖t u‖ ≤ Δ_k`.
* (3.3.30): **false** with `+ 1`; proved with `+ 2` (`theorem_3_3_9`).
* Theorems 3.3.6, 3.3.10: **reading**, proved here from the data of Theorem 12.2.15 (the book
  defers them to §12.2.2.4) (`theorem_3_3_6`, `theorem_3_3_10`).
* Lemma 3.4.3: **typo**, misprinted quadratic and root; (3.4.10) proved directly (`lemma_3_4_3`).
* Lemma 3.4.4: **typo**, the case labels (3.4.13)/(3.4.14) are swapped (`lemma_3_4_4`).
* Theorems 3.4.6, 3.4.12: **gap**, a successful iteration without the required decrease is only
  followed by one with it; proved with a factor `2` on the leading terms
  (`Optimization.card_successSet_le_two_mul_add_one`, `theorem_3_4_6`, `theorem_3_4_12`).
* Theorems 3.4.11, 3.4.12: **gap**, the count misses the successful iterations and the final
  unsuccessful block; corrected constants `κ^A = κ^S (M + 1)`, `κ^B = M + 2`, `κ^D = 2M + 3`
  (`kappaAIRN`, `kappaBIRN`, `kappaDIRN`, `theorem_3_4_11`).
* Lemma 3.5.1: **typo**, the self-referential constant is `κ_λ = 2√(κ̄_λ(1 + κ_rg))`
  (`lemma_3_5_1`). (3.5.17): **typo**, sign of `s_k` (`theorem_3_5_4`).
* Corollary 3.5.5: **gap**, the AR2 example is that of Theorem 3.3.6, and for iRN the ratio
  (3.4.35) is not scale invariant: the data (3.5.12) are rescaled to `c G(x/c)`,
  `c = min(1, (2η)^{-1/2})` (`irn_slow_example`, `corollary_3_5_5_iii`).
* Lemmas 3.5.1–3.5.3: **reading**, unused hypotheses dropped (`lemma_3_5_1`, `lemma_3_5_2`,
  `lemma_3_5_3`).

## Not formalized

Every numbered result of the chapter is formalized.
-/
