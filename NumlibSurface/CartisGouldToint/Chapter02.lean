import NumlibSurface.CartisGouldToint.Chapter02.Section01
import NumlibSurface.CartisGouldToint.Chapter02.Section02
import NumlibSurface.CartisGouldToint.Chapter02.Section03
import NumlibSurface.CartisGouldToint.Chapter02.Section04

/-!
# Cartis–Gould–Toint, Chapter 2: Methods Using First Derivatives

Surface of [cartis2022evaluation] Chapter 2: first-order methods for the unconstrained problem
under the assumptions f.Bb, f.C1 and f.gL, each with an `O(ε⁻²)` evaluation bound and an example
showing that the bound is attained. This module imports the section modules and adds nothing of
its own; §2.5 has no numbered results.

* §2.1, `Chapter02.Section01`: the standing assumptions f.Bb, f.C1, f.gL
* §2.2, `Chapter02.Section02`: steepest descent with backtracking (SDBA, Algorithm 2.2.1) and exact
  linesearch (SDEX); Lemma 2.2.1, Theorems 2.2.2–2.2.5
* §2.3, `Chapter02.Section03`: the trust-region method TR1 (Algorithm 2.3.1); Lemmas 2.3.1–2.3.6,
  Theorems 2.3.7–2.3.8
* §2.4, `Chapter02.Section04`: the adaptive-regularization method AR1 (Algorithm 2.4.1); Lemmas
  2.4.1–2.4.3, Theorems 2.4.4–2.4.5

Algorithms are run predicates `algorithm_2_2_1`, `algorithm_2_3_1`, `algorithm_2_4_1` (SDEX is
`IsSDEXRun`), each with an existence theorem; TR1 and AR1 are instances of the generic backbone runs
`Optimization.IsTRRun` and `Optimization.IsARRun`. The zig-zag example behind Theorem 2.2.5 is
Appendix B's Lemmas B.2.1–B.2.6 (`AppendixB.Chapter02`).

## Deviations from the book

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* Theorem 2.2.2, (2.2.8): **false**, the bound vanishes for `t_ini ≤ 2(1-α)/L` and omits the
  first trial point of every iteration; proved as
  `1 + (⌈log₂(L t_ini/(2(1-α)))⌉ + 1) κ (f(x₀) - f_low)/ε²` with
  `κ = 1/(α min(t_ini, (1-α)/L))` (`kappaSDBA`, the book's `κ_SDBA` when `t_ini ≥ (1-α)/L`)
  (`theorem_2_2_2`).
* (2.2.7): **false** when `t_ini < t_low/2`; proved with `min(t_ini, t_low/2)`
  (`lemma_2_2_1_index`).
* Theorems 2.2.3, 2.2.5: **reading**, `ε⁻²` is an integer (as the proofs assume); `t_ini ≥ α` is
  dropped (`theorem_2_2_3`, `theorem_2_2_5`).
* Theorem 2.2.5: **gap**, the book's corridor function gives a first *local* line minimizer; the
  example realizes the global exact linesearch (2.2.26) (`AppendixB.lemma_B_2_6`).
* Theorem 2.3.8: **false** example, with the printed `B_k = 2t⁻¹` the Cauchy condition (2.3.4)
  fails; the example uses `B_k = t⁻¹ I`, `t = Δ₀/2`, with `ρ_k = 2` (`theorem_2_3_8`).
* Lemma 2.3.5: **typo**, the model decrease is `m_k(0) - m_k(s_k)` (`lemma_2_3_5`).
* "Reasonable values" after Algorithm 2.4.1: **typo**, they contradict (2.4.2) and are not used.

## Not formalized

The one-dimensional example showing that f.Bb and f.C1 alone give no complexity bound (§2.1), and
the linesearch variants of §§2.2.3.1–2.2.3.3, 2.2.3.5 (no numbered results).
-/
