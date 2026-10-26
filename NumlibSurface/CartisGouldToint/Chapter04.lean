import NumlibSurface.CartisGouldToint.Chapter04.Section01
import NumlibSurface.CartisGouldToint.Chapter04.Section02

/-!
# Cartis–Gould–Toint, Chapter 4: Methods Using Third Derivatives and Beyond

Surface of [cartis2022evaluation] Chapter 4: the adaptive-regularization method ARp with `p`-th
order Taylor models and its complexity `O(ε^{-(p+1)/(p-q+1)})` for approximate minimizers of order
`q ∈ {1, 2, 3}` (§4.1), and the lower bound of Carmon, Duchi, Hinder and Sidford for `p`-th order
methods on functions of unbounded dimension, showing that ARp is optimal (§4.2). This module imports
the section modules and adds nothing of its own.

* §4.1, `Chapter04.Section01`: ARp (Algorithm 4.1.1), f.DpL; Lemmas 4.1.1–4.1.4, Theorems
  4.1.5–4.1.6
* §4.2, `Chapter04.Section02`: zero chains, the classes `𝓜(p)`, `𝓜_ZR(p)`, `𝓕(Δ, p)`; Lemmas
  4.2.1–4.2.3, 4.2.5, Theorems 4.2.4, 4.2.6

ARp is the backbone run predicate `Optimization.IsARpRun`; the lower-bound machinery is in the
backbone modules `Numlib.Optimization.Complexity.ZeroChain`, `ResistingOracle` and `CarmonChain`.
Appendix B's Lemma B.4.1 is in `AppendixB.Chapter04`.

## Deviations from the book

* ARp's third-order test (4.1.8)–(4.1.9) requires `𝓜_k ≠ ∅`; literally read, a run can get stuck.
  The test is read vacuously ("for all `d ∈ 𝓜_k`"), which is what the proof of Theorem 4.1.5 uses.
  Even so, with `ε₃ < ∞` an admissible step need not exist
  (`not_exists_algorithm_4_1_1_third_order`): the third-order mode is not always well posed, and
  Theorem 4.1.5 (iii) is a statement about runs.
* Theorem 4.1.5 is split by order of criticality, each part with the constants of the active
  orders only (`theorem_4_1_5_i` – `theorem_4_1_5_iii`).
* Theorem 4.1.6 (proof deferred by the book to §12.2.2.4) is proved on the data of
  Theorem 12.2.15; part (iii) assumes `σ₀ ≤ (p-2)! min(θ₂, θ₃)`, without which the slow example's
  steps need not be admissible.
* (4.2.6): the first term of `f^D` is `-Ψ(1) Φ([x]_1)`; with the printed `-Ψ([x]_1) Φ([x]_1)`
  Lemma 4.2.5 (ii) fails at `x = 0`.
* Theorem 4.2.6: the proof gives `#_ε ≥ k̄`, not `≥ 2k̄`, and the form with `c₀` needs `ε` small;
  the upper and lower bounds have different dependence on `L`, so only the order in `ε` is tight
  (`theorem_4_2_6_ii`).
* Members of `𝓕(Δ, p)` are `C^∞` (the book's footnote), and zero-respecting methods are defined
  through null directions of the derivative tensors.

## Not formalized

The explicit growth `L^D_p ≤ exp(5/2 p log p + c₁ p)` of the constant of Lemma 4.2.5 (iv)
(planned as `lemma_4_2_5_iv_growth`, open); the lemma itself is proved with an explicit constant
independent of `k̄`. §4.1.3 ("A TRp algorithm?") contains no numbered statement.
-/
