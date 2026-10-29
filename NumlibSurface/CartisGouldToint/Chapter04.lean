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

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* (4.1.8)–(4.1.9), `𝓜_k ≠ ∅`: **gap**, literally read a run can get stuck; read vacuously
  ("for all `d ∈ 𝓜_k`"), as the proof of Theorem 4.1.5 uses (`algorithm_4_1_1`).
* Algorithm 4.1.1 with `ε₃ < ∞`: **false** that an admissible step exists
  (`not_exists_algorithm_4_1_1_third_order`); Theorem 4.1.5 (iii) is a statement about runs
  (`theorem_4_1_5_iii`).
* Theorem 4.1.5: **reading**, split by order of criticality with the constants of the active
  orders (`theorem_4_1_5_i`, `theorem_4_1_5_ii`, `theorem_4_1_5_iii`).
* Theorem 4.1.6 (iii): **gap**, the book defers the proof (to §12.2.2.4) and its sign of
  `λ_min` is wrong; proved on the data of Theorem 12.2.15 assuming `σ₀ ≤ (p-2)! min(θ₂, θ₃)`
  (`theorem_4_1_6_iii`).
* (4.2.6): **typo** in the first term, `-Ψ(1) Φ([x]_1)`; with the printed one Lemma 4.2.5 (ii)
  fails at `x = 0` (`lemma_4_2_5_ii`).
* Theorem 4.2.6: **gap**, the proof gives `#_ε ≥ k̄`, not `≥ 2k̄`, and the form with `c₀` needs `ε`
  small (`theorem_4_2_6_i`); only the order in `ε` is tight (`theorem_4_2_6_ii`).
* Lemma 4.2.5 (iv): **reading**, the absolute constant is `c₁ = 20` (`lemma_4_2_5_iv_growth`).
* `𝓕(Δ, p)`, zero-respecting methods: **reading**, members are `C^∞` (the book's footnote), and
  zero respect is defined through null directions of the derivative tensors.

## Not formalized

§4.1.3 ("A TRp algorithm?") contains no numbered statement.
-/
