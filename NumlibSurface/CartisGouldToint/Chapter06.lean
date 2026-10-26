import NumlibSurface.CartisGouldToint.Chapter06.Section01
import NumlibSurface.CartisGouldToint.Chapter06.Section02
import NumlibSurface.CartisGouldToint.Chapter06.Section03

/-!
# Cartis–Gould–Toint, Chapter 6: Convexly Constrained Problems

Surface of [cartis2022evaluation] Chapter 6: `minimize_{x ∈ 𝒞} f(x)` over a closed convex
nonempty `𝒞`. This module imports the section modules and adds nothing of its own.

* §6.1, `Chapter06.Section01`: C.CNe; the measures `ω_{f,𝒞,1}`, `ω_{f,𝒞,2}`, `ω_{f,𝒞,3}`
  (6.1.5)–(6.1.10)
* §6.2, `Chapter06.Section02`: ARp-CC (Algorithm 6.2.1), ARp1-CC (Algorithm 6.2.2); Lemmas
  6.2.1–6.2.2, 6.2.4, Theorems 6.2.3, 6.2.5
* §6.3, `Chapter06.Section03`: ARpLE-CC (Algorithm 6.3.1); Theorem 6.3.1

All measures are instances of the backbone `Optimization.formCriticality` over
`Optimization.feasibleSteps` / `Optimization.restrictedSteps`; runs are instances of
`Optimization.IsARRun`. The order of the sought minimizer is an explicit `q ∈ {1, 2, 3}` with
`q ≤ p`, in place of the book's infinite tolerances.

## Deviations from the book

* (6.1.5), (6.1.9) lack a minus sign; the claim that C.CNe ensures that (6.1.1) has a solution is
  false (`not_assumptionCNe_imp_exists_minimizer`).
* Step 2 of ARp-CC can be infeasible for `q ≥ 2`, even at a strict global minimizer
  (`algorithm_6_2_1_not_exists_step`); Theorem 6.2.3 holds for every run, and runs exist for
  `q = 1` and whenever Step 2 is feasible.
* Lemma 6.2.1's (6.2.18)–(6.2.19) need `‖d‖ ≤ 1`; Lemma 6.2.2's constants have `(p+1)!` for `p!`.
* Theorem 6.3.1: "for" is "or", `2^*` is `2^i`; the test (6.3.2) is written multiplicatively, and
  the display before (6.3.3) mixes scaled and unscaled measures (`arpleCC_decrease` is the decrease
  that holds).

## Not formalized

The remarks on the (dis)continuity of `ω_{f,𝒞,2}(x, 0)`, on computational cost and on norms other
than the Euclidean one.
-/
