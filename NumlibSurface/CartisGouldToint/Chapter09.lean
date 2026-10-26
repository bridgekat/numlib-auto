import NumlibSurface.CartisGouldToint.Chapter09.Section01
import NumlibSurface.CartisGouldToint.Chapter09.Section02
import NumlibSurface.CartisGouldToint.Chapter09.Section03
import NumlibSurface.CartisGouldToint.Chapter09.Section04

/-!
# Cartis–Gould–Toint, Chapter 9: Step Computation with Factorizations

Surface of [cartis2022evaluation] Chapter 9: solving the subproblems of Chapter 8 with
factorizations of `H + λM`. Conventions as in Chapter 8, whose definitions are reused. This module
imports the section modules and adds nothing of its own.

* §9.1, `Chapter09.Section01`: derivatives of `π` from `LDLᵀ` factors; Algorithm 9.1.1, Corollary
  9.1.1
* §9.2, `Chapter09.Section02`: safeguarded bracketing to reach `𝓛` (Algorithm 9.2.1)
* §9.3, `Chapter09.Section03`: the regularization subproblem: bounds (9.3.3)–(9.3.7), Algorithm
  9.3.1, Theorems 9.3.1–9.3.2
* §9.3.1, also in `Chapter09.Section03`: `‖H‖₂ ≤ min(‖H‖_∞, ‖H‖_F)`
  (`opNorm_le_min_linfty_frobenius`, `extremeEigenvalue_bounds_9_3_1`)
* §9.4, `Chapter09.Section04`: the trust-region subproblem: bounds (9.4.1), (9.4.5)–(9.4.7), the
  early-termination tests (9.4.2)–(9.4.4)

The proofs are in the backbone modules `Bracketing`, `InverseIteration`, `Stopping` and
`TrustRegion` of `Numlib.Optimization.Subproblem`.

## Deviations from the book

* Algorithm 9.1.1 computes the derivative vectors of (8.2.29) up to the sign `(-1)ᵏ` (harmless for
  the values `π⁽ʲ⁾`); the Cholesky remark after it has a spurious factor `2`.
* Algorithm 9.2.1: the printed contraction factor is not uniformly below `1`; finite termination
  needs the initial lower bound strictly below `λ*`.
* Theorem 9.3.1 omits the hypothesis `z₀ ∈ 𝒵₁`, which must be read in the `M`-inner product.
* Theorem 9.3.2 is false with the Euclidean `λ_min` in (9.3.14c) when `M ≠ I`; it is stated with
  the `M`-scaled norms and eigenvalue.
* (9.3.6): the middle term is not a valid bound as printed; only the outer inequality used by
  (9.3.7) is stated. (9.4.5) is an implication, not an equivalence.

## Not formalized

The safeguarded update (9.3.10)–(9.3.12) and the overall procedure of §9.3.7 (heuristics, whose
admissible choices are covered by `algorithm_9_2_1`); the closing advice of §9.4.2 to stop
Algorithm 9.2.1 as soon as (9.4.3) or (9.4.4) holds (a heuristic procedure; the sufficient
conditions it relies on are `test_9_4_3_of_9_4_6`, `test_9_4_4_of_9_4_6`, `test_9_4_3_of_9_4_7`
and their `𝓛`/`𝓖` forms); the Gertz–Gill criterion (9.4.8) of the Notes (quoted from [179, 292]
without statement of what "suitable approximate solution" means).
-/
