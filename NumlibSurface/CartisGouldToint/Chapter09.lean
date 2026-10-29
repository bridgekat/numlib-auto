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

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* Algorithm 9.1.1: **typo**, its vectors are those of (8.2.29) up to the sign `(-1)ᵏ`, harmless
  for the values `π⁽ʲ⁾` (`algS_eq`, `algorithm_9_1_1`); the Cholesky remark after it has a
  spurious factor `2` (`corollary_9_1_1`).
* Algorithm 9.2.1: **gap**, the printed contraction factor is not uniformly below `1`, and finite
  termination needs the initial lower bound strictly below `λ*` (`algorithm_9_2_1_terminates`).
* Theorem 9.3.1: **gap**, omits the hypothesis `z₀ ∈ 𝒵₁`, read in the `M`-inner product
  (`theorem_9_3_1`).
* Theorem 9.3.2: **false** with the Euclidean `λ_min` in (9.3.14c) when `M ≠ I`; stated with the
  `M`-scaled norms and eigenvalue (`theorem_9_3_2`).
* (9.3.6): **false** middle term; only the outer inequality used by (9.3.7) is stated
  (`exists_abs_sub_le_of_eigen`). (9.4.5): **false** as an equivalence; the implication holds.

## Not formalized

The safeguarded update (9.3.10)–(9.3.12) and the overall procedure of §9.3.7 (heuristics, whose
admissible choices are covered by `algorithm_9_2_1`); the closing advice of §9.4.2 to stop
Algorithm 9.2.1 as soon as (9.4.3) or (9.4.4) holds (a heuristic procedure; the sufficient
conditions it relies on are `test_9_4_3_of_9_4_6`, `test_9_4_4_of_9_4_6`, `test_9_4_3_of_9_4_7`
and their `𝓛`/`𝓖` forms); the Gertz–Gill criterion (9.4.8) of the Notes (quoted from [179, 292]
without statement of what "suitable approximate solution" means).
-/
