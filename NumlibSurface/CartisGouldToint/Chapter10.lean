import NumlibSurface.CartisGouldToint.Chapter10.Section01
import NumlibSurface.CartisGouldToint.Chapter10.Section02
import NumlibSurface.CartisGouldToint.Chapter10.Section03

/-!
# Cartis–Gould–Toint, Chapter 10: Step Computation without Factorizations

Surface of [cartis2022evaluation] Chapter 10: the subproblems of Chapter 8 restricted to the Krylov
subspaces `𝒦ₖ = 𝒦(M⁻¹H, M⁻¹g, k)`, computed by the preconditioned Lanczos method, and the
convergence of the subspace solutions. Conventions as in Chapter 8. This module imports the section
modules and adds nothing of its own.

* §10.1, `Chapter10.Section01`: Krylov subspaces, the preconditioned Lanczos method (Algorithm
  10.1.1), the hard-case obstruction
* §10.2, `Chapter10.Section02`: regularization: Algorithms 10.2.1–10.2.2, Lemma 10.2.1, Theorem
  10.2.2, Corollary 10.2.3
* §10.3, `Chapter10.Section03`: trust region: Lemma 10.3.1, Theorem 10.3.2, Corollary 10.3.3

Krylov subspaces are the backbone `Krylov.subspace`; the proofs are in the backbone modules
`Numlib.Optimization.Subproblem.Krylov`, `Numlib.Optimization.Subproblem.KrylovConvergence`,
`Numlib.LinearAlgebra.Matrix.TridiagonalLDL` and
`Numlib.LinearAlgebra.Matrix.InverseDecay`. `‖M⁻¹H‖` is the
operator norm induced by `‖·‖_M`. Appendix B's Lemma B.10.1 is in `AppendixB.Chapter10`.

## Deviations from the book

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* (10.1.7): **typo**, the leading block of `Tₖ` is `T_{k-1}`, not `T_{k-1}⁻¹`, and the Krylov
  subspaces nest as a span of a union (`algorithm_10_1_1_spec`).
* (B.10.4): **reading**, `‖M^{-1/2} H M^{-1/2}‖` is the operator norm of `M⁻¹H` induced by `‖·‖_M`
  (the Euclidean norm is only an upper bound) (`AppendixB.lemma_B_10_1`).
* Corollaries 10.2.3, 10.3.3: **false** iteration bounds when the logarithm is negative, undefined
  for `κ* = 1`; read with `⌈·⌉₊`, with a separate `κ* = 1` case and `g ≠ 0` (`corollary_10_2_3`,
  `corollary_10_3_3`).
* Lemma 10.2.1: **typo**, the problem is (8.1.3), not the model (8.1.4) (`lemma_10_2_1`).

## Not formalized

Every numbered result of the chapter is formalized.
-/
