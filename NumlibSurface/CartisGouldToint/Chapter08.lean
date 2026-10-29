import NumlibSurface.CartisGouldToint.Chapter08.Section01
import NumlibSurface.CartisGouldToint.Chapter08.Section02
import NumlibSurface.CartisGouldToint.Chapter08.Section03

/-!
# Cartis–Gould–Toint, Chapter 8: Subproblem Fundamentals

Surface of [cartis2022evaluation] Chapter 8: the trust-region subproblem (8.1.2) and the
regularization subproblem (8.1.3) of a quadratic model in a scaled norm `‖·‖_M`, the secular
function and its transformed versions, global optimality and the hard case. This module imports
the section modules and adds nothing of its own.

* §8.1, `Chapter08.Section01`: `‖·‖_M`, the models (8.1.1), (8.1.4) and the two subproblems
* §8.2, `Chapter08.Section02`: the secular function; Lemmas 8.2.1, 8.2.3, Corollary 8.2.4, Theorems
  8.2.2, 8.2.5–8.2.8
* §8.3, `Chapter08.Section03`: the sets `𝓝`, `𝓛`, `𝓖`; Algorithms 8.3.1–8.3.2; Corollaries
  8.3.1–8.3.2

Conventions shared by Chapters 8–11: vectors in `EuclideanSpace ℝ (Fin n)`, `H` symmetric, `M`
symmetric positive definite, eigenvalues of the pencil `(H, M)` via `Matrix.pencilEigenvalues`.
Every statement is transported through the `M`-inner product space `Subproblem.ScaledSpace` to the
operator backbone `Numlib.Optimization.Subproblem`. Appendix B's Lemmas B.8.1–B.8.2 are in
`AppendixB.Chapter08`.

## Deviations from the book

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* Lemma 8.2.1: **reading**, `π(λₛ) > τ(λₛ)` is a right limit (`λₛ` may be a pole), and `τ` is
  right-continuous at `λₛ` (`lemma_8_2_1`).
* Lemma 8.2.3, Theorem 8.2.5: **false** strict inequalities for `g = 0`, and for `β = -1/2` when
  `g = M v` for a generalized eigenvector `v` (`π(λ; -1/2)` is then affine); proved with these
  cases excluded, and `δ ≠ 0` in Theorem 8.2.5 (`lemma_8_2_3_strict`, `theorem_8_2_5_strict`).
* Corollary 8.2.4: **gap**, needs `g ≠ 0`; the starting values "`π(λₛ; β)`" are right limits,
  possibly `+∞` (`corollary_8_2_4`, `corollary_8_2_4_tendsto_lambdaS`).
* §8.3, `𝓝`, `𝓛`, `𝓖`: **false** set-builder descriptions when `λ₁ > 0`; the interval forms, which
  partition `ℝ`, are used (`setL_tr_union_setG_tr`).
* §8.3: **typo**, the transformed target is `(λ/σ)^{2β/(r-2)}`; Algorithm 8.3.1 must exclude
  `β = 0` (`algorithm_8_3_1`).
* Corollaries 8.3.1–8.3.2: **gap**, when `λ₁` is multiple one eigenvector does not parametrize all
  minimizers (any generalized eigenvector for `λ₁` is allowed), and the minimum-norm solution is
  in the `M`-norm (`corollary_8_3_1`, `corollary_8_3_2`).
* Corollary 8.3.2, boundary form: **false** for interior solutions with `λ* = 0`; stated for
  `λ* > 0` (`corollary_8_3_2`).
* Theorem 8.2.2: **reading**, holds for every `k`, not only `k > 0` (`theorem_8_2_2`).
-/
