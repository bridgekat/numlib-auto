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

* Lemma 8.2.1: `π(λₛ) > τ(λₛ)` is read as a right limit (`λₛ` may be a pole), and `τ` is assumed
  right-continuous at `λₛ`.
* Lemma 8.2.3 and Theorem 8.2.5: the strict inequalities need `g ≠ 0` and fail for `β = -1/2`
  exactly when `g = M v` for a generalized eigenvector `v` (`π(λ; -1/2)` is then affine); Theorem
  8.2.5 also needs `δ ≠ 0`, Corollary 8.2.4 needs `g ≠ 0`.
* §8.3: the set-builder descriptions of `𝓝`, `𝓛`, `𝓖` disagree with the interval forms when
  `λ₁ > 0`; the interval forms, which partition `ℝ`, are used. The transformed target is
  `(λ/σ)^{2β/(r-2)}`, and Algorithm 8.3.1 must exclude `β = 0`.
* Corollaries 8.3.1–8.3.2: when `λ₁` is multiple, a single eigenvector does not parametrize all
  minimizers (any generalized eigenvector `v` for `λ₁` is allowed); the minimum-norm solution is
  taken in the `M`-norm; in Corollary 8.3.2 the boundary form fails for interior solutions with
  `λ* = 0`.

## Not formalized

The starting values of Corollary 8.2.4 (the right limits of `π(λ; β)` at `λₛ`, possibly `+∞`);
only monotonicity, convexity/concavity and the limits at `+∞` are stated.
-/
