import NumlibSurface.CartisGouldToint.AppendixA.Section08
import NumlibSurface.CartisGouldToint.AppendixA.Section09
import NumlibSurface.CartisGouldToint.AppendixA.Section10

/-!
# Cartis–Gould–Toint, Appendix A: Background and General Technical Results

Surface of [cartis2022evaluation] Appendix A. Only §§A.8–A.10 contain numbered results; the
notation of §§A.1–A.7 (norms, eigenvalues, tensors) is realized by Mathlib and the backbone: the
tensor norm (A.7) is the operator norm of continuous multilinear maps, `∇^j f(x)` is
`iteratedFDeriv ℝ j f x`, `λ_min` is `minCurvature`. This module imports the section modules and
adds nothing of its own.

* §A.8, `AppendixA.Section08`: Taylor's theorem: Theorems A.8.1–A.8.3, A.8.5, Corollary A.8.4,
  (A.16)
* §A.9, `AppendixA.Section09`: Hermite interpolation: Theorems A.9.1–A.9.2
* §A.10, `AppendixA.Section10`: partial sums of the exponential series: Lemma A.10.1, (A.34)–(A.36)

## Deviations from the book

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* Theorem A.8.5: **false** for `L < 0` on `ℝ⁰`; `L ≥ 0` is assumed (`theorem_A_8_5`). Theorem
  A.8.2: **gap**, assumes `h ≠ 0` (`theorem_A_8_2`).
* Theorem A.9.2: **typo**, the index range of `s_k > 0` is `k < k_e` and the bound is for `x ∈ ℝ`
  (printed `x ∈ ℝⁿ`); `p > 0` is dropped (`theorem_A_9_2`).

## Not formalized

Every numbered result of the appendix is formalized.
-/
