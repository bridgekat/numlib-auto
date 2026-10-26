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

* Theorem A.8.5 assumes `L ≥ 0` (on `ℝ⁰` it fails for `L < 0`); Theorem A.8.2 assumes `h ≠ 0`.
* Theorem A.9.2: the index range of `s_k > 0` is `k < k_e`, the bound is for `x ∈ ℝ` (printed
  `x ∈ ℝⁿ`), and `p > 0` is not needed.

## Not formalized

Every numbered result of the appendix is formalized.
-/
