import NumlibSurface.CartisGouldToint.AppendixB.Chapter02
import NumlibSurface.CartisGouldToint.AppendixB.Chapter03
import NumlibSurface.CartisGouldToint.AppendixB.Chapter04
import NumlibSurface.CartisGouldToint.AppendixB.Chapter05
import NumlibSurface.CartisGouldToint.AppendixB.Chapter07
import NumlibSurface.CartisGouldToint.AppendixB.Chapter08
import NumlibSurface.CartisGouldToint.AppendixB.Chapter10
import NumlibSurface.CartisGouldToint.AppendixB.Chapter12

/-!
# Cartis–Gould–Toint, Appendix B: Technical Results from Individual Chapters

Surface of [cartis2022evaluation] Appendix B. The appendix mostly contains proofs of chapter
results; those proofs are part of the corresponding chapter declarations. Only the separately
numbered lemmas `Lemma B.N.k` are declarations here, one module `AppendixB.ChapterNN` per chapter
that has them (namespace `CartisGouldToint.AppendixB`). Where a chapter result needs such a lemma,
both specialize a common backbone result, so the surface dependencies still run forward. This
module imports the section modules and adds nothing of its own.

* Chapter 2, `AppendixB.Chapter02`: Lemmas B.2.1–B.2.6, the SDEX zig-zag example of Theorem 2.2.5
* Chapter 3, `AppendixB.Chapter03`: Lemma B.3.1 (for Lemma 3.4.3)
* Chapter 4, `AppendixB.Chapter04`: Lemma B.4.1, derivatives of `‖s‖^{p+β}`
* Chapter 5, `AppendixB.Chapter05`: Lemma B.5.1, positivity of the exponents `ι_j`
* Chapter 7, `AppendixB.Chapter07`: Lemma B.7.1 (for Lemma 7.2.3)
* Chapter 8, `AppendixB.Chapter08`: Lemmas B.8.1–B.8.2, Newton and secant iterations
* Chapter 10, `AppendixB.Chapter10`: Lemma B.10.1, decay of inverses of tridiagonal matrices
* Chapter 12, `AppendixB.Chapter12`: Lemma B.12.1, `φ^δ_{f,3} = 0 ⇒ φ^δ_{f,2} = 0`

The appendices to Chapters 9, 13 and 14 contain no separately numbered lemmas.

## Deviations from the book

Kinds (**false**, **gap**, **typo**, **reading**) as in the book index `CartisGouldToint`.

* Lemma B.4.1, (B.4.3): **false** for `β ∈ (0, 1)` (`lemma_B_4_1_iii_false`: `n = 2`, `p = 1`,
  `β = ½`, `s = e₁`); the printed value is the radial value and a lower bound
  (`lemma_B_4_1_iii_radial`), the norm is `O(‖s‖^{β-1})` (`lemma_B_4_1_iii_bound`), and for
  `β = 1`, the case the book uses, (B.4.3) holds (`lemma_B_4_1_iii`).
* Lemma B.8.1: **gap**, needs `θ'(λ*) ≠ 0` (otherwise Newton's method is only linearly convergent)
  (`lemma_B_8_1`); in the concave case the starting condition is `θ(λ₀) < 0` (**typo**, printed
  `> 0`) (`lemma_B_8_1_concave`).
* Lemma B.2.1: **gap**, the bound needs `|f₀|, |g₀|, |H₀| ≤ κ_f` (`lemma_B_2_1_bound`). Lemma B.2.6:
  **gap**, the book's corridor function gives a first *local* line minimizer; the backbone's capped
  square makes it global (`lemma_B_2_6`).
* Lemma B.5.1: **typo**, `ι₁` for `ι₃` (`lemma_B_5_1`). Lemma B.7.1: **reading**, also covers the
  boundary cases `ω = 0`, `ω = ε` used by Lemma 7.2.3 (`lemma_B_7_1`). Lemma B.12.1: **reading**,
  no symmetry of `H`, `T` is needed (`lemma_B_12_1`).

## Not formalized

Every separately numbered lemma of the appendix is formalized.
-/
