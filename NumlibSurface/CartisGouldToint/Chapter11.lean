import NumlibSurface.CartisGouldToint.Chapter11.Section01
import NumlibSurface.CartisGouldToint.Chapter11.Section02
import NumlibSurface.CartisGouldToint.Chapter11.Section03

/-!
# Cartis–Gould–Toint, Chapter 11: Variable Scaling and Other Practicalities

Surface of [cartis2022evaluation] Chapter 11. The chapter has no numbered results; the surface
states its checkable displayed claims. Conventions as in Chapter 8. This module imports the section
modules and adds nothing of its own.

* §11.1, `Chapter11.Section01`: the modified absolute value (11.1.4), the ideal scaling
  (11.1.2)–(11.1.7), the explicit diagonal solutions (§11.1.3), indefinite factorizations (§11.1.4)
* §11.2, `Chapter11.Section02`: radius/weight asymptotics (11.2.3)–(11.2.6)
* §11.3, `Chapter11.Section03`: least-squares models (11.3.1)–(11.3.3)

## Deviations from the book

* (11.1.6) regularizes `‖sᴰ‖` (printed `‖s‖`); the cases of (11.1.7) need `≥`, `≤`.
* §11.1.3, regularization: the secular equation has right-hand side `(λ/σ)^{2/(r-2)}` (printed
  `(λ²/σ²)^{2/(r-2)}`), the hard case occurs iff `½‖gᴰ‖ ≤ σ^{-1/(r-2)}` (printed `≥`), and then
  `∑ αᵢ² = σ^{-2/(r-2)} - ¼‖gᴰ‖²` (printed as a product).
* (11.2.3) and (11.2.5) are printed inverted: `λ ≈ ‖g‖_{M⁻¹}/Δ` and `σ ≈ ‖g‖_{M⁻¹}/Δ^{r-1}`, as the
  derivation, Table 11.2.1 and the rule (11.2.6) confirm.

## Not formalized

The practical update rules (11.2.1)–(11.2.2), which are parameter choices, and the remarks on
Krylov and LSQR methods in §11.3.
-/
