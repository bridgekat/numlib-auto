import NumlibSurface.CartisGouldToint.Chapter05.Section01
import NumlibSurface.CartisGouldToint.Chapter05.Section02
import NumlibSurface.CartisGouldToint.Chapter05.Section03
import NumlibSurface.CartisGouldToint.Chapter05.Section04
import NumlibSurface.CartisGouldToint.Chapter05.Section05

/-!
# Cartis–Gould–Toint, Chapter 5: Structured Problems

Surface of [cartis2022evaluation] Chapter 5: problems whose structure improves on the bounds of
Chapters 2–4. This module imports the section modules and adds nothing of its own.

* §5.1, `Chapter05.Section01`: least squares / least Euclidean norm via `Φ_ℓ = ‖r‖^ℓ/ℓ`, ARpLE
  (Algorithm 5.1.1); Lemmas 5.1.1–5.1.6, Theorem 5.1.7
* §5.2, `Chapter05.Section02`: partially separable functions (5.2.1)–(5.2.2) (no numbered results)
* §5.3, `Chapter05.Section03`: measure-dominated problems, the classes `ARψ,ν`, `TRψ,ν`; Lemmas
  5.3.1, 5.3.6, Theorems 5.3.2–5.3.5, 5.3.7–5.3.12
* §5.4, `Chapter05.Section04`: AR2 under strict local convexity (5.4.3); Lemmas 5.4.1–5.4.3, Theorem
  5.4.4
* §5.5, `Chapter05.Section05`: universal regularization ARp-H (Algorithm 5.5.1), f.DpH; Lemmas
  5.5.1–5.5.6, Theorem 5.5.7

ARpLE is the backbone `Optimization.IsARpRun` applied to `Φ_ℓ`; the classes of §5.3 are
`Optimization.IsARLikeRun`, `Optimization.IsTRLikeRun`, whose analysis is the scalar recurrences of
`Optimization.GapRecurrence`; ARp-H is an instance of `Optimization.IsARRun`. Rates and "at most `N`
iterations" are stated as upper bounds along the iterations. Appendix B's Lemma B.5.1 is in
`AppendixB.Chapter05`.

## Deviations from the book

* ARpLE's third-order test (Algorithm 5.1.1) drops `𝓜_k ≠ ∅` (with it the proof of
  Theorem 5.1.7 fails when `𝓜_{k+1} = ∅`), and third-order runs need not exist; existence is
  proved for `q ≤ 2`. Theorem 5.1.7's OCR exponents and its "and"/"or" in (5.1.51) are restored, and
  the theorem is proved in a general form (`theorem_5_1_7_of_iota_nonneg`).
* §5.3: several Appendix B constants for Theorems 5.3.3, 5.3.5, 5.3.9 are corrected (recorded in
  `Optimization.GapRecurrence`); Lemma 5.3.6 (ii)'s "`Γ ≥ 1`" means `Γ ≥ Γ□`; measure versions take
  up to two successful iterations beyond the gap count.
* Lemma 5.4.2: the step bound (5.4.8) is false as printed (it uses `λ_min ≥ λ_*` where only `λ_*/2`
  is available and drops a factor `‖s_k‖`); the correct constant is `κ_s = 2(1 + θ₁)/λ_*`, which
  changes `ζ_*` (5.4.5).
* Lemma 5.4.3 and Theorem 5.4.4: the count `log₂ log₂(ζ/ε)` is one too small in the worst case;
  it is `⌈log₂ log₂(ζ_*/ε)⌉₊`.
* Algorithm 5.5.1 Step 4: the third case must be "`ρ_k < η₁`, or (5.5.10) fails, or (5.5.11)
  fails". Theorem 5.5.7's evaluation counts need `+ 2` (evaluations at `x₀` and at every trial
  point); Lemma 5.5.4's proof has `ε₁` for `ε₂`.

## Not formalized

The examples of §5.3.1 other than full-rank least squares (convex functions on a ball, strongly
convex functions, `‖x‖^{2i}`); the claim that TR1/TR2 belong to `TRψ,ν` with uniform constants;
the structured trust regions of the Notes to §5.2.
-/
