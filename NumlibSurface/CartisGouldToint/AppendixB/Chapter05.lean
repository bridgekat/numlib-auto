import NumlibSurface.CartisGouldToint.Chapter05.Section01

/-!
# Cartis–Gould–Toint, Appendix B: Appendix to Chapter 5

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Appendix B, "Appendix to
Chapter 5": Lemma B.5.1 on the positivity of the residual exponents
`ι_j(p, ℓ, i) = (2^i - 1)/2^i - j (ℓ - 1)/(p - j + 1)` of (5.1.21), (5.1.23), (5.1.25)
(`Chapter05.iota`). The appendix proofs of Lemmas 5.1.3 and 5.1.5 and of Theorems 5.3.3–5.3.9
are those of the corresponding Chapter 5 results (and of the backbone
`Optimization.GapRecurrence`).

## Main results

* `lemma_B_5_1` — Lemma B.5.1.

## Deviations from the book

* The statement lists `ι₁, ι₂, ι₁`; the third exponent is `ι₃`. The proof writes `ι₁` for `ι₂`
  and `ι₃` in its second and third parts.
* The conditions `i > log₂ p`, `i > log₂ (p - 1)`, `i > log₂ (p - 2)` are written `p < 2^i`,
  `p - 1 < 2^i`, `p - 2 < 2^i` (equivalent, and meaningful also when the logarithm is not).
-/

namespace CartisGouldToint.AppendixB

open CartisGouldToint.Chapter05

/-- **Lemma B.5.1** ([cartis2022evaluation]): `ι₁(p, p, i) > 0` when `p ≥ 1` and `p < 2^i`;
`ι₂(p, p/2, i) > 0` when `p` is a positive multiple of two and `p - 1 < 2^i`; and
`ι₃(p, p/3, i) > 0` when `p` is a positive multiple of three and `p - 2 < 2^i`. -/
theorem lemma_B_5_1 {p i : ℕ} :
    (1 ≤ p → p < 2 ^ i → 0 < iota 1 p p i) ∧
    (0 < p → 2 ∣ p → (p : ℝ) - 1 < 2 ^ i → 0 < iota 2 p ((p : ℝ) / 2) i) ∧
    (0 < p → 3 ∣ p → (p : ℝ) - 2 < 2 ^ i → 0 < iota 3 p ((p : ℝ) / 3) i) := by
  refine ⟨fun hp hi => (lemma_5_1_6 hp).1 p i rfl hi, fun hp h2 hi => ?_, fun hp h3 hi => ?_⟩
  · obtain ⟨ℓ, rfl⟩ := h2
    have hle : 2 * ℓ - 1 < 2 ^ i := by
      have : ((2 * ℓ - 1 : ℕ) : ℝ) < 2 ^ i := by
        push_cast [Nat.cast_sub (show 1 ≤ 2 * ℓ by omega)]
        push_cast at hi
        exact hi
      exact_mod_cast this
    have := ((lemma_5_1_6 (p := 2 * ℓ) (by omega)).2.2.1 ℓ i (even_two_mul ℓ) rfl hle).2
    convert this using 2
    push_cast
    ring
  · obtain ⟨ℓ, rfl⟩ := h3
    have hle : 3 * ℓ - 2 < 2 ^ i := by
      have : ((3 * ℓ - 2 : ℕ) : ℝ) < 2 ^ i := by
        push_cast [Nat.cast_sub (show 2 ≤ 3 * ℓ by omega)]
        push_cast at hi
        exact hi
      exact_mod_cast this
    have := ((lemma_5_1_6 (p := 3 * ℓ) (by omega)).2.2.2.2.1 ℓ i rfl hle).2.2
    convert this using 2
    push_cast
    ring

end CartisGouldToint.AppendixB
