/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter05.Section01

/-!
# Cartis, Gould and Toint, Appendix B: Appendix to Chapter 5

This module formalizes the part of Appendix B of [cartis2022evaluation] that belongs to Chapter 5:
Lemma B.5.1 on the positivity of the exponents
$$\iota_j(p, \ell, i) = \frac{2^i - 1}{2^i} - \frac{j(\ell - 1)}{p - j + 1}$$
of (5.1.21), (5.1.23) and (5.1.25), defined in `CartisGouldToint.Chapter05.iota`. The proofs of
Lemmas 5.1.3 and 5.1.5 and of Theorems 5.3.3–5.3.9 that the book gives in this appendix are the
proofs of those results in Chapter 5 and in the backbone module
`Numlib.Optimization.Complexity.GapRecurrence`.

## Main results

* Lemma B.5.1, `CartisGouldToint.AppendixB.lemma_B_5_1`: the exponents $\iota_1(p, p, i)$,
  $\iota_2(p, p/2, i)$ and $\iota_3(p, p/3, i)$ are positive when $i$ is large enough.

## Deviations from the source

* **Lemma B.5.1** (typo). The statement lists $\iota_1, \iota_2, \iota_1$; the third exponent is
  $\iota_3$. The proof writes $\iota_1$ for $\iota_2$ and $\iota_3$ in its second and third parts.
  See `CartisGouldToint.AppendixB.lemma_B_5_1`.
* **Lemma B.5.1** (reading). The conditions $i > \log_2 p$, $i > \log_2(p - 1)$ and
  $i > \log_2(p - 2)$ are written $p < 2^i$, $p - 1 < 2^i$ and $p - 2 < 2^i$. These forms are
  equivalent, and they have a meaning also when the logarithm has none. See
  `CartisGouldToint.AppendixB.lemma_B_5_1`.
-/

namespace CartisGouldToint.AppendixB

open CartisGouldToint.Chapter05

/-- **Lemma B.5.1** of [cartis2022evaluation]. Let $p, i \in \mathbb{N}$. Then:

* if $p \ge 1$ and $p < 2^i$, then $\iota_1(p, p, i) > 0$;
* if $p > 0$ is a multiple of $2$ and $p - 1 < 2^i$, then $\iota_2(p, p/2, i) > 0$;
* if $p > 0$ is a multiple of $3$ and $p - 2 < 2^i$, then $\iota_3(p, p/3, i) > 0$.

**Typo.** The statement of the book lists the exponents $\iota_1, \iota_2, \iota_1$; the third
one is $\iota_3$. The proof writes $\iota_1$ for $\iota_2$ and $\iota_3$ in its second and third
parts.

**Reading.** The book's conditions $i > \log_2 p$, $i > \log_2(p - 1)$ and $i > \log_2(p - 2)$
are written $p < 2^i$, $p - 1 < 2^i$ and $p - 2 < 2^i$. These forms are equivalent, and they
have a meaning also when the logarithm has none.

The exponents are `CartisGouldToint.Chapter05.iota`, with $p/2$ and $p/3$ computed in
$\mathbb{R}$. -/
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
