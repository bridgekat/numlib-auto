/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.SpecialFunctions.SqrtBound

/-!
# Cartis, Gould and Toint, Appendix B: Appendix to Chapter 3

This module formalizes the part of Appendix B of [cartis2022evaluation] that belongs to Chapter 3:
the algebraic Lemma B.3.1, which the proof of Lemma 3.4.3 uses. For $a, b > 0$ and $c \ge 0$ it
bounds $-b + \sqrt{b^2 + ac}$ below by $(-b + \sqrt{b^2 + a}) \min(1, c)$. The proof specializes the
backbone theorem `neg_add_sqrt_sq_add_mul_ge`. The proofs of Theorems 3.4.11, 3.4.12, Lemmas
3.5.1–3.5.3 and Theorem 3.5.4 that the book gives in this appendix are the proofs of those results
in Chapter 3.

## Main results

* Lemma B.3.1, `CartisGouldToint.AppendixB.lemma_B_3_1`: the inequality (B.3.1).
-/

namespace CartisGouldToint.AppendixB

/-- **Lemma B.3.1** of [cartis2022evaluation]. Let $a > 0$, $b > 0$ and $c \ge 0$. Then (B.3.1)
holds:
$$-b + \sqrt{b^2 + ac} \ge \bigl(-b + \sqrt{b^2 + a}\bigr) \min(1, c).$$

The proof does not use the hypothesis $b > 0$. -/
theorem lemma_B_3_1 {a b c : ℝ} (ha : 0 < a) (_hb : 0 < b) (hc : 0 ≤ c) :
    -b + √(b ^ 2 + a * c) ≥ (-b + √(b ^ 2 + a)) * min 1 c :=
  neg_add_sqrt_sq_add_mul_ge ha.le hc

end CartisGouldToint.AppendixB
