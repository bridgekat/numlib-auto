/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TargetResidual

/-!
# Cartis, Gould and Toint, Appendix B: Appendix to Chapter 7

This module formalizes the part of Appendix B of [cartis2022evaluation] that belongs to Chapter 7:
Lemma B.7.1, a global minimization in two variables that the proof of Lemma 7.2.3 uses for the
target decrease (7.2.30). For $0 < \omega < \varepsilon$ the function
$\psi(f, c) = -f + \sqrt{\varepsilon^2 - c^2}$ has the minimum value $\varepsilon - \omega$ on the
disc $f^2 + c^2 \le \omega^2$ (B.7.1), and $(\omega, 0)$ is the only minimizer. The inequality
behind the lemma is the backbone theorem `neg_add_sqrt_sq_sub_sq_ge`.

## Main definitions

* Lemma B.7.1, `CartisGouldToint.AppendixB.psiB71`: the objective $\psi$ of (B.7.1).

## Main results

* Lemma B.7.1, `CartisGouldToint.AppendixB.eq_of_neg_add_sqrt_sq_sub_sq_eq`: the minimum value is
  attained only at $(\omega, 0)$.
* Lemma B.7.1, `CartisGouldToint.AppendixB.lemma_B_7_1`: $(\omega, 0)$ is the unique global
  minimizer, with the value $\varepsilon - \omega$.

## Proof outline

The book's proof uses the KKT conditions. The proof here is an elementary monotonicity argument.

## Implementation notes

* The backbone inequality `neg_add_sqrt_sq_sub_sq_ge` also covers the boundary cases $\omega = 0$
  and $\omega = \varepsilon$, which the proof of Lemma 7.2.3 needs, since there
  $\omega \in [0, \varepsilon_0]$. The lemma as printed assumes $0 < \omega < \varepsilon$.

## Deviations from the source

* **Totalized square root.** The objective in (B.7.1) is totalized outside the feasible disk. See
  `CartisGouldToint.AppendixB.psiB71`.
* **Explicit uniqueness.** Lemma B.7.1 explicitly proves uniqueness of the minimizer. See
  `CartisGouldToint.AppendixB.eq_of_neg_add_sqrt_sq_sub_sq_eq`,
  `CartisGouldToint.AppendixB.lemma_B_7_1`.
* **Lemma B.7.1** (generalization). The book speaks of "the" global minimizer without a proof of
  uniqueness; the uniqueness of the minimizer $(\omega, 0)$ is also proved. See
  `CartisGouldToint.AppendixB.lemma_B_7_1`.
-/

namespace CartisGouldToint.AppendixB

/-- **Lemma B.7.1** of [cartis2022evaluation], the objective. For $\varepsilon \in \mathbb{R}$, the
objective of (B.7.1) is $\psi(f, c) = -f + \sqrt{\varepsilon^2 - c^2}$ for
$(f, c) \in \mathbb{R}^2$.

The square root is the real square root of Mathlib, which is $0$ at negative arguments; on the
disc of Lemma B.7.1 its argument is positive.

**Reading.** The objective has a real value even outside the disk when the radicand is negative,
where Lean returns zero for the square-root term. On the feasible disk the original formula applies.
-/
noncomputable def psiB71 (ε : ℝ) (p : ℝ × ℝ) : ℝ := -p.1 + √(ε ^ 2 - p.2 ^ 2)

/-- Let $0 \le \omega < \varepsilon$, and let $u, v \in \mathbb{R}$ with $u^2 + v^2 \le \omega^2$
and $-u + \sqrt{\varepsilon^2 - v^2} = \varepsilon - \omega$. Then $u = \omega$ and $v = 0$.
This gives the uniqueness of the minimizer in Lemma B.7.1.

**Generalization.** The result and equality-case lemma show that only the specified feasible point
attains the stated global value.
-/
theorem eq_of_neg_add_sqrt_sq_sub_sq_eq {ω ε u v : ℝ} (hω : 0 ≤ ω) (hωε : ω < ε)
    (huv : u ^ 2 + v ^ 2 ≤ ω ^ 2) (heq : -u + √(ε ^ 2 - v ^ 2) = ε - ω) : u = ω ∧ v = 0 := by
  set A := √(ε ^ 2 - v ^ 2) with hA
  set B := √(ω ^ 2 - v ^ 2) with hB
  have hvω : v ^ 2 ≤ ω ^ 2 := by nlinarith
  have hA2 : A ^ 2 = ε ^ 2 - v ^ 2 := Real.sq_sqrt (by nlinarith)
  have hB2 : B ^ 2 = ω ^ 2 - v ^ 2 := Real.sq_sqrt (by linarith)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBω : B ≤ ω := by
    rw [hB, Real.sqrt_le_left hω]
    nlinarith
  have huB : u ≤ B := (le_abs_self u).trans (Real.abs_le_sqrt (by linarith))
  -- `A - B ≤ ε - ω` and `(A - B)(A + B) = (ε - ω)(ε + ω)` force `A + B ≥ ε + ω`, hence `A ≥ ε`.
  have hAB : A - B ≤ ε - ω := by linarith
  have hprod : (A - B) * (A + B) = (ε - ω) * (ε + ω) := by nlinarith
  have hApos : B < A := by nlinarith
  have hsum : ε + ω ≤ A + B := by
    by_contra hlt
    push Not at hlt
    have : (A - B) * (A + B) < (ε - ω) * (ε + ω) :=
      mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hAB hlt (by linarith) (by linarith)
    linarith
  have hεA : ε ≤ A := by linarith
  have hv : v = 0 := by nlinarith
  subst hv
  have hBeq : B = ω := by rw [hB]; simp [Real.sqrt_sq hω]
  have hAeq : A = ε := by rw [hA]; simp [Real.sqrt_sq (hω.trans hωε.le)]
  exact ⟨by linarith, rfl⟩

/-- **Lemma B.7.1** of [cartis2022evaluation]. Let $0 < \omega < \varepsilon$, let $K = \{(f, c) \in
\mathbb{R}^2 : f^2 + c^2 \le \omega^2\}$, and let
$\psi(f, c) = -f + \sqrt{\varepsilon^2 - c^2}$. Then $(\omega, 0) \in K$ is a global minimizer
of $\psi$ on $K$ (B.7.1), its value is $\psi(\omega, 0) = \varepsilon - \omega$, and every
$(f, c) \in K$ with $\psi(f, c) = \varepsilon - \omega$ is equal to $(\omega, 0)$.

**Generalization.** The book speaks of "the" global minimizer without a proof of uniqueness. The
uniqueness of the minimizer is also proved.

The objective is `CartisGouldToint.AppendixB.psiB71 ε`. The minimizer property is `IsMinOn`.

**Generalization.** The result and equality-case lemma show that only the specified feasible point
attains the stated global value.
-/
theorem lemma_B_7_1 {ω ε : ℝ} (hω : 0 < ω) (hωε : ω < ε) :
    let K : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ ω ^ 2}
    (ω, 0) ∈ K ∧ IsMinOn (psiB71 ε) K (ω, 0) ∧ psiB71 ε (ω, 0) = ε - ω ∧
      ∀ p ∈ K, psiB71 ε p = ε - ω → p = (ω, 0) := by
  intro K
  have hval : psiB71 ε (ω, 0) = ε - ω :=
    neg_add_sqrt_sq_sub_zero_sq (hω.le.trans hωε.le)
  refine ⟨by simp [K], fun p hp => ?_, hval, fun p hp hpeq => ?_⟩
  · simp only [Set.mem_ofPred_eq, hval]
    exact neg_add_sqrt_sq_sub_sq_ge hω.le hωε.le hp
  · obtain ⟨h1, h2⟩ := eq_of_neg_add_sqrt_sq_sub_sq_eq hω.le hωε hp hpeq
    exact Prod.ext h1 h2

end CartisGouldToint.AppendixB
