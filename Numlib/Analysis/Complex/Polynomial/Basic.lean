/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Complex.Polynomial.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The complex roots of a real polynomial

Let $p$ be a polynomial with real coefficients, viewed as a polynomial over $\mathbb{C}$. This
module proves that its complex roots, counted with multiplicity, are closed under complex
conjugation: $\lambda$ is a root of multiplicity $m$ if and only if $\bar\lambda$ is.

## Main results

* `Polynomial.roots_map_algebraMap_conj`: conjugation maps the multiset of complex roots of a real
  polynomial onto itself.
-/

namespace Polynomial

/-- **The roots of a real polynomial are closed under conjugation**, with multiplicities. Let
$p \in \mathbb{R}[X]$, and let $p_{\mathbb{C}} \in \mathbb{C}[X]$ be $p$ with its coefficients
viewed as complex numbers. Then the multiset of roots of $p_{\mathbb{C}}$, with each root
repeated by its multiplicity, is unchanged when every root is replaced by its complex conjugate.

$p_{\mathbb{C}}$ is `p.map (algebraMap ℝ ℂ)`, its multiset of roots is `Polynomial.roots`, and
complex conjugation is `starRingEnd ℂ`. -/
theorem roots_map_algebraMap_conj (p : ℝ[X]) :
    (p.map (algebraMap ℝ ℂ)).roots.map (starRingEnd ℂ) = (p.map (algebraMap ℝ ℂ)).roots := by
  rw [roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
    (splits_iff_card_roots.1 (IsAlgClosed.splits _)), Polynomial.map_map]
  congr 2
  exact RingHom.ext fun x => by simp

end Polynomial
