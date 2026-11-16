/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Integral.IntegrableOn`, beside `IntegrableOn.of_bound`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability from a bound and a support condition

Let $s$ be a measurable set and let $K$ be a set of finite measure. A function that is almost
everywhere strongly measurable on $s$, bounded on $s$, and zero on $s \setminus K$ is integrable on
$s$. The bound gives integrability on $s \cap K$, and the function is zero on the rest of $s$. In
this form, a compactly supported vector field of class $C^1(\bar\Omega)$ is integrable on an
unbounded set $\Omega$.

## Main results

* `integrableOn_of_forall_norm_le_of_eq_zero`: the statement above.
-/

open MeasureTheory Set

/-- Let $\mu$ be a measure on $X$, let $G$ be a normed group, let $s \subseteq X$ be measurable, and
let $K \subseteq X$ satisfy $\mu(K) < \infty$. Let $\varphi \colon X \to G$ be almost everywhere
strongly measurable for the restriction of $\mu$ to $s$. If there is $M \in \mathbb{R}$ with
$\|\varphi(y)\| \le M$ for every $y \in s$, and $\varphi(y) = 0$ for every
$y \in s \setminus K$, then $\varphi$ is integrable on $s$.

The set $K$ need not be measurable. -/
theorem integrableOn_of_forall_norm_le_of_eq_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {G : Type*} [NormedAddCommGroup G] {φ : X → G} {s K : Set X}
    (hs : MeasurableSet s) (hK : μ K ≠ ⊤) (hφ : AEStronglyMeasurable φ (μ.restrict s)) {M : ℝ}
    (hM : ∀ y ∈ s, ‖φ y‖ ≤ M) (h0 : ∀ y ∈ s, y ∉ K → φ y = 0) : IntegrableOn φ s μ := by
  have h1 : IntegrableOn φ (s ∩ K) μ := by
    refine IntegrableOn.of_bound ((measure_mono inter_subset_right).trans_lt hK.lt_top)
      (hφ.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) M ?_
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left (ae_restrict_of_forall_mem hs hM)
  exact h1.of_forall_sdiff_eq_zero hs fun y hy ↦ h0 y hy.1 fun hK' ↦ hy.2 ⟨hy.1, hK'⟩
