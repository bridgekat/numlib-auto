/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Conn, Gould and Toint, Section 8.3: Rayleigh infima in Hilbert spaces

In an infinite-dimensional real inner product space $E$, a bounded operator $H$ need not have a
least eigenvalue. Section 8.3 of [conn2000trust] uses instead the **Rayleigh infimum** (8.3.3),
$$\lambda_{\min}[H] = \inf_{d \neq 0} \frac{\langle d, H d \rangle}{\|d\|^2}.$$
This module defines it, characterizes its lower bounds by the quadratic form of $H$, and shows that
every number above it is exceeded by the curvature of some unit direction. Such a direction serves
as an approximate eigenpoint direction when no eigenvector attains the infimum.

## Main definitions

* Equation (8.3.3), `ConnGouldToint.Chapter08.hilbertRayleighFloor`: the Rayleigh infimum
  $\lambda_{\min}[H]$.

## Main results

* Equation (8.3.3), `ConnGouldToint.Chapter08.hilbertRayleighFloor_le_iff`:
  $a \le \lambda_{\min}[H]$ if and only if $a \|d\|^2 \le \langle d, H d \rangle$ for every $d$.
* Equation (8.3.3),
  `ConnGouldToint.Chapter08.exists_unit_direction_below_of_hilbertRayleighFloor_lt`: if
  $\lambda_{\min}[H] < a$, some unit vector $d$ has $\langle d, H d \rangle < a$.

## Implementation notes

* The infimum runs over the nonzero vectors of $E$. On the zero space the index set is empty, and
  the Lean value is $0$. The two results assume that $E$ is nontrivial.

## Deviations from the source

* **Equation (8.3.3)** (generalization). The Rayleigh infimum is defined on real inner-product
  spaces without a completeness assumption. The direction result gives a unit vector below any
  strict upper threshold on the infimum. See `ConnGouldToint.Chapter08.hilbertRayleighFloor` and
  `ConnGouldToint.Chapter08.exists_unit_direction_below_of_hilbertRayleighFloor_lt`.
-/

open Set
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter08

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (8.3.3)** of [conn2000trust]. For a continuous linear operator $H$ on a real inner
product space $E$, the **Rayleigh infimum** is
$$\lambda_{\min}[H] = \inf_{d \neq 0} \frac{\langle d, H d \rangle}{\|d\|^2}.$$

In infinite dimension it need not be an eigenvalue. The infimum is finite, since the Rayleigh
quotients are bounded below by $-\|H\|$. On the zero space the Lean value is $0$.

**Generalization.** The quotient uses a bounded linear operator. The ambient real inner-product
space need not be complete. -/
noncomputable def hilbertRayleighFloor (H : E →L[ℝ] E) : ℝ :=
  ⨅ d : {d : E // d ≠ 0}, H.rayleighQuotient d

private theorem bddBelow_nonzero_rayleigh (H : E →L[ℝ] E) :
    BddBelow (range fun d : {d : E // d ≠ 0} ↦ H.rayleighQuotient d) := by
  refine ⟨-‖H‖, ?_⟩
  rintro _ ⟨d, rfl⟩
  exact (neg_le_neg (H.rayleighQuotient_le_norm d)).trans (neg_abs_le _)

private theorem rayleighQuotient_real (H : E →L[ℝ] E) (d : E) :
    H.rayleighQuotient d = ⟪d, H d⟫ / ‖d‖ ^ 2 := by
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
  simp [real_inner_comm (H d) d]

/-- **Equation (8.3.3)** of [conn2000trust], lower bounds. Let $E \neq 0$, let $H$ be a continuous
linear operator on $E$, and let $a \in \mathbb{R}$. Then $a \le \lambda_{\min}[H]$ if and only
if
$$a \|d\|^2 \le \langle d, H d \rangle \qquad \text{for every } d \in E.$$
-/
theorem hilbertRayleighFloor_le_iff [Nontrivial E] (H : E →L[ℝ] E) (a : ℝ) :
    a ≤ hilbertRayleighFloor H ↔ ∀ d, a * ‖d‖ ^ 2 ≤ ⟪d, H d⟫ := by
  let : Nonempty {d : E // d ≠ 0} := by
    obtain ⟨d, hd⟩ := exists_ne (0 : E)
    exact ⟨⟨d, hd⟩⟩
  rw [hilbertRayleighFloor, le_ciInf_iff (bddBelow_nonzero_rayleigh H)]
  constructor
  · intro h d
    by_cases hd : d = 0
    · simp [hd]
    have hd₂ := sq_pos_of_pos (norm_pos_iff.mpr hd)
    have hq := h ⟨d, hd⟩
    rw [rayleighQuotient_real] at hq
    exact (le_div_iff₀ hd₂).mp hq
  · intro h d
    rw [rayleighQuotient_real]
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr d.property))).mpr (h d)

/-- **Equation (8.3.3)** of [conn2000trust], approximate eigenpoint direction. Let $E \neq 0$, let
$H$ be a continuous linear operator on $E$, and let $\lambda_{\min}[H] < a$. Then there is
$d \in E$ with $\|d\| = 1$ and $\langle d, H d \rangle < a$.

This gives a direction of negative curvature, when $a \le 0$, without an eigenvector that
attains the infimum.

**Reading.** The conclusion provides a unit direction strictly below the given threshold.
Attainment of the Rayleigh infimum is unnecessary. -/
theorem exists_unit_direction_below_of_hilbertRayleighFloor_lt [Nontrivial E]
    (H : E →L[ℝ] E) {a : ℝ} (ha : hilbertRayleighFloor H < a) :
    ∃ d, ‖d‖ = 1 ∧ ⟪d, H d⟫ < a := by
  have ha' : (⨅ d : Metric.sphere (0 : E) 1, H.rayleighQuotient d) < a := by
    rwa [← H.iInf_rayleigh_eq_iInf_rayleigh_sphere zero_lt_one]
  let : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  obtain ⟨d, hd⟩ := exists_lt_of_ciInf_lt ha'
  have hn : ‖(d : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using d.property
  rw [rayleighQuotient_real, hn, one_pow, div_one] at hd
  exact ⟨d, hn, hd⟩

end ConnGouldToint.Chapter08
