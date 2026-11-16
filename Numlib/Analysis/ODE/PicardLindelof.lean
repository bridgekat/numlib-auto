/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The Picard–Lindelöf theorem with the solution confined to the ball

Let $E$ be a real Banach space, $f : \mathbb{R} \times E \to E$, $t_0 \in [t_{\min}, t_{\max}]$ and
$x_0 \in E$. Mathlib's `IsPicardLindelof f t₀ x₀ a r L K` collects the hypotheses of the
Picard–Lindelöf theorem: on the closed ball $\bar B(x_0, a)$ the field $f(t, \cdot)$ is
$K$-Lipschitz and bounded by $L$, $f$ is continuous in time there, and the time interval is so short
that $L \max(t_{\max} - t_0, t_0 - t_{\min}) \le a - r$. Mathlib's existence theorem
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` gives an integral curve, but says
nothing about where the curve goes. Mathlib's uniqueness theorem `ODE_solution_unique_of_mem_Icc`
compares only solutions that stay in a set on which the field is Lipschitz. So the two theorems do
not combine into the textbook statement that the initial value problem has a unique solution on the
short interval.

This file proves that statement. For an initial value $x$ with $\|x - x_0\| \le r$, there is an
integral curve that stays in $\bar B(x_0, a)$, and it is the only integral curve with this property.

## Main results

* `IsPicardLindelof.exists_mem_closedBall_hasDerivWithinAt`: existence of an integral curve that
  stays in $\bar B(x_0, a)$.
* `IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt`: existence and uniqueness among
  the curves that stay in $\bar B(x_0, a)$.

## Proof outline

Every hypothesis of `IsPicardLindelof` constrains the field only on the ball. So the field can be
replaced by one that is constant outside the ball: $f(t, u)$ is replaced by $f(t, x_0)$ for $u$
outside the ball. The new field satisfies the same hypotheses, and it is bounded by $L$ at every
state. The mean value inequality then bounds the displacement of each of its integral curves by $L$
times the elapsed time, without circularity.

## Implementation notes

* The new field need not be continuous or Lipschitz. A radial retraction onto the ball is not
  needed; its Lipschitz constant in a general normed space is not in Mathlib.
-/

open Metric Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- **Picard–Lindelöf theorem, existence in the ball.** Let $E$ be a real Banach space, and assume
`IsPicardLindelof f t₀ x₀ a r L K`. Let $x \in E$ with $\|x - x_0\| \le r$. Then there is a
curve $\alpha : \mathbb{R} \to E$ with $\alpha(t_0) = x$, with $\alpha(t) \in \bar B(x_0, a)$
for all $t \in [t_{\min}, t_{\max}]$, and with
$$\alpha'(t) = f(t, \alpha(t)), \qquad t \in [t_{\min}, t_{\max}],$$
where the derivative is taken within $[t_{\min}, t_{\max}]$.

Mathlib's `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` gives all but the
containment in the ball. To add it, the proof replaces $f$ outside the ball by the constant
field $f(t, x_0)$. The hypotheses of `IsPicardLindelof` speak only about the ball, so they hold
for the new field, and the bound $\|f(t, u)\| \le L$ now holds at every state. The mean value
inequality then gives $\|\alpha(t) - \alpha(t_0)\| \le L |t - t_0| \le a - r$. On the ball the
two fields agree, so $\alpha$ solves the original equation. -/
theorem IsPicardLindelof.exists_mem_closedBall_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ (∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a) ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  classical
  obtain ⟨p, hpmem, hpeq⟩ : ∃ p : E → E, (∀ u, p u ∈ closedBall x₀ (a : ℝ)) ∧
      ∀ u ∈ closedBall x₀ (a : ℝ), p u = u := by
    refine ⟨fun u => if u ∈ closedBall x₀ (a : ℝ) then u else x₀, fun u => ?_, fun u hu => ?_⟩
    · dsimp only
      split_ifs with h
      · exact h
      · exact mem_closedBall_self a.2
    · dsimp only
      split_ifs
      rfl
  have hg : IsPicardLindelof (fun t u => f t (p u)) t₀ x₀ a r L K := by
    refine ⟨fun t ht u hu v hv => ?_, fun u hu => ?_, fun t ht u hu => ?_, hf.mul_max_le⟩
    · simp only [hpeq u hu, hpeq v hv]
      exact hf.lipschitzOnWith t ht hu hv
    · simp only [hpeq u hu]
      exact hf.continuousOn u hu
    · exact hf.norm_le t ht _ (hpmem u)
  obtain ⟨α, hα₀, hα⟩ := hg.exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  have hbound : ∀ t ∈ Icc tmin tmax, ‖f t (p (α t))‖ ≤ (L : ℝ) := fun t ht =>
    hf.norm_le t ht _ (hpmem _)
  have hmem : ∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ (a : ℝ) := by
    intro t ht
    have hle : ‖α t - α t₀‖ ≤ (L : ℝ) * ‖t - (t₀ : ℝ)‖ :=
      (convex_Icc tmin tmax).norm_image_sub_le_of_norm_hasDerivWithin_le hα hbound t₀.2 ht
    have habs : ‖t - (t₀ : ℝ)‖ ≤ max (tmax - t₀) ((t₀ : ℝ) - tmin) := by
      rw [Real.norm_eq_abs, abs_sub_le_iff]
      exact ⟨le_trans (by linarith [ht.2]) (le_max_left _ _),
        le_trans (by linarith [ht.1]) (le_max_right _ _)⟩
    have hxr : ‖α t₀ - x₀‖ ≤ (r : ℝ) := by
      rw [hα₀]
      exact mem_closedBall_iff_norm.mp hx
    rw [mem_closedBall, dist_eq_norm]
    calc ‖α t - x₀‖ ≤ ‖α t - α t₀‖ + ‖α t₀ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ (L : ℝ) * max (tmax - t₀) ((t₀ : ℝ) - tmin) + r :=
        add_le_add (hle.trans (mul_le_mul_of_nonneg_left habs L.coe_nonneg)) hxr
      _ ≤ ((a : ℝ) - r) + r := by linarith [hf.mul_max_le]
      _ = a := sub_add_cancel _ _
  refine ⟨α, hα₀, hmem, fun t ht => ?_⟩
  simpa only [hpeq _ (hmem t ht)] using hα t ht

/-- **Picard–Lindelöf theorem, existence and uniqueness.** Let $E$ be a real Banach space, and
assume `IsPicardLindelof f t₀ x₀ a r L K` with $t_{\min} < t_0 < t_{\max}$. Let $x \in E$ with
$\|x - x_0\| \le r$. Then there is a curve $\alpha : \mathbb{R} \to E$ with $\alpha(t_0) = x$,
with $\alpha(t) \in \bar B(x_0, a)$ and $\alpha'(t) = f(t, \alpha(t))$ for all
$t \in [t_{\min}, t_{\max}]$ (derivatives within $[t_{\min}, t_{\max}]$), and every curve
$\beta$ with these three properties agrees with $\alpha$ on $[t_{\min}, t_{\max}]$.

Uniqueness is `ODE_solution_unique_of_mem_Icc` with the ball as the set in which the solutions
stay. This is possible because `IsPicardLindelof.exists_mem_closedBall_hasDerivWithinAt` puts
the solution that it builds in the ball. The restriction to curves in the ball is not a
weakening: $f$ is Lipschitz only on the ball, and outside it the equation is not constrained. -/
theorem IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax) :
    ∃ α : ℝ → E, α t₀ = x ∧ (∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a) ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) ∧
      ∀ β : ℝ → E, β t₀ = x → (∀ t ∈ Icc tmin tmax, β t ∈ closedBall x₀ a) →
        (∀ t ∈ Icc tmin tmax, HasDerivWithinAt β (f t (β t)) (Icc tmin tmax) t) →
        EqOn α β (Icc tmin tmax) := by
  obtain ⟨α, hα₀, hαmem, hα⟩ := hf.exists_mem_closedBall_hasDerivWithinAt hx
  refine ⟨α, hα₀, hαmem, hα, fun β hβ₀ hβmem hβ => ?_⟩
  exact ODE_solution_unique_of_mem_Icc (K := K) (s := fun _ => closedBall x₀ a)
    (fun t ht => hf.lipschitzOnWith t (Ioo_subset_Icc_self ht)) ht₀
    (fun t ht => (hα t ht).continuousWithinAt)
    (fun t ht => (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => hαmem t (Ioo_subset_Icc_self ht))
    (fun t ht => (hβ t ht).continuousWithinAt)
    (fun t ht => (hβ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => hβmem t (Ioo_subset_Icc_self ht)) (hα₀.trans hβ₀.symm)
