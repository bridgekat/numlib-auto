/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.TietzeExtension`, though the statement needs the sup norm of
`Mathlib.Topology.ContinuousMap.Compact`, which that file does not import.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.TietzeExtension

/-!
# Interpolating finitely many values by a continuous function of norm at most one

Let $X$ be a compact Hausdorff space, let $x_1, \dots, x_n \in X$ be distinct points, and let
$\sigma_1, \dots, \sigma_n \in \mathbb{R}$ satisfy $|\sigma_i| \le 1$. This file proves that some
continuous function $f : X \to \mathbb{R}$ with sup norm $\|f\| \le 1$ takes the value $\sigma_i$ at
$x_i$ for each $i$. The proof applies the Tietze extension theorem to the finite, hence discrete,
set of nodes. The result shows that the norm of a quadrature functional is the sum of the absolute
values of its weights.

## Main results

* `ContinuousMap.exists_norm_le_one_apply_eq`: prescribed values of modulus at most $1$ at finitely
  many distinct points are taken by a continuous real function of sup norm at most $1$.
-/

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Let $X$ be a compact Hausdorff space, let $x_0, \dots, x_{n-1} \in X$ be distinct, and let
$\sigma_0, \dots, \sigma_{n-1} \in \mathbb{R}$ with $|\sigma_i| \le 1$ for all $i$. Then there
is a continuous function $f : X \to \mathbb{R}$ with $\|f\| \le 1$ and $f(x_i) = \sigma_i$ for
all $i$.

The norm $\|f\|$ is the sup norm. The values $\sigma_i$ define a continuous function on the
finite, hence discrete, set of nodes, and the Tietze extension theorem extends it to $X$ with
values in $[-1, 1]$. -/
theorem exists_norm_le_one_apply_eq {n : ℕ} {x : Fin n → X} (hx : Function.Injective x)
    (σ : Fin n → ℝ) (hσ : ∀ i, |σ i| ≤ 1) : ∃ f : C(X, ℝ), ‖f‖ ≤ 1 ∧ ∀ i, f (x i) = σ i := by
  classical
  have hclosed : IsClosed (Set.range x) := (Set.finite_range x).isClosed
  let g : C((Set.range x : Set X), ℝ) :=
    ⟨fun u => σ (Classical.choose u.2), continuous_of_discreteTopology⟩
  have hg : ∀ (u : (Set.range x : Set X)) (i : Fin n), (u : X) = x i → g u = σ i := by
    intro u i hu
    exact congrArg σ (hx ((Classical.choose_spec u.2).trans hu))
  have hmem : ∀ u : (Set.range x : Set X), g u ∈ Set.Icc (-1 : ℝ) 1 := fun u =>
    Set.mem_Icc.mpr (abs_le.mp (hσ (Classical.choose u.2)))
  obtain ⟨f, hfmem, hfeq⟩ :=
    ContinuousMap.exists_restrict_eq_forall_mem_of_closed g hmem ⟨0, by norm_num⟩ hclosed
  refine ⟨f, ?_, fun i => ?_⟩
  · rw [ContinuousMap.norm_le _ zero_le_one]
    exact fun u => Real.norm_eq_abs _ ▸ abs_le.2 ⟨(hfmem u).1, (hfmem u).2⟩
  · have hcongr := congrArg
      (fun h : C((Set.range x : Set X), ℝ) => h ⟨x i, Set.mem_range_self i⟩) hfeq
    simp only [ContinuousMap.restrict_apply] at hcongr
    rw [hcongr, hg _ i rfl]

end ContinuousMap
