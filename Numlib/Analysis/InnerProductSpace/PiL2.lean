/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.PiL2`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinate directions of Euclidean space

Let $\iota$ be a finite type, and let $e_i$ be the $i$-th coordinate direction of the Euclidean
space $\mathbb{R}^\iota$, that is, `EuclideanSpace.single i 1`. This module records the inner
products and norms of multiples of the $e_i$. It also proves that a vector orthogonal to all
coordinate directions but $e_i$ is the multiple $\langle e_i, v \rangle e_i$ of $e_i$, with norm
$|\langle e_i, v \rangle|$. In $\mathbb{R}^1$ every vector has this form. In $\mathbb{R}^2$ the
squared norm is the sum of the two squared coordinates.

## Main results

* `EuclideanSpace.eq_inner_single_smul_of_forall_ne`: if $\langle e_j, v \rangle = 0$ for all
  $j \neq i$, then $v = \langle e_i, v \rangle e_i$.
* `EuclideanSpace.norm_eq_abs_inner_single_of_forall_ne`: under the same hypothesis,
  $\|v\| = |\langle e_i, v \rangle|$.
* `EuclideanSpace.eq_inner_single_smul`, `EuclideanSpace.norm_eq_abs_inner_single`: the two
  statements for $\mathbb{R}^1$, without hypothesis.
* `EuclideanSpace.norm_sq_eq_fin_two`: $\|s\|^2 = s_0^2 + s_1^2$ in $\mathbb{R}^2$.
-/

open scoped RealInnerProductSpace

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Let $\iota$ be a finite type and let $i \neq j$ in $\iota$. Then the coordinate directions of
$\mathbb{R}^\iota$ satisfy $\langle e_i, c e_j \rangle = 0$ for every $c \in \mathbb{R}$. -/
theorem inner_single_smul_single_of_ne {i j : ι} (h : i ≠ j) (c : ℝ) :
    ⟪single i (1 : ℝ), c • single j (1 : ℝ)⟫ = 0 := by
  simp [inner_single_left, h]

/-- Let $\iota$ be a finite type and let $i \neq j$ in $\iota$. Then the coordinate directions of
$\mathbb{R}^\iota$ satisfy $\langle e_i, e_j \rangle = 0$. -/
theorem inner_single_single_of_ne {i j : ι} (h : i ≠ j) :
    ⟪single i (1 : ℝ), single j (1 : ℝ)⟫ = 0 := by
  simpa using inner_single_smul_single_of_ne h 1

/-- Let $\iota$ be a finite type and let $i \in \iota$. Then $\|c e_i\| = |c|$ in $\mathbb{R}^\iota$
for every $c \in \mathbb{R}$. -/
theorem norm_smul_single (i : ι) (c : ℝ) : ‖c • single i (1 : ℝ)‖ = |c| := by
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

/-- Let $\iota$ be a finite type and let $i \in \iota$. The coordinate direction $e_i$ of
$\mathbb{R}^\iota$ is a unit vector: $\|e_i\| = 1$. -/
theorem norm_single_one (i : ι) : ‖single i (1 : ℝ)‖ = 1 := by
  rw [PiLp.norm_single, norm_one]

/-- Let $\iota$ be a finite type and let $i \in \iota$. Then $\langle e_i, c e_i \rangle = c$ in
$\mathbb{R}^\iota$ for every $c \in \mathbb{R}$. -/
theorem inner_single_smul_self (i : ι) (c : ℝ) : ⟪single i (1 : ℝ), c • single i (1 : ℝ)⟫ = c := by
  simp [inner_single_left]

/-- Let $\iota$ be a finite type, let $i \in \iota$, and let $v \in \mathbb{R}^\iota$. If
$\langle e_j, v \rangle = 0$ for every $j \neq i$, then $v$ is a multiple of the $i$-th
coordinate direction:
$$v = \langle e_i, v \rangle \, e_i.$$

The coordinate direction $e_i$ is `EuclideanSpace.single i 1`. -/
theorem eq_inner_single_smul_of_forall_ne {i : ι} {v : EuclideanSpace ℝ ι}
    (hv : ∀ j, j ≠ i → ⟪single j (1 : ℝ), v⟫ = 0) :
    v = ⟪single i (1 : ℝ), v⟫ • single i (1 : ℝ) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp [inner_single_left]
  · have := hv j hj
    simp only [inner_single_left, map_one, one_mul] at this
    simp [hj, this]

/-- Let $\iota$ be a finite type, let $i \in \iota$, and let $v \in \mathbb{R}^\iota$. If
$\langle e_j, v \rangle = 0$ for every $j \neq i$, then the norm of $v$ is the absolute value of
its $i$-th coordinate:
$$\|v\| = |\langle e_i, v \rangle|.$$

The coordinate direction $e_i$ is `EuclideanSpace.single i 1`. -/
theorem norm_eq_abs_inner_single_of_forall_ne {i : ι} {v : EuclideanSpace ℝ ι}
    (hv : ∀ j, j ≠ i → ⟪single j (1 : ℝ), v⟫ = 0) : ‖v‖ = |⟪single i (1 : ℝ), v⟫| := by
  conv_lhs => rw [eq_inner_single_smul_of_forall_ne hv]
  exact norm_smul_single i _

/-- Every vector $v \in \mathbb{R}^1$ is a multiple of the coordinate direction $e_0$:
$$v = \langle e_0, v \rangle \, e_0.$$

The index set of $\mathbb{R}^1$ is `Fin 1`, and $e_0$ is `EuclideanSpace.single 0 1`. -/
theorem eq_inner_single_smul (v : EuclideanSpace ℝ (Fin 1)) :
    v = ⟪single 0 (1 : ℝ), v⟫ • single 0 (1 : ℝ) :=
  eq_inner_single_smul_of_forall_ne fun j hj => absurd (Subsingleton.elim j 0) hj

/-- Every vector $v \in \mathbb{R}^1$ has the norm
$$\|v\| = |\langle e_0, v \rangle|,$$
the absolute value of its coordinate.

The index set of $\mathbb{R}^1$ is `Fin 1`, and $e_0$ is `EuclideanSpace.single 0 1`. -/
theorem norm_eq_abs_inner_single (v : EuclideanSpace ℝ (Fin 1)) :
    ‖v‖ = |⟪single 0 (1 : ℝ), v⟫| :=
  norm_eq_abs_inner_single_of_forall_ne fun j hj => absurd (Subsingleton.elim j 0) hj

/-- Every vector $v \in \mathbb{R}^1$ satisfies $\langle e_0, v \rangle^2 = \|v\|^2$. -/
theorem inner_single_sq (v : EuclideanSpace ℝ (Fin 1)) :
    ⟪single 0 (1 : ℝ), v⟫ ^ 2 = ‖v‖ ^ 2 := by
  rw [norm_eq_abs_inner_single, sq_abs]

/-- Every vector $s \in \mathbb{R}^2$ has the squared norm
$$\|s\|^2 = s_0^2 + s_1^2.$$

The index set of $\mathbb{R}^2$ is `Fin 2`, so the coordinates are numbered from $0$. -/
theorem norm_sq_eq_fin_two (s : EuclideanSpace ℝ (Fin 2)) : ‖s‖ ^ 2 = (s 0) ^ 2 + (s 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

end EuclideanSpace
