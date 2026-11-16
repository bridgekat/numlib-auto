/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Hessenberg

/-!
# Perturbed Arnoldi and Lanczos relations

An Arnoldi or Lanczos process in finite precision does not produce the exact relation
$A v_j = \sum_{i \le j+1} h_{ij} v_i$ with orthonormal vectors $v_i$. It produces this relation up
to a residual $F_j$ of small norm, and its vectors are orthonormal only up to a defect
([meurant2006lanczos], Theorem 14, after Paige). This module takes these two properties as a
hypothesis, `Arnoldi.IsPerturbedRelation`. The identities of exact arithmetic then hold with the
perturbation carried along, and they apply to computed quantities as soon as a rounding model
supplies the two bounds.

The hypothesis depends on the number $m$ of steps: $A v_j$ is expanded for $j < m$, and the
orthogonality defect is bounded for the $m + 1$ vectors $v_0, \dots, v_m$ that these expansions use.
The exact process is the case $F = 0$ with both bounds $0$. It needs
$m < \operatorname{grade}(A, b)$, because the Arnoldi vectors from the grade onwards are zero and
not unit vectors. The results carry along the coordinate form (6.27) of the residual in
[saad2003iterative]: they bound the gap between the true residual and the residual
$V_{m+1}(\beta e_1 - \bar H_m y)$ of the small problem, which an implementation monitors, and the
gap in the Pythagoras identity that turns coordinates into norms.

## Main definitions

* `Arnoldi.IsPerturbedRelation`: $A v_j = \sum_{i \le j+1} h_{ij} v_i + F_j$ with
  $\|F_j\| \le \varepsilon$ for $j < m$, $h$ upper Hessenberg, and $|\langle v_i, v_j \rangle -
  \delta_{ij}| \le \varepsilon'$ for $i, j \le m$.

## Main results

* `Arnoldi.IsPerturbedRelation.residual_eq`: the residual of $x_0 + V_m y$ is $V_{m+1}(\beta e_1 -
  \bar H_m y) - \sum_j y_j F_j$.
* `Arnoldi.IsPerturbedRelation.norm_residual_sub_le`: the true residual and the small-problem
  residual differ in norm by at most $\varepsilon \sum_j |y_j|$.
* `Arnoldi.IsPerturbedRelation.abs_norm_sq_sub_sum_le`: $\big| \|\sum_i c_i v_i\|^2 - \sum_i |c_i|^2
  \big| \le \varepsilon' (\sum_i |c_i|)^2$.
* `Arnoldi.hessenbergRelation_isPerturbedRelation`: below the grade, the exact Arnoldi process
  satisfies the perturbed relation with $F = 0$ and $\varepsilon = \varepsilon' = 0$.

## Notation

* $\bar H_m$ is the $(m+1) \times m$ upper Hessenberg matrix $(h_{ij})$, `Krylov.hessenbergOf h m`,
  and $\beta e_1 \in \mathbb{K}^{m+1}$ is `Krylov.firstVec β (m + 1)`. Here $\mathbb{K}$ is
  $\mathbb{R}$ or $\mathbb{C}$.
-/

open Krylov Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Arnoldi

/-- Let $A$ be a linear operator on an inner product space $E$ over $\mathbb{K}$, let
$(v_j)_{j \ge 0}$ and $(F_j)_{j \ge 0}$ be sequences in $E$, let $(h_{ij})_{i, j \ge 0}$ be
scalars, let $m \in \mathbb{N}$ and let $\varepsilon, \varepsilon' \in \mathbb{R}$. These data
form a **perturbed Hessenberg relation over $m$ steps** if
$$A v_j = \sum_{i=0}^{j+1} h_{ij} v_i + F_j \quad \text{and} \quad \|F_j\| \le \varepsilon
  \qquad (j < m),$$
$h_{ij} = 0$ whenever $i > j + 1$, and
$$|\langle v_i, v_j \rangle - \delta_{ij}| \le \varepsilon' \qquad (i, j \le m).$$

An Arnoldi or Lanczos process in finite precision satisfies this hypothesis, with $\varepsilon$
and $\varepsilon'$ of order $u \|A\|$ for the unit roundoff $u$ ([meurant2006lanczos], Theorem
14). The exact process is the case $F = 0$ and $\varepsilon = \varepsilon' = 0$; see
`Arnoldi.hessenbergRelation_isPerturbedRelation`. -/
structure IsPerturbedRelation (A : E →ₗ[𝕜] E) (v : ℕ → E) (h : ℕ → ℕ → 𝕜) (F : ℕ → E) (m : ℕ)
    (ε ε' : ℝ) : Prop where
  /-- The expansion $A v_j = \sum_{i \le j+1} h_{ij} v_i + F_j$ for $j < m$. -/
  apply_eq : ∀ j < m, A (v j) = ∑ i ∈ range (j + 2), h i j • v i + F j
  /-- The coefficients are upper Hessenberg: $h_{ij} = 0$ for $i > j + 1$. -/
  eq_zero_of_lt : ∀ i j, j + 1 < i → h i j = 0
  /-- The residuals are small: $\|F_j\| \le \varepsilon$ for $j < m$. -/
  norm_F_le : ∀ j < m, ‖F j‖ ≤ ε
  /-- The vectors are orthonormal up to the defect $\varepsilon'$: $|\langle v_i, v_j \rangle -
  \delta_{ij}| \le \varepsilon'$ for $i, j \le m$. -/
  inner_sub_le : ∀ i ≤ m, ∀ j ≤ m,
    ‖(inner 𝕜 (v i) (v j) : 𝕜) - (if i = j then 1 else 0)‖ ≤ ε'

namespace IsPerturbedRelation

variable {A : E →ₗ[𝕜] E} {v : ℕ → E} {h : ℕ → ℕ → 𝕜} {F : ℕ → E} {m : ℕ} {ε ε' : ℝ}
  (hv : IsPerturbedRelation A v h F m ε ε')
include hv

/-- The expansion of $A v_j$ for $j < m$ can be taken over any range $i < N$ with $N \ge j + 2$. -/
private theorem apply_eq_range {j : ℕ} (hj : j < m) (N : ℕ) (hN : j + 2 ≤ N) :
    A (v j) = ∑ i ∈ range N, h i j • v i + F j := by
  rw [hv.apply_eq j hj]
  congr 1
  refine Finset.sum_subset (by simpa using hN) fun i _ hi' => ?_
  rw [Finset.mem_range] at hi'
  rw [hv.eq_zero_of_lt i j (by omega), zero_smul]

/-- Under a perturbed Hessenberg relation over $m$ steps, for every $y \in \mathbb{K}^m$,
$$A \sum_{j<m} y_j v_j = \sum_{i=0}^{m} (\bar H_m y)_i \, v_i + \sum_{j<m} y_j F_j,$$
that is, $A V_m y = V_{m+1} \bar H_m y + \sum_j y_j F_j$. This is the perturbed form of
`Krylov.HessenbergRelation₂.apply_sum`. -/
theorem apply_sum (y : Fin m → 𝕜) :
    A (∑ j, y j • v j)
      = (∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i) + ∑ j, y j • F j := by
  rw [map_sum]
  have hleft : ∀ j : Fin m,
      A (y j • v j) = (∑ i : Fin (m + 1), (y j * h i j) • v i) + y j • F j := by
    intro j
    rw [map_smul, hv.apply_eq_range j.isLt (m + 1) (by omega), smul_add, Finset.smul_sum,
      Fin.sum_univ_eq_sum_range (fun i => (y j * h i (j : ℕ)) • v i) (m + 1)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun j _ => hleft j, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [hessenbergOf, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Assume a perturbed Hessenberg relation over $m$ steps, and let $b, x_0 \in E$ and
$\beta \in \mathbb{K}$ satisfy $b - A x_0 = \beta v_0$. Then for every $y \in \mathbb{K}^m$
$$b - A \Big( x_0 + \sum_{j<m} y_j v_j \Big) = \sum_{i=0}^{m} (\beta e_1 - \bar H_m y)_i \,
  v_i - \sum_{j<m} y_j F_j.$$
This is the perturbed form of (6.27) in [saad2003iterative] and of
`Krylov.HessenbergRelation₂.residual_eq`.

Here $\bar H_m$ and $\beta e_1$ are `Krylov.hessenbergOf h m` and `Krylov.firstVec β (m + 1)`. -/
theorem residual_eq {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • v j)
      = (∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i)
        - ∑ j, y j • F j := by
  have hfirst : ∑ i : Fin (m + 1), firstVec β (m + 1) i • v i = β • v 0 := by
    rw [Finset.sum_eq_single (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))]
    · rfl
    · intro i _ hi
      have hne : (i : ℕ) ≠ 0 := fun hc => hi (Fin.ext hc)
      simp [firstVec, hne]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hsplit : ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i
      = β • v 0 - ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i := by
    rw [← hfirst, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, sub_smul]
  rw [hsplit, map_add, hv.apply_sum y, ← hr]
  abel

/-- Assume a perturbed Hessenberg relation over $m$ steps, and let $b, x_0 \in E$ and
$\beta \in \mathbb{K}$ satisfy $b - A x_0 = \beta v_0$. Then for every $y \in \mathbb{K}^m$
$$\Big\| b - A \Big( x_0 + \sum_{j<m} y_j v_j \Big) - \sum_{i=0}^{m} (\beta e_1 - \bar H_m y)_i
  \, v_i \Big\| \le \varepsilon \sum_{j<m} |y_j|.$$
So the residual $V_{m+1}(\beta e_1 - \bar H_m y)$ of the small problem, which an implementation
in finite precision monitors, is the true residual up to $\varepsilon \|y\|_1$.

The proof uses only the expansion and the bound on the residuals, not the orthogonality defect. -/
theorem norm_residual_sub_le {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) (y : Fin m → 𝕜) :
    ‖(b - A (x₀ + ∑ j, y j • v j))
        - ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i‖
      ≤ ε * ∑ j, ‖y j‖ := by
  rw [hv.residual_eq hr y, sub_sub_cancel_left, norm_neg]
  calc ‖∑ j, y j • F j‖ ≤ ∑ j, ‖y j • F j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin m, ‖y j‖ * ε := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hv.norm_F_le j j.isLt) (norm_nonneg _)
    _ = ε * ∑ j, ‖y j‖ := by rw [← Finset.sum_mul, mul_comm]

/-- Assume a perturbed Hessenberg relation over $m$ steps. Then for every $c \in \mathbb{K}^{m+1}$
$$\Big| \Big\| \sum_{i=0}^{m} c_i v_i \Big\|^2 - \sum_{i=0}^{m} |c_i|^2 \Big| \le \varepsilon'
  \Big( \sum_{i=0}^{m} |c_i| \Big)^2.$$
So the norm of a combination of the $v_i$ is the Euclidean norm of its coordinates up to a term
of order $\varepsilon'$. At $\varepsilon' = 0$ this is the Pythagoras identity, and the
coordinates give the norm exactly.

The proof uses only the bound on the orthogonality defect. -/
theorem abs_norm_sq_sub_sum_le (c : Fin (m + 1) → 𝕜) :
    |‖∑ i, c i • v i‖ ^ 2 - ∑ i, ‖c i‖ ^ 2| ≤ ε' * (∑ i, ‖c i‖) ^ 2 := by
  classical
  -- the orthogonality defect of the pair `(i, j)`
  set e : Fin (m + 1) → Fin (m + 1) → 𝕜 := fun i j =>
    (inner 𝕜 (v i) (v j) : 𝕜) - (if (i : ℕ) = (j : ℕ) then 1 else 0) with he
  have hebound : ∀ i j, ‖e i j‖ ≤ ε' := fun i j =>
    hv.inner_sub_le i (Nat.lt_succ_iff.1 i.isLt) j (Nat.lt_succ_iff.1 j.isLt)
  have hinner : ∀ i j : Fin (m + 1),
      (inner 𝕜 (v i) (v j) : 𝕜) = (if (i : ℕ) = (j : ℕ) then 1 else 0) + e i j := by
    intro i j; rw [he]; ring
  -- expand the inner product of the sum with itself
  have hexpand : (inner 𝕜 (∑ i, c i • v i) (∑ i, c i • v i) : 𝕜)
      = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          starRingEnd 𝕜 (c i) * c j * (inner 𝕜 (v i) (v j) : 𝕜) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum,
      ← mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hdiag : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        starRingEnd 𝕜 (c i) * c j * (if (i : ℕ) = (j : ℕ) then (1 : 𝕜) else 0)
      = ∑ i : Fin (m + 1), ((‖c i‖ : 𝕜) ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [RCLike.conj_mul]
    · intro j _ hj
      have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => hj (Fin.ext hc.symm)
      simp [hne]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  -- the remainder
  set R : 𝕜 := ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    starRingEnd 𝕜 (c i) * c j * e i j with hR
  have hsum : (inner 𝕜 (∑ i, c i • v i) (∑ i, c i • v i) : 𝕜)
      = (∑ i : Fin (m + 1), ((‖c i‖ : 𝕜) ^ 2)) + R := by
    rw [hexpand, hR, ← hdiag, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hinner i j]; ring
  have hre : ‖∑ i, c i • v i‖ ^ 2 - ∑ i, ‖c i‖ ^ 2 = RCLike.re R := by
    have h1 : RCLike.re (inner 𝕜 (∑ i, c i • v i) (∑ i, c i • v i) : 𝕜)
        = ‖∑ i : Fin (m + 1), c i • v i‖ ^ 2 := inner_self_eq_norm_sq _
    rw [hsum] at h1
    rw [map_add, map_sum] at h1
    have h2 : ∀ i : Fin (m + 1), RCLike.re ((‖c i‖ : 𝕜) ^ 2) = ‖c i‖ ^ 2 := by
      intro i; norm_cast
    simp only [h2] at h1
    linarith
  -- bound the remainder
  have hRbound : ‖R‖ ≤ ε' * (∑ i, ‖c i‖) ^ 2 := by
    calc ‖R‖ ≤ ∑ i : Fin (m + 1), ‖∑ j : Fin (m + 1), starRingEnd 𝕜 (c i) * c j * e i j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), ‖c i‖ * (‖c j‖ * ε') := by
          refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_mul, RCLike.norm_conj, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hebound i j) (norm_nonneg _)) (norm_nonneg _)
      _ = ε' * (∑ i, ‖c i‖) ^ 2 := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
          rw [sq]
          ring
  rw [hre]
  exact (RCLike.abs_re_le_norm R).trans hRbound

end IsPerturbedRelation

/-- Let $A$ be a linear operator on $E$ and $b \in E$, such that the Krylov space $\mathcal{K}(A,
b) = \operatorname{span}\{A^k b : k \ge 0\}$ is finite-dimensional. If
$m < \operatorname{grade}(A, b)$, then the Arnoldi vectors $v_j$ and the Arnoldi coefficients
$h_{ij}$ of $A$ and $b$ form a perturbed Hessenberg relation over $m$ steps with $F = 0$ and
$\varepsilon = \varepsilon' = 0$. In words, below the grade the Arnoldi vectors are orthonormal
and satisfy the Hessenberg relation exactly.

The hypothesis $m < \operatorname{grade}(A, b)$ is needed for the orthogonality clause: from the
grade onwards the Arnoldi vectors are $0$ and not unit vectors (`Arnoldi.vec_eq_zero_iff`). The
vectors are `Arnoldi.vec A b`, the coefficients are `Arnoldi.coeff A b`, and the Krylov space is
`Krylov.fullSubspace A b`. -/
theorem hessenbergRelation_isPerturbedRelation (A : E →ₗ[𝕜] E) (b : E)
    [FiniteDimensional 𝕜 (Krylov.fullSubspace A b)] {m : ℕ} (hm : m < grade A b) :
    IsPerturbedRelation A (vec A b) (coeff A b) 0 m 0 0 where
  apply_eq j _ := by simpa using (hessenbergRelation A b).apply_eq j
  eq_zero_of_lt := (hessenbergRelation A b).eq_zero_of_lt
  norm_F_le j _ := by simp
  inner_sub_le i hi j hj := by
    rcases eq_or_ne i j with rfl | hij
    · have hnorm : ‖vec A b i‖ = 1 :=
        norm_vec_eq_one_of_lt_grade A b (lt_of_le_of_lt hi hm)
      simp [hnorm]
    · rw [inner_vec_eq_zero A b hij]
      simp [hij]

end Arnoldi
