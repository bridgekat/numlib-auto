/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Preconditioned
import NumlibSurface.SaadSparse.Chapter09.Section03

/-!
# Saad, Section 9.4: Flexible variants

This module formalizes Section 9.4 of [saad2003iterative]. In flexible GMRES (FGMRES, Algorithm 9.6)
the preconditioner may change at every step. The iterate is therefore expanded in arbitrary
directions $z_j = M_j^{-1} v_j$, while the residual is still expanded in the orthonormal Arnoldi
basis $v_0, v_1, \ldots$. The search space $x_0 + \operatorname{span}\{z_0, \ldots, z_{m-1}\}$ is
not a Krylov subspace. The process satisfies the relation $A Z_m = V_{m+1} \bar H_m$ of (9.22), a
Hessenberg relation with two families of vectors, and the whole section follows from it.

Proposition 9.2 states that the FGMRES iterate minimizes $\|b - Ax\|_2$ over $x_0 +
\operatorname{span}\{z_0, \ldots, z_{m-1}\}$, and Proposition 9.3 relates exactness of the iterate
to the vanishing of the subdiagonal entry $h_{m+1,m}$. An inner solve that is exact at one step,
$A z_j = v_j$, ends the outer iteration. A constant preconditioner gives back GMRES with right
preconditioning (Algorithm 9.5). Flexible DQGMRES (9.28) is Algorithm 6.13 applied to the
preconditioned vectors $M_j^{-1} v_j$. The proofs specialize `Numlib.Krylov.QuasiMinRes` and
`Numlib.Krylov.Preconditioned`.

## Main definitions

* Algorithm 9.6, `SaadSparse.Chapter09.fgmresV`: the Arnoldi basis of the flexible process.
* Algorithm 9.6, `SaadSparse.Chapter09.fgmresZ`: the preconditioned directions $z_j = M_j^{-1} v_j$.
* Algorithm 9.6, `SaadSparse.Chapter09.fgmresCoeff`: the Hessenberg coefficients $h_{ij}$.
* Algorithm 9.6, `SaadSparse.Chapter09.fgmres`: the FGMRES iterate $x_m = x_0 + Z_m y_m$.
* Equation (9.28), `SaadSparse.Chapter09.fdqgmres`: flexible DQGMRES.

## Main results

* Equation (9.22), `SaadSparse.Chapter09.equation_9_22`: the two-family Hessenberg relation
  $A Z_m = V_{m+1} \bar H_m$.
* Section 9.4.1, `SaadSparse.Chapter09.orthonormal_fgmresV`: the flexible Arnoldi basis is
  orthonormal as long as the process does not break down.
* Proposition 9.2, `SaadSparse.Chapter09.proposition_9_2`: the FGMRES iterate minimizes
  $\|b - Ax\|_2$ over $x_0 + \operatorname{span}\{z_0, \ldots, z_{m-1}\}$.
* Proposition 9.3, `SaadSparse.Chapter09.proposition_9_3`: exactness of the FGMRES iterate and the
  subdiagonal entry $h_{m+1,m}$.
* Remark after Proposition 9.3, `SaadSparse.Chapter09.hessenbergSq_isUnit_of_linearIndependent`: the
  nonsingularity hypothesis of Proposition 9.3 holds when $A$ is nonsingular and
  $z_0, \ldots, z_{m-1}$ are linearly independent.
* Section 9.4.1, `SaadSparse.Chapter09.fgmres_eq_of_apply_fgmresZ_eq`: an exact preconditioning step
  $A z_j = v_j$ makes $x_{j+1}$ exact.
* Section 9.4.1, `SaadSparse.Chapter09.fgmres_eq_gmresRight`: with a constant preconditioner, FGMRES
  is Algorithm 9.5.
* Equation (9.28), `SaadSparse.Chapter09.fdqgmres_eq_dqgmres`: with the identity preconditioner,
  flexible DQGMRES is Algorithm 6.13.

## Implementation notes

* The preconditioners are a sequence `M : ℕ → Matrix (Fin n) (Fin n) 𝕜`, and $M_j^{-1}$ is Mathlib's
  matrix inverse.
* Indices are $0$-based: the basis starts at $v_0$, the first vector of the book, and the entry
  $h_{m+1,m}$ of the book is `fgmresCoeff M A v₁ m (m - 1)`. Division by $0$ gives $0$, so the stop
  "if $h_{j+1,j} = 0$" of the book makes every later vector $0$.
* The vector $y_m$ is computed by the Givens rotations of Algorithm 6.9, as $y_m = R_m^{-1} g_m$
  with `SaadSparse.Chapter06.R` and `SaadSparse.Chapter06.g`.
* The hypothesis of `SaadSparse.Chapter09.proposition_9_3` that no step before $m$ breaks down
  includes $w_{m-1} \neq 0$. This gives $h_{m+1,m} = \|w_{m-1}\|_2 \neq 0$, so in this form the
  result states that the iterate $x_m$ is not exact. The direction from $h_{m+1,m} = 0$ to exactness
  is stated, for an exact inner solve, by `SaadSparse.Chapter09.fgmres_eq_of_apply_fgmresZ_eq`.
-/

open Matrix Finset

open scoped SaadSparse

namespace SaadSparse.Chapter09

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Algorithm 9.6 -/

/-- **Algorithm 9.6** of [saad2003iterative] (FGMRES), lines 3–9: the Arnoldi basis of the flexible
process. Let $M_0, M_1, \ldots \in \mathbb{K}^{n \times n}$ be the preconditioners,
$A \in \mathbb{K}^{n \times n}$ and $v_0 \in \mathbb{K}^n$. The vectors are defined by
recursion:
$$v_{j+1} = \frac{w_j}{\|w_j\|_2}, \qquad w_j = A M_j^{-1} v_j - \sum_{i=0}^{j} h_{ij} v_i,
  \qquad h_{ij} = (A M_j^{-1} v_j, v_i).$$

Indices are $0$-based, so $v_0$ is the first vector $v_1$ of the book. The stop "if
$h_{j+1,j} = 0$" of the book is the Lean convention $x/0 = 0$: after a breakdown every later
vector is $0$. -/
noncomputable def fgmresV (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) : ℕ → EuclideanSpace 𝕜 (Fin n)
  | 0 => v₁
  | j + 1 =>
    let v : Fin (j + 1) → EuclideanSpace 𝕜 (Fin n) := fun i => fgmresV M A v₁ (i : ℕ)
    let Az := op A (op (M j)⁻¹ (v (Fin.last j)))
    let w := Az - ∑ i : Fin (j + 1), inner 𝕜 (v i) Az • v i
    ((‖w‖ : 𝕜)⁻¹) • w
  termination_by j => j
  decreasing_by exact i.isLt

/-- **Algorithm 9.6** of [saad2003iterative], line 3: the preconditioned direction
$z_j = M_j^{-1} v_j$. FGMRES expands its iterate in these directions. -/
noncomputable def fgmresZ (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  op (M j)⁻¹ (fgmresV M A v₁ j)

/-- Lines 4–7 of Algorithm 9.6 of [saad2003iterative]: the vector
$w_j = A z_j - \sum_{i=0}^{j} (A z_j, v_i) v_i$ before normalization. -/
noncomputable def fgmresW (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  op A (fgmresZ M A v₁ j) -
    ∑ i ∈ Finset.range (j + 1),
      inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j)) • fgmresV M A v₁ i

/-- **Algorithm 9.6** of [saad2003iterative], lines 6 and 9: the Hessenberg coefficients. For
$i \le j$ the coefficient is $h_{ij} = (A z_j, v_i)$, the subdiagonal coefficient is
$h_{j+1,j} = \|w_j\|_2$, and $h_{ij} = 0$ for $i > j + 1$. -/
noncomputable def fgmresCoeff (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) (i j : ℕ) : 𝕜 :=
  if i = j + 1 then (‖fgmresW M A v₁ j‖ : 𝕜)
  else if i ≤ j then inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j))
  else 0

variable {M : ℕ → Matrix (Fin n) (Fin n) 𝕜} {A : Matrix (Fin n) (Fin n) 𝕜}
variable {v₁ : EuclideanSpace 𝕜 (Fin n)}

/-- Line 1 of Algorithm 9.6: the Arnoldi basis starts at the given vector $v_0$. -/
@[simp]
theorem fgmresV_zero : fgmresV M A v₁ 0 = v₁ := by rw [fgmresV]

/-- Line 9 of Algorithm 9.6: $v_{j+1} = w_j/\|w_j\|_2$, which is $0$ at a breakdown $w_j = 0$. -/
theorem fgmresV_succ (j : ℕ) :
    fgmresV M A v₁ (j + 1) = ((‖fgmresW M A v₁ j‖ : 𝕜)⁻¹) • fgmresW M A v₁ j := by
  rw [fgmresV, fgmresW, fgmresZ]
  simp only [Fin.val_last]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => inner 𝕜 (fgmresV M A v₁ i) (op A (op (M j)⁻¹ (fgmresV M A v₁ j))) •
      fgmresV M A v₁ i) (j + 1)]

/-- For $i \le j$ the Hessenberg coefficient of Algorithm 9.6 is $h_{ij} = (A z_j, v_i)$. -/
theorem fgmresCoeff_of_le {i j : ℕ} (hij : i ≤ j) :
    fgmresCoeff M A v₁ i j = inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j)) := by
  rw [fgmresCoeff, ite_eq_right (by omega), ite_eq_left hij]

/-- The subdiagonal Hessenberg coefficient of Algorithm 9.6 is $h_{j+1,j} = \|w_j\|_2$. -/
theorem fgmresCoeff_succ_self (j : ℕ) :
    fgmresCoeff M A v₁ (j + 1) j = (‖fgmresW M A v₁ j‖ : 𝕜) := by
  rw [fgmresCoeff, ite_eq_left rfl]

/-- The coefficients of Algorithm 9.6 form an upper Hessenberg array: $h_{ij} = 0$ for $i > j + 1$.
-/
theorem fgmresCoeff_eq_zero_of_lt {i j : ℕ} (hij : j + 1 < i) : fgmresCoeff M A v₁ i j = 0 := by
  rw [fgmresCoeff, ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ### Equation (9.22): the two-family Hessenberg relation -/

/-- For every vector $w$, $\|w\| \, (\|w\|^{-1} w) = w$; at $w = 0$ both sides are $0$. -/
private theorem smul_inv_smul_norm (w : EuclideanSpace 𝕜 (Fin n)) :
    ((‖w‖ : 𝕜)) • (((‖w‖ : 𝕜))⁻¹ • w) = w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [smul_smul, mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 hw), one_smul]

/-- **Equations (9.22)–(9.23)** of [saad2003iterative]. Let $M_0, M_1, \ldots$ be the
preconditioners, $A \in \mathbb{K}^{n \times n}$ and $v_0 \in \mathbb{K}^n$. Then the vectors
and coefficients of Algorithm 9.6 satisfy, for every $j$,
$$A z_j = \sum_{i=0}^{j+1} h_{ij} v_i,$$
and $h_{ij} = 0$ for $i > j + 1$. That is, $A Z_m = V_{m+1} \bar H_m$ for every $m$, with
$\bar H_m$ upper Hessenberg.

This two-family Hessenberg relation replaces the relation $(A M^{-1}) V_m = V_{m+1} \bar H_m$ of
a fixed preconditioner. It holds without hypotheses, also after a breakdown $h_{j+1,j} = 0$. The
conclusion is `Krylov.HessenbergRelation₂`. -/
theorem equation_9_22 (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) :
    Krylov.HessenbergRelation₂ (op A) (fgmresZ M A v₁) (fgmresV M A v₁) (fgmresCoeff M A v₁) := by
  refine ⟨fun j => ?_, fun i j hij => fgmresCoeff_eq_zero_of_lt hij⟩
  rw [Finset.sum_range_succ, fgmresCoeff_succ_self, fgmresV_succ, smul_inv_smul_norm, fgmresW]
  rw [Finset.sum_congr rfl fun i (hi : i ∈ Finset.range (j + 1)) => by
    rw [fgmresCoeff_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]]
  abel

/-! ### Orthonormality of the flexible Arnoldi basis -/

/-- If $w_j \neq 0$, then the next basis vector $v_{j+1}$ of Algorithm 9.6 is a unit vector. -/
private theorem norm_fgmresV_succ {j : ℕ} (hw : fgmresW M A v₁ j ≠ 0) :
    ‖fgmresV M A v₁ (j + 1)‖ = 1 := by
  rw [fgmresV_succ, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]

/-- If $\|v_0\| = 1$ and $w_j \neq 0$ for all $j < m$, then $(v_a, v_b) = \delta_{ab}$ for all
$a, b \le m$; this is the induction behind `SaadSparse.Chapter09.orthonormal_fgmresV`. -/
private theorem inner_fgmresV (hv : ‖v₁‖ = 1) :
    ∀ m : ℕ, (∀ j, j < m → fgmresW M A v₁ j ≠ 0) →
      ∀ a ≤ m, ∀ b ≤ m,
        inner 𝕜 (fgmresV M A v₁ a) (fgmresV M A v₁ b) = if a = b then 1 else 0 := by
  intro m
  induction m with
  | zero =>
    intro _ a ha b hb
    obtain rfl : a = 0 := Nat.le_zero.1 ha
    obtain rfl : b = 0 := Nat.le_zero.1 hb
    rw [ite_eq_left rfl, fgmresV_zero, inner_self_eq_norm_sq_to_K, hv]
    norm_num
  | succ m ih =>
    intro hbreak
    have hIH := ih fun j hj => hbreak j (by omega)
    -- the new vector is orthogonal to all the previous ones
    have hperp : ∀ c ≤ m, inner 𝕜 (fgmresV M A v₁ c) (fgmresW M A v₁ m) = 0 := by
      intro c hc
      rw [fgmresW, inner_sub_right, inner_sum]
      have hterm : ∀ i ∈ Finset.range (m + 1),
          inner 𝕜 (fgmresV M A v₁ c)
              (inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ m)) • fgmresV M A v₁ i)
            = if i = c then inner 𝕜 (fgmresV M A v₁ c) (op A (fgmresZ M A v₁ m)) else 0 := by
        intro i hi
        rw [inner_smul_right, hIH c hc i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
        by_cases hic : c = i
        · rw [ite_eq_left hic, ite_eq_left hic.symm, mul_one, hic]
        · rw [ite_eq_right hic, ite_eq_right (fun h => hic h.symm), mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (m + 1)) c
        (fun _ => inner 𝕜 (fgmresV M A v₁ c) (op A (fgmresZ M A v₁ m))),
        ite_eq_left (Finset.mem_range.2 (by omega)), sub_self]
    have hnew : ∀ c ≤ m, inner 𝕜 (fgmresV M A v₁ c) (fgmresV M A v₁ (m + 1)) = 0 := by
      intro c hc
      rw [fgmresV_succ, inner_smul_right, hperp c hc, mul_zero]
    intro a ha b hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ha) with ha' | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hb) with hb' | rfl
      · exact hIH a (by omega) b (by omega)
      · rw [hnew a (by omega), ite_eq_right (by omega)]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hb) with hb' | rfl
      · rw [← inner_conj_symm, hnew b (by omega), map_zero, ite_eq_right (by omega)]
      · rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K,
          norm_fgmresV_succ (hbreak m (by omega))]
        norm_num

/-- **Section 9.4.1** of [saad2003iterative], orthonormality of the flexible Arnoldi basis. Let
$\|v_0\|_2 = 1$, and let $w_j \neq 0$ for all $j < m$, that is, the process does not break down
before step $m$. Then the vectors $v_0, \ldots, v_m$ of Algorithm 9.6 are orthonormal.

Orthonormality makes the quasi-residual of Section 9.4 equal to the true residual norm, so
Proposition 9.2 is an optimality statement for $\|b - Ax\|_2$. -/
theorem orthonormal_fgmresV (hv : ‖v₁‖ = 1) {m : ℕ}
    (hbreak : ∀ j, j < m → fgmresW M A v₁ j ≠ 0) :
    Orthonormal 𝕜 fun i : Fin (m + 1) => fgmresV M A v₁ (i : ℕ) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · dsimp only
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · rw [h0, fgmresV_zero]; exact hv
    · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
      rw [hk]
      exact norm_fgmresV_succ (hbreak k (by omega : k < m))
  · dsimp only
    have h := inner_fgmresV hv m hbreak (i : ℕ) (by omega) (j : ℕ) (by omega)
    rwa [ite_eq_right fun hc => hij (Fin.ext hc)] at h

/-! ### Algorithm 9.6: the iterate -/

/-- Line 12 of Algorithm 9.6 of [saad2003iterative]: the minimizer $y_m$ of
$\|\beta e_1 - \bar H_m y\|_2$, computed by the Givens rotations of Algorithm 6.9 as
$y_m = R_m^{-1} g_m$. The Arnoldi process starts at $v_0 = r_0/\beta$ with $r_0 = b - A x_0$ and
$\beta = \|r_0\|_2$. -/
noncomputable def fgmresY (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) : Fin m → 𝕜 :=
  (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m)⁻¹ *ᵥ
    Chapter06.g (fgmresCoeff M A (Chapter06.v₁ A b x₀)) (Chapter06.β A b x₀ : 𝕜) m

/-- **Algorithm 9.6** of [saad2003iterative] (FGMRES), line 12. Let $M_0, M_1, \ldots$ be the
preconditioners, $A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$, $r_0 = b - A x_0$
and $\beta = \|r_0\|_2$. Run the flexible Arnoldi process from $v_0 = r_0/\beta$ and let $y_m$
be the minimizer of $\|\beta e_1 - \bar H_m y\|_2$ computed by the Givens rotations. The FGMRES
iterate is
$$x_m = x_0 + Z_m y_m = x_0 + \sum_{j=0}^{m-1} (y_m)_j \, z_j.$$

The iterate is expanded in the preconditioned directions $z_j = M_j^{-1} v_j$, so the flexible
algorithm has to store them. -/
noncomputable def fgmres (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  x₀ + ∑ j : Fin m, fgmresY M A b x₀ m j • fgmresZ M A (Chapter06.v₁ A b x₀) (j : ℕ)

/-- The initial residual is $r_0 = \beta v_0$, the starting relation of the Arnoldi process of
Algorithm 9.6. -/
private theorem residual_eq_smul_fgmresV (M : ℕ → Matrix (Fin n) (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    b - op A x₀ = (Chapter06.β A b x₀ : 𝕜) • fgmresV M A (Chapter06.v₁ A b x₀) 0 := by
  rw [fgmresV_zero]
  exact (smul_inv_smul_norm (b - op A x₀)).symm

/-- If $R_m$ is nonsingular, the vector $y_m = R_m^{-1} g_m$ minimizes the quasi-residual
$\|\beta e_1 - \bar H_m y\|_2$ over all $y$. -/
private theorem isMinOn_fgmresY (M : ℕ → Matrix (Fin n) (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ}
    (hR : IsUnit (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m)) :
    IsMinOn
      (Krylov.quasiResidual (fgmresCoeff M A (Chapter06.v₁ A b x₀)) (Chapter06.β A b x₀ : 𝕜) m)
      Set.univ (fgmresY M A b x₀ m) :=
  (Chapter06.isMinOn_lsq _ _ (fun _ _ hij => fgmresCoeff_eq_zero_of_lt hij) hR).1

/-! ### Propositions 9.2 and 9.3 -/

/-- **Proposition 9.2** of [saad2003iterative], with (9.24)–(9.26). Let $M_0, M_1, \ldots$ be the
preconditioners, $A \in \mathbb{K}^{n \times n}$ and $b, x_0 \in \mathbb{K}^n$ with
$r_0 = b - A x_0 \neq 0$. Assume that the process does not break down before step $m$
($w_j \neq 0$ for all $j < m$) and that the triangular matrix $R_m$ of the Givens process is
nonsingular. Then the FGMRES iterate $x_m$ satisfies $x_m - x_0 \in \operatorname{span}\{z_0,
\ldots, z_{m-1}\}$ and
$$\|b - A x_m\|_2 \le \|b - Ax\|_2 \quad \text{for all } x \in x_0 + \operatorname{span}\{z_0,
  \ldots, z_{m-1}\}.$$

Unlike for GMRES, the space is not a Krylov subspace. The minimization uses only the two-family
relation (9.22) and the orthonormality of $V_{m+1}$. The proof uses the hypothesis $w_j \neq 0$
for the orthonormality of $V_{m+1}$, and the hypothesis on $R_m$ for the minimizer $y_m$. -/
theorem proposition_9_2 (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ} (hr : Chapter06.r₀ A b x₀ ≠ 0)
    (hbreak : ∀ j, j < m → fgmresW M A (Chapter06.v₁ A b x₀) j ≠ 0)
    (hR : IsUnit (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m)) :
    IsMinResidual (op A) b x₀
      (Submodule.span 𝕜 (Set.range fun j : Fin m => fgmresZ M A (Chapter06.v₁ A b x₀) (j : ℕ)))
      (fgmres M A b x₀ m) :=
  Krylov.FGMRES.isMinResidual (equation_9_22 M A _) (residual_eq_smul_fgmresV M A b x₀)
    (orthonormal_fgmresV (Chapter06.norm_v₁ A b x₀ hr) hbreak) (isMinOn_fgmresY M A b x₀ hR)

/-- **Proposition 9.3** of [saad2003iterative]. Let $M_0, M_1, \ldots$ be the preconditioners,
$A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$ with $r_0 = b - A x_0 \neq 0$, and
$m > 0$. Assume that $h_{i+1,i} \neq 0$ for $i + 1 < m$, that the square Hessenberg matrix $H_m$
is nonsingular, that $w_j \neq 0$ for all $j < m$, and that $R_m$ is nonsingular. Then
$$A x_m = b \iff h_{m+1,m} = 0,$$
where $h_{m+1,m}$ is the last subdiagonal entry of $\bar H_m$ (`fgmresCoeff M A v₁ m (m - 1)` in
$0$-based indexing).

The nonsingularity of $H_m$ is an extra hypothesis in the flexible case; by
`SaadSparse.Chapter09.hessenbergSq_isUnit_of_linearIndependent` it is not vacuous. The
hypothesis $w_{m-1} \neq 0$ gives $h_{m+1,m} = \|w_{m-1}\|_2 \neq 0$, so in this form the
statement says that $x_m$ is not exact. The direction from $h_{m+1,m} = 0$ to exactness is
stated, for an exact inner solve, by `SaadSparse.Chapter09.fgmres_eq_of_apply_fgmresZ_eq`. The
proof specializes `Krylov.FGMRES.apply_eq_iff_coeff_eq_zero`. The matrix $H_m$ is
`Krylov.hessenbergSqOf`. -/
theorem proposition_9_3 (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ} (hr : Chapter06.r₀ A b x₀ ≠ 0) (hm : 0 < m)
    (hsub : ∀ i, i + 1 < m → fgmresCoeff M A (Chapter06.v₁ A b x₀) (i + 1) i ≠ 0)
    (hH : IsUnit (Krylov.hessenbergSqOf (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m).det)
    (hbreak : ∀ j, j < m → fgmresW M A (Chapter06.v₁ A b x₀) j ≠ 0)
    (hR : IsUnit (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m)) :
    op A (fgmres M A b x₀ m) = b ↔ fgmresCoeff M A (Chapter06.v₁ A b x₀) m (m - 1) = 0 :=
  Krylov.FGMRES.apply_eq_iff_coeff_eq_zero (equation_9_22 M A _)
    (residual_eq_smul_fgmresV M A b x₀)
    (by simpa [Chapter06.β] using (RCLike.ofReal_ne_zero (K := 𝕜)).2 (norm_ne_zero_iff.2 hr))
    hm hsub hH (orthonormal_fgmresV (Chapter06.norm_v₁ A b x₀ hr) hbreak)
    (isMinOn_fgmresY M A b x₀ hR)

/-! ### Section 9.4.1: an exact preconditioning step ends the iteration -/

/-- **Section 9.4.1** of [saad2003iterative]. Let $\|v_0\|_2 = 1$, let $w_i \neq 0$ for all $i < j$,
and let the preconditioning be exact at step $j$: $A z_j = v_j$. Then the orthogonalization of
line 5 of Algorithm 9.6 leaves nothing: $w_j = 0$, and hence $h_{j+1,j} = 0$. The reason is that
$A z_j = v_j$ is one of the vectors against which it is orthogonalized. -/
theorem fgmresW_eq_zero_of_apply_fgmresZ_eq (hv : ‖v₁‖ = 1) {j : ℕ}
    (hbreak : ∀ i, i < j → fgmresW M A v₁ i ≠ 0)
    (hz : op A (fgmresZ M A v₁ j) = fgmresV M A v₁ j) : fgmresW M A v₁ j = 0 := by
  have hsum : ∑ i ∈ Finset.range (j + 1),
      inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j)) • fgmresV M A v₁ i
        = fgmresV M A v₁ j := by
    have hterm : ∀ i ∈ Finset.range (j + 1),
        inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j)) • fgmresV M A v₁ i
          = if i = j then fgmresV M A v₁ j else 0 := by
      intro i hi
      rw [hz, inner_fgmresV hv j hbreak i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) j le_rfl]
      by_cases hij : i = j
      · rw [ite_eq_left hij, ite_eq_left hij, one_smul, hij]
      · rw [ite_eq_right hij, ite_eq_right hij, zero_smul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (j + 1)) j
      (fun _ => fgmresV M A v₁ j), ite_eq_left (Finset.mem_range.2 (Nat.lt_succ_self j))]
  rw [fgmresW, hsum, hz, sub_self]

/-- **Section 9.4.1** of [saad2003iterative], an exact inner solve ends the outer iteration. Let
$M_0, M_1, \ldots$ be the preconditioners, $A \in \mathbb{K}^{n \times n}$ and
$b, x_0 \in \mathbb{K}^n$ with $r_0 = b - A x_0 \neq 0$. Assume that $w_i \neq 0$ for all
$i < j$, that $A z_j = v_j$, and that the matrices $H_{j+1}$ and $R_{j+1}$ are nonsingular. Then
the FGMRES iterate $x_{j+1}$ solves $Ax = b$.

The book calls this a consequence of Proposition 9.3. Here $h_{j+1,j} = 0$ by
`SaadSparse.Chapter09.fgmresW_eq_zero_of_apply_fgmresZ_eq`, and a vanishing subdiagonal entry
makes the iterate exact by `Krylov.FGMRES.apply_eq_of_coeff_eq_zero`. So any inner solve that is
exact on one vector ends the outer iteration. The statement
`SaadSparse.Chapter09.proposition_9_3` cannot be used directly, because its hypothesis
$w_j \neq 0$ fails at this step. -/
theorem fgmres_eq_of_apply_fgmresZ_eq (M : ℕ → Matrix (Fin n) (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n)) {j : ℕ}
    (hr : Chapter06.r₀ A b x₀ ≠ 0)
    (hbreak : ∀ i, i < j → fgmresW M A (Chapter06.v₁ A b x₀) i ≠ 0)
    (hz : op A (fgmresZ M A (Chapter06.v₁ A b x₀) j) = fgmresV M A (Chapter06.v₁ A b x₀) j)
    (hH : IsUnit (Krylov.hessenbergSqOf (fgmresCoeff M A (Chapter06.v₁ A b x₀)) (j + 1)).det)
    (hR : IsUnit (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) (j + 1))) :
    op A (fgmres M A b x₀ (j + 1)) = b := by
  have hw := fgmresW_eq_zero_of_apply_fgmresZ_eq (Chapter06.norm_v₁ A b x₀ hr) hbreak hz
  have hzero : fgmresCoeff M A (Chapter06.v₁ A b x₀) (j + 1) (j + 1 - 1) = 0 := by
    rw [Nat.add_sub_cancel, fgmresCoeff_succ_self, hw, norm_zero, RCLike.ofReal_zero]
  exact Krylov.FGMRES.apply_eq_of_coeff_eq_zero (equation_9_22 M A _)
    (residual_eq_smul_fgmresV M A b x₀) (Nat.succ_pos j) hH hzero
    (isMinOn_fgmresY M A b x₀ hR)

/-- **Remark after Proposition 9.3** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be
nonsingular, let $m > 0$, let the directions $z_0, \ldots, z_{m-1}$ of Algorithm 9.6 be linearly
independent, and let $h_{m+1,m} = 0$, so that the process breaks down at step $m$. Then the
square Hessenberg matrix $H_m$ is nonsingular. So the extra hypothesis of Proposition 9.3 is not
vacuous.

This is the flexible form of the first part of Proposition 6.9: $A Z_m = V_m H_m$, with $A Z_m$
of full rank, forces $H_m$ to have full rank. The entry $h_{m+1,m}$ is
`fgmresCoeff M A v₁ m (m - 1)`. -/
theorem hessenbergSq_isUnit_of_linearIndependent (M : ℕ → Matrix (Fin n) (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ} (hm : 0 < m)
    (hA : IsUnit A) (hz : LinearIndependent 𝕜 fun j : Fin m => fgmresZ M A v₁ (j : ℕ))
    (hlast : fgmresCoeff M A v₁ m (m - 1) = 0) :
    IsUnit (Krylov.hessenbergSqOf (fgmresCoeff M A v₁) m) := by
  refine Matrix.mulVec_injective_iff_isUnit.1 fun y w hyw => ?_
  have key : ∀ u : Fin m → 𝕜,
      (Krylov.hessenbergSqOf (fgmresCoeff M A v₁) m).mulVec u = 0 →
        ∀ i : Fin m, u i = 0 := by
    intro u hu
    have hzero : op A (∑ j, u j • fgmresZ M A v₁ (j : ℕ)) = 0 := by
      rw [(equation_9_22 M A v₁).apply_sum m u]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 i.isLt) with heq | hlt
      · have hi : i = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := Fin.ext heq
        have hrow : (Krylov.hessenbergOf (fgmresCoeff M A v₁) m).mulVec u
            ⟨m, Nat.lt_succ_self m⟩ = 0 := by
          simp only [Matrix.mulVec, dotProduct, Krylov.hessenbergOf, Matrix.of_apply]
          refine Finset.sum_eq_zero fun k _ => ?_
          rcases eq_or_ne (k : ℕ) (m - 1) with hk | hk
          · rw [hk, hlast, zero_mul]
          · rw [fgmresCoeff_eq_zero_of_lt (by omega : (k : ℕ) + 1 < m), zero_mul]
        rw [hi, hrow, zero_smul]
      · have hrow : (Krylov.hessenbergOf (fgmresCoeff M A v₁) m).mulVec u i
            = (Krylov.hessenbergSqOf (fgmresCoeff M A v₁) m).mulVec u ⟨(i : ℕ), hlt⟩ := by
          simp only [Matrix.mulVec, dotProduct, Krylov.hessenbergOf, Krylov.hessenbergSqOf,
            Matrix.of_apply]
        rw [hrow, hu, Pi.zero_apply, zero_smul]
    have hinj := Chapter06.injective_op_of_isUnit hA
    have h0 : ∑ j, u j • fgmresZ M A v₁ (j : ℕ) = 0 := by
      have := hinj (by rw [hzero, map_zero] : op A (∑ j, u j • fgmresZ M A v₁ (j : ℕ)) = op A 0)
      exact this
    exact fun i => Fintype.linearIndependent_iff.1 hz u h0 i
  have hsub : (Krylov.hessenbergSqOf (fgmresCoeff M A v₁) m).mulVec (y - w) = 0 := by
    rw [Matrix.mulVec_sub, hyw, sub_self]
  funext i
  have := key (y - w) hsub i
  simpa [sub_eq_zero] using this

/-! ### A constant preconditioner gives back Algorithm 9.5 -/

section Const

variable (M A : Matrix (Fin n) (Fin n) 𝕜)

/-- The operator of $A M^{-1}$ maps $x$ to $A(M^{-1} x)$. -/
private theorem op_rightPreconditioned_apply (x : EuclideanSpace 𝕜 (Fin n)) :
    op (rightPreconditioned M A) x = op A (op M⁻¹ x) := op_mul_apply A M⁻¹ x

/-- With a constant preconditioner $M$, the flexible Arnoldi basis is the Arnoldi basis of
$A M^{-1}$. -/
private theorem fgmresV_const (u : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    fgmresV (fun _ => M) A u j = Chapter06.arnoldiCGS (rightPreconditioned M A) u j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [fgmresV_zero, Chapter06.arnoldiCGS_zero]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hlt : ∀ i, i ≤ k →
          fgmresV (fun _ => M) A u i = Chapter06.arnoldiCGS (rightPreconditioned M A) u i :=
        fun i hi => ih i (by omega)
      have hAz : op A (op M⁻¹ (fgmresV (fun _ => M) A u k))
          = op (rightPreconditioned M A) (Chapter06.arnoldiCGS (rightPreconditioned M A) u k) := by
        rw [hlt k le_rfl, op_rightPreconditioned_apply]
      have hW : fgmresW (fun _ => M) A u k
          = Chapter06.arnoldiW (rightPreconditioned M A) u k := by
        simp only [fgmresW, fgmresZ, Chapter06.arnoldiW, Chapter06.arnoldiCoeff]
        rw [hAz]
        congr 1
        exact Finset.sum_congr rfl fun i hi =>
          by rw [hlt i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
      rw [fgmresV_succ, Chapter06.arnoldiCGS_succ, hW]

/-- With a constant preconditioner $M$, the vectors $w_j$ of Algorithm 9.6 are those of Algorithm
6.1 for $A M^{-1}$. -/
private theorem fgmresW_const (u : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    fgmresW (fun _ => M) A u k = Chapter06.arnoldiW (rightPreconditioned M A) u k := by
  have hAz : op A (op M⁻¹ (fgmresV (fun _ => M) A u k))
      = op (rightPreconditioned M A) (Chapter06.arnoldiCGS (rightPreconditioned M A) u k) := by
    rw [fgmresV_const, op_rightPreconditioned_apply]
  simp only [fgmresW, fgmresZ, Chapter06.arnoldiW, Chapter06.arnoldiCoeff]
  rw [hAz]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [fgmresV_const]

/-- With a constant preconditioner $M$ and a unit start vector, the Hessenberg coefficients of
Algorithm 9.6 are those of Algorithm 6.1 for $A M^{-1}$. -/
private theorem fgmresCoeff_const {u : EuclideanSpace 𝕜 (Fin n)} (hu : ‖u‖ = 1) :
    fgmresCoeff (fun _ => M) A u = Chapter06.arnoldiCoeff (rightPreconditioned M A) u := by
  funext i j
  rcases lt_trichotomy i (j + 1) with h | rfl | h
  · rw [fgmresCoeff_of_le (by omega), fgmresZ]
    simp only [fgmresV_const]
    rw [← op_rightPreconditioned_apply]
    rfl
  · rw [fgmresCoeff_succ_self, fgmresW_const, Chapter06.arnoldiCoeff_succ_self _ _ hu]
  · rw [fgmresCoeff_eq_zero_of_lt h, Chapter06.arnoldiCoeff_eq_zero_of_lt _ _ hu h]

/-- **Section 9.4.1** of [saad2003iterative], a constant preconditioner. Let
$M, A \in \mathbb{K}^{n \times n}$ with $M$ nonsingular, and let $b, x_0 \in \mathbb{K}^n$ with
$r_0 = b - A x_0 \neq 0$. Then FGMRES run with $M_j = M$ at every step gives the iterate of
GMRES with right preconditioning (Algorithm 9.5): for every $m$, the two iterates $x_m$ are
equal.

So the flexible algorithm generalizes Algorithm 9.5. -/
theorem fgmres_eq_gmresRight (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) (hM : IsUnit M)
    (hr : Chapter06.r₀ A b x₀ ≠ 0) :
    fgmres (fun _ => M) A b x₀ m = gmresRight M A b x₀ m := by
  have hMM : ∀ x : EuclideanSpace 𝕜 (Fin n), op M⁻¹ (op M x) = x := by
    intro x
    have h1 : (op (1 : Matrix (Fin n) (Fin n) 𝕜)) = LinearMap.id := Matrix.toEuclideanLin_one
    rw [← op_mul_apply, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).1 hM), h1,
      LinearMap.id_apply]
  have hr0 : Chapter06.r₀ (rightPreconditioned M A) b (op M x₀) = Chapter06.r₀ A b x₀ := by
    rw [Chapter06.r₀_def, Chapter06.r₀_def, op_rightPreconditioned_apply, hMM]
  have hbetaR : Chapter06.β (rightPreconditioned M A) b (op M x₀) = Chapter06.β A b x₀ :=
    congrArg norm hr0
  have hv1 : Chapter06.v₁ (rightPreconditioned M A) b (op M x₀) = Chapter06.v₁ A b x₀ := by
    have e1 : Chapter06.v₁ (rightPreconditioned M A) b (op M x₀)
        = (‖Chapter06.r₀ (rightPreconditioned M A) b (op M x₀)‖ : 𝕜) ⁻¹ •
            Chapter06.r₀ (rightPreconditioned M A) b (op M x₀) := rfl
    have e2 : Chapter06.v₁ A b x₀ = (‖Chapter06.r₀ A b x₀‖ : 𝕜)⁻¹ • Chapter06.r₀ A b x₀ := rfl
    rw [e1, e2, hr0]
  have hcoeff : fgmresCoeff (fun _ => M) A (Chapter06.v₁ A b x₀)
      = Chapter06.arnoldiCoeff (rightPreconditioned M A) (Chapter06.v₁ A b x₀) :=
    fgmresCoeff_const M A (Chapter06.norm_v₁ A b x₀ hr)
  have hy : fgmresY (fun _ => M) A b x₀ m
      = Chapter06.gmresY (rightPreconditioned M A) b (op M x₀) m := by
    rw [fgmresY, Chapter06.gmresY, hv1, hcoeff, hbetaR]
  have hvec : ∀ j : ℕ, fgmresZ (fun _ => M) A (Chapter06.v₁ A b x₀) j
      = op M⁻¹ (Arnoldi.vec (op (rightPreconditioned M A))
          (Chapter06.r₀ (rightPreconditioned M A) b (op M x₀)) j) := by
    intro j
    rw [fgmresZ, fgmresV_const, ← Chapter06.arnoldiCGS_v₁_apply, hv1]
  rw [fgmres, gmresRight, Chapter06.gmresFixed, Chapter06.krylovIterate_eq_sum, add_sub_cancel_left,
    map_sum, hy]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [hvec, map_smul]

end Const

/-! ### Section 9.4.2: flexible DQGMRES -/

/-- **Equation (9.28)** of [saad2003iterative], flexible DQGMRES. Let $M_0, M_1, \ldots$ be the
preconditioners, $x_0 \in \mathbb{K}^n$, $v_0, v_1, \ldots \in \mathbb{K}^n$ a basis sequence,
$h_{ij}$ the Hessenberg coefficients, $\beta \in \mathbb{K}$ and $k$ the truncation parameter.
Flexible DQGMRES is DQGMRES (Algorithm 6.13) with the preconditioned vectors $M_j^{-1} v_j$ in
place of $v_j$ in the direction update
$$p_j = \frac{1}{r_{jj}} \Big( M_j^{-1} v_j - \sum_{i=j-k+1}^{j-1} r_{ij} p_i \Big).$$
The preconditioned vector is used at once and need not be stored.

The book states nothing about the method beyond the algorithm. The basis and the coefficients
are inputs, as for `SaadSparse.Chapter06.dqgmres`. The identification with Algorithm 6.13 at
$M_j = I$ is `SaadSparse.Chapter09.fdqgmres_eq_dqgmres`. -/
noncomputable def fdqgmres (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (x₀ : EuclideanSpace 𝕜 (Fin n))
    (v : ℕ → EuclideanSpace 𝕜 (Fin n)) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k : ℕ) :
    ℕ → EuclideanSpace 𝕜 (Fin n) :=
  Chapter06.dqgmres x₀ (fun j => op (M j)⁻¹ (v j)) h β k

/-- **Equation (9.28)** of [saad2003iterative]. With the identity preconditioner $M_j = I$ at every
step, flexible DQGMRES gives the iterates of DQGMRES (Algorithm 6.13), for the same inputs
$x_0$, $v_j$, $h_{ij}$, $\beta$ and $k$. -/
theorem fdqgmres_eq_dqgmres (x₀ : EuclideanSpace 𝕜 (Fin n)) (v : ℕ → EuclideanSpace 𝕜 (Fin n))
    (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k : ℕ) :
    fdqgmres (fun _ => (1 : Matrix (Fin n) (Fin n) 𝕜)) x₀ v h β k
      = Chapter06.dqgmres x₀ v h β k := by
  have hv : (fun j => op ((1 : Matrix (Fin n) (Fin n) 𝕜))⁻¹ (v j)) = v := by
    funext j
    have h1 : (op (1 : Matrix (Fin n) (Fin n) 𝕜)) = LinearMap.id := Matrix.toEuclideanLin_one
    rw [_root_.inv_one, h1, LinearMap.id_apply]
  rw [fdqgmres, hv]

end SaadSparse.Chapter09
