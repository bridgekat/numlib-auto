/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.SaadSparse.Chapter07.Section01

/-!
# Saad, Section 7.2: The two-sided Lanczos algorithm for linear systems

This module formalizes Section 7.2 of [saad2003iterative]. Algorithm 7.2 runs the Lanczos
biorthogonalization procedure (Algorithm 7.1) from $v_1 = r_0/\beta$, with $r_0 = b - Ax_0$ and
$\beta = \|r_0\|_2$, and from a dual starting vector $w_1$, then solves the tridiagonal system
$T_m y_m = \beta e_1$ and sets $x_m = x_0 + V_m y_m$. It has the form of FOM (Section 6.4), with the
Arnoldi basis replaced by the biorthogonal basis. The iterate is the Petrov–Galerkin approximation
onto $\mathcal{K}_m(A, v_1)$ orthogonally to $\mathcal{K}_m(A^H, w_1)$, and by (7.9) its residual is
a multiple of the next Lanczos vector,
$$b - Ax_m = -\delta_{m+1} (e_m^T y_m)\, v_{m+1}.$$
At a lucky breakdown of Algorithm 7.1 the iterate is exact. The proofs use
`SaadSparse.Chapter07.bilanczos_hessenbergRelation` of
`NumlibSurface.SaadSparse.Chapter07.Section01`, which gives the backbone
`Krylov.HessenbergRelation`, so the residual formula is the same lemma that serves FOM.

## Main definitions

* Algorithm 7.2, `SaadSparse.Chapter07.lanczosSolve`: the iterate
  $x_m = x_0 + V_m T_m^{-1} (\beta e_1)$ of the two-sided Lanczos algorithm for linear systems.

## Main results

* Section 7.2, `SaadSparse.Chapter07.lanczosSolve_isPetrovGalerkin`: the iterate of Algorithm 7.2 is
  the Petrov–Galerkin approximation onto $\mathcal{K}_m(A, v_1)$ orthogonally to
  $\mathcal{K}_m(A^H, w_1)$.
* Equation (7.9), `SaadSparse.Chapter07.equation_7_9`: $\|b - Ax_m\|_2 = |\delta_{m+1} (e_m^T
  y_m)|\, \|v_{m+1}\|_2$.
* Section 7.1.2, `SaadSparse.Chapter07.lanczosSolve_eq_of_bilanczosVhat_eq_zero`: at a lucky
  breakdown, the iterate of Algorithm 7.2 is exact.

## Conventions

* Indices are $0$-based, as in `NumlibSurface.SaadSparse.Chapter07.Section01`. The book's $v_{j+1}$
  is `SaadSparse.Chapter07.bilanczosV A v₁ w₁ j`.
* The book's $\delta_{m+1}$ is `SaadSparse.Chapter07.bilanczosDelta A v₁ w₁ m`.

## Implementation notes

* The Petrov–Galerkin identification needs only the no-breakdown hypothesis of Section 7.1 and the
  nonsingularity of $T_m$, since the orthogonality is tested against the dual basis directly through
  (7.5).
* The factor $\|v_{m+1}\|_2$ in (7.9), which is $1$ in FOM and in the symmetric Lanczos method, is
  what remains when the basis is only biorthogonal.
* The other half of the lucky-breakdown claim of Section 7.1.2, that the Krylov subspace is
  invariant, is `SaadSparse.Chapter07.krylov_mem_invtSubmodule_of_bilanczosVhat_eq_zero`.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter07

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### The starting vector -/

/-- For every $A$, $b$ and $x_0$, $\beta v_1 = r_0$ with $\beta = \|r_0\|_2$ and $r_0 = b - Ax_0$:
the normalization of line 1 of Algorithm 6.4. No hypothesis is needed, since $r_0 = 0$ makes
both sides $0$. -/
theorem smul_v₁_eq_r₀ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (Chapter06.β A b x₀ : 𝕜) • Chapter06.v₁ A b x₀ = b - op A x₀ := by
  rw [Chapter06.v₁, smul_smul]
  rcases eq_or_ne (Chapter06.β A b x₀) 0 with h | h
  · have hr : Chapter06.r₀ A b x₀ = 0 := norm_eq_zero.1 h
    rw [hr, smul_zero]
    exact hr.symm
  · rw [mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 h), one_smul]

/-! ### Algorithm 7.2 -/

section Algorithm

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- The coordinate vector $y_m = T_m^{-1} (\beta e_1)$ of the last line of Algorithm 7.2, where
$T_m$ is the tridiagonal matrix of Algorithm 7.1 started from $v_1 = r_0/\beta$ and $w_1$.

If $T_m$ is singular, which is the breakdown case of the book, `Matrix.inv` gives $0$ and so
$y_m = 0$. -/
noncomputable def lanczosSolveY (m : ℕ) : Fin m → 𝕜 :=
  (T A (Chapter06.v₁ A b x₀) w₁ m)⁻¹ *ᵥ ((Chapter06.β A b x₀ : 𝕜) • Chapter06.e₁ m)

/-- **Algorithm 7.2** of [saad2003iterative] (the two-sided Lanczos algorithm for linear systems).
For $A \in \mathbb{K}^{n \times n}$, $b, x_0, w_1 \in \mathbb{K}^n$ and $m \in \mathbb{N}$, the
iterate
$$x_m = x_0 + V_m T_m^{-1} (\beta e_1),$$
where $V_m$ and $T_m$ are the primal Lanczos basis and the tridiagonal matrix of Algorithm 7.1
started from $v_1 = r_0/\beta$ and the dual vector $w_1$, with $r_0 = b - Ax_0$ and
$\beta = \|r_0\|_2$.

If $T_m$ is singular, the inverse is $0$ in Lean and $x_m = x_0$. The dual vector $w_1$ is used
as given; the normalization $(v_1, w_1) = 1$ is part of the hypothesis
`SaadSparse.Chapter07.NoBreakdown` of the results below. -/
noncomputable def lanczosSolve (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  x₀ + Matrix.toEuclideanLin (V A (Chapter06.v₁ A b x₀) w₁ m)
    (WithLp.toLp 2 (lanczosSolveY A b x₀ w₁ m))

/-- The iterate of Algorithm 7.2 is $x_m = x_0 + V_m y_m = x_0 + \sum_j (y_m)_j v_j$. -/
theorem lanczosSolve_eq_add_sum (m : ℕ) :
    lanczosSolve A b x₀ w₁ m
      = x₀ + ∑ j, lanczosSolveY A b x₀ w₁ m j • bilanczosV A (Chapter06.v₁ A b x₀) w₁ (j : ℕ) :=
  congrArg (fun z => x₀ + z)
    (Chapter06.toEuclideanLin_colMatrix_apply _ (lanczosSolveY A b x₀ w₁ m))

/-- With $m = 0$ steps, the iterate of Algorithm 7.2 is $x_0$. -/
@[simp] theorem lanczosSolve_zero : lanczosSolve A b x₀ w₁ 0 = x₀ := by
  rw [lanczosSolve_eq_add_sum]
  simp

/-- If $T_m$ is nonsingular, then $y_m$ solves the tridiagonal system $T_m y_m = \beta e_1$ of
Algorithm 7.2. -/
theorem T_mulVec_lanczosSolveY {m : ℕ} (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ m)) :
    T A (Chapter06.v₁ A b x₀) w₁ m *ᵥ lanczosSolveY A b x₀ w₁ m
      = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) m := by
  rw [lanczosSolveY, Matrix.mulVec_nonsing_inv_mulVec hT, Chapter06.smul_e₁_eq_firstVec]

end Algorithm

/-! ### The Petrov–Galerkin identification -/

section PetrovGalerkin

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- Equation (7.5) entry by entry: while Algorithm 7.1 has not broken down, $(Av_j, w_i) = t_{ij}$.
-/
private theorem inner_bilanczosW_apply_bilanczosV {v : EuclideanSpace 𝕜 (Fin n)}
    (h : NoBreakdown A v w₁ m) {i j : ℕ} (hi : i ≤ m) (hj : j + 1 ≤ m) :
    inner 𝕜 (bilanczosW A v w₁ i) (op A (bilanczosV A v w₁ j)) = bilanczosCoeff A v w₁ i j := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  rw [bilanczosW_eq, bilanczosV_eq, bilanczosCoeff_eq]
  exact BiLanczos.inner_dualVec_apply_vec h.toBiLanczos hi (by omega)

/-- **Section 7.2** of [saad2003iterative], the iterate of Algorithm 7.2 as a projection. Assume
that Algorithm 7.1, started from $v_1 = r_0/\beta$ and $w_1$, runs $m$ steps without breakdown,
and that $T_m$ is nonsingular. Then the iterate $x_m$ of Algorithm 7.2 is the Petrov–Galerkin
approximation onto $\mathcal{K}_m(A, v_1)$ orthogonally to $\mathcal{K}_m(A^H, w_1)$:
$$x_m - x_0 \in \mathcal{K}_m(A, v_1), \qquad b - Ax_m \perp \mathcal{K}_m(A^H, w_1).$$

This is the projection process from which the section derives the algorithm. The predicate is
the backbone `IsPetrovGalerkin`. -/
theorem lanczosSolve_isPetrovGalerkin (h : NoBreakdown A (Chapter06.v₁ A b x₀) w₁ m)
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ m)) :
    IsPetrovGalerkin (op A) b x₀ (Chapter06.krylov A (Chapter06.v₁ A b x₀) m)
      (Chapter06.krylov Aᴴ w₁ m) (lanczosSolve A b x₀ w₁ m) := by
  have hsum := lanczosSolve_eq_add_sum A b x₀ w₁ m
  constructor
  · rw [hsum, add_sub_cancel_left, ← (proposition_7_1_span h).1]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [← (proposition_7_1_span h).2, Submodule.mem_orthogonal_span]
    rintro _ ⟨i, rfl⟩
    have hres : b - op A (lanczosSolve A b x₀ w₁ m)
        = (b - op A x₀)
          - ∑ j, lanczosSolveY A b x₀ w₁ m j
              • op A (bilanczosV A (Chapter06.v₁ A b x₀) w₁ (j : ℕ)) := by
      rw [hsum, map_add, map_sum]
      simp only [map_smul]
      abel
    have hstart : inner 𝕜 (bilanczosW A (Chapter06.v₁ A b x₀) w₁ (i : ℕ)) (b - op A x₀)
        = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) m i := by
      have h0 : b - op A x₀
          = (Chapter06.β A b x₀ : 𝕜) • bilanczosV A (Chapter06.v₁ A b x₀) w₁ 0 := by
        rw [bilanczosV_zero]
        exact (smul_v₁_eq_r₀ A b x₀).symm
      rw [h0, inner_smul_right, proposition_7_1 h (le_of_lt i.2) (Nat.zero_le m)]
      by_cases h1 : (i : ℕ) = 0 <;> simp [Krylov.firstVec, h1]
    have hcoeff : ∀ j : Fin m,
        inner 𝕜 (bilanczosW A (Chapter06.v₁ A b x₀) w₁ (i : ℕ))
            (op A (bilanczosV A (Chapter06.v₁ A b x₀) w₁ (j : ℕ)))
          = T A (Chapter06.v₁ A b x₀) w₁ m i j := fun j =>
      inner_bilanczosW_apply_bilanczosV h (le_of_lt i.2) j.2
    have hmv : (T A (Chapter06.v₁ A b x₀) w₁ m *ᵥ lanczosSolveY A b x₀ w₁ m) i
        = ∑ j, lanczosSolveY A b x₀ w₁ m j * T A (Chapter06.v₁ A b x₀) w₁ m i j := by
      rw [Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hres, inner_sub_right, inner_sum, hstart]
    simp only [inner_smul_right, hcoeff]
    rw [← hmv, T_mulVec_lanczosSolveY A b x₀ w₁ hT, sub_self]

end PetrovGalerkin

/-! ### (7.9): the residual norm -/

section Residual

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- **Equation (7.9)** of [saad2003iterative], in vector form. Assume that Algorithm 7.1, started
from $v_1 = r_0/\beta$ and $w_1$, has no serious breakdown, that $m \ge 1$, and that $T_m$ is
nonsingular. Then the residual of the iterate of Algorithm 7.2 is a multiple of the next Lanczos
vector:
$$b - Ax_m = -\delta_{m+1} (e_m^T y_m)\, v_{m+1}.$$
-/
theorem residual_lanczosSolve (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ m)) (hm : 0 < m) :
    b - op A (lanczosSolve A b x₀ w₁ m)
      = -(bilanczosDelta A (Chapter06.v₁ A b x₀) w₁ m
          * lanczosSolveY A b x₀ w₁ m ⟨m - 1, by omega⟩)
        • bilanczosV A (Chapter06.v₁ A b x₀) w₁ m := by
  have hstart : b - op A x₀
      = (Chapter06.β A b x₀ : 𝕜) • bilanczosV A (Chapter06.v₁ A b x₀) w₁ 0 := by
    rw [bilanczosV_zero]
    exact (smul_v₁_eq_r₀ A b x₀).symm
  have hmul : Krylov.hessenbergSqOf (bilanczosCoeff A (Chapter06.v₁ A b x₀) w₁) m
      *ᵥ lanczosSolveY A b x₀ w₁ m = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) m := by
    rw [← T_eq_hessenbergSqOf]
    exact T_mulVec_lanczosSolveY A b x₀ w₁ hT
  have hdelta : bilanczosCoeff A (Chapter06.v₁ A b x₀) w₁ m (m - 1)
      = bilanczosDelta A (Chapter06.v₁ A b x₀) w₁ m := by
    obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, bilanczosCoeff_succ_self]
  rw [lanczosSolve_eq_add_sum, ← hdelta]
  exact (bilanczos_hessenbergRelation h).residual_eq_of_mulVec_eq hstart hm _ hmul

/-- **Equation (7.9)** of [saad2003iterative]. Assume that Algorithm 7.1, started from
$v_1 = r_0/\beta$ and $w_1$, has no serious breakdown, that $m \ge 1$, and that $T_m$ is
nonsingular. Then the residual norm of the iterate of Algorithm 7.2 is
$$\|b - Ax_m\|_2 = |\delta_{m+1} (e_m^T y_m)|\, \|v_{m+1}\|_2,$$
so it is available without forming the iterate.

This is the analogue of (6.18) for FOM and of (6.87) for the symmetric Lanczos method. The
factor $\|v_{m+1}\|_2$, which is $1$ there, is what a basis that is only biorthogonal leaves. -/
theorem equation_7_9 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ m)) (hm : 0 < m) :
    ‖b - op A (lanczosSolve A b x₀ w₁ m)‖
      = ‖bilanczosDelta A (Chapter06.v₁ A b x₀) w₁ m
          * lanczosSolveY A b x₀ w₁ m ⟨m - 1, by omega⟩‖
        * ‖bilanczosV A (Chapter06.v₁ A b x₀) w₁ m‖ := by
  rw [residual_lanczosSolve h hT hm, norm_smul, norm_neg]

end Residual

/-! ### §7.1.2: exactness at a lucky breakdown -/

section LuckyBreakdown

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- **Section 7.1.2** of [saad2003iterative], the lucky breakdown. Let $k = m + 1$. Assume that
Algorithm 7.1, started from $v_1 = r_0/\beta$ and $w_1$, runs $m$ steps without breakdown, that
the next unnormalized vector is $\hat v_{k+1} = 0$, and that $T_k$ is nonsingular. Then the
iterate $x_k$ of Algorithm 7.2 is exact: $b - Ax_k = 0$.

By (7.9) the residual is a multiple of $\delta_{k+1}$, and $\delta_{k+1}$ vanishes with
$\hat v_{k+1}$. The hypothesis of no serious breakdown that (7.9) needs holds here by
`SaadSparse.Chapter07.noSeriousBreakdown_of_bilanczosVhat_eq_zero`. The other half of the claim
of the book, that $\mathcal{K}_k(A, v_1)$ is then invariant under $A$, is
`SaadSparse.Chapter07.krylov_mem_invtSubmodule_of_bilanczosVhat_eq_zero`. Nothing of this kind
holds at a serious breakdown, which is the distinction that Section 7.1.2 draws. The dual lucky
breakdown $\hat w_{k+1} = 0$ makes the span of $w_1, \dots, w_k$ invariant under $A^H$ and the
iterate of the transposed system exact, but says nothing about $Ax = b$. -/
theorem lanczosSolve_eq_of_bilanczosVhat_eq_zero (h : NoBreakdown A (Chapter06.v₁ A b x₀) w₁ m)
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1)))
    (hv : bilanczosVhat A (Chapter06.v₁ A b x₀) w₁ m = 0) :
    b - op A (lanczosSolve A b x₀ w₁ (m + 1)) = 0 := by
  have hd : bilanczosDelta A (Chapter06.v₁ A b x₀) w₁ (m + 1) = 0 := by
    rw [bilanczosDelta_succ, hv, inner_zero_right, norm_zero, Real.sqrt_zero, RCLike.ofReal_zero]
  rw [residual_lanczosSolve (noSeriousBreakdown_of_bilanczosVhat_eq_zero h hv) hT (by omega), hd,
    zero_mul, neg_zero, zero_smul]

end LuckyBreakdown

end SaadSparse.Chapter07
