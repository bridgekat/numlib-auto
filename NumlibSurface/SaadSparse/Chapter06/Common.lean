/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Subspace
import NumlibSurface.SaadSparse.Chapter06.Section02

/-!
# Saad, Chapter 6: The data of a linear system

This module names the quantities from which every Krylov method of Chapter 6 of [saad2003iterative]
starts. For a linear system $Ax = b$ with $A \in \mathbb{K}^{n \times n}$ and an initial guess
$x_0$, these are the initial residual $r_0 = b - Ax_0$, its norm $\beta = \|r_0\|_2$, and the unit
vector $v_1 = r_0 / \beta$ on which Algorithm 6.1 runs. The module also defines the first coordinate
vector $e_1 \in \mathbb{K}^m$, and the number of Arnoldi steps that an algorithm actually performs,
$\min(m, \mu)$ with $\mu$ the grade of $v_1$. It proves what Section 6.2 gives about $v_1$: it is a
unit vector when $r_0 \neq 0$, and it has the grade and the Krylov subspaces of $r_0$.

## Main definitions

* `SaadSparse.Chapter06.r₀`: the initial residual $r_0 = b - Ax_0$.
* `SaadSparse.Chapter06.β`: its norm $\beta = \|r_0\|_2$.
* `SaadSparse.Chapter06.v₁`: the starting vector $v_1 = r_0 / \beta$.
* `SaadSparse.Chapter06.e₁`: the first coordinate vector $e_1 \in \mathbb{K}^m$.
* `SaadSparse.Chapter06.mEff`: the number $\min(m, \mu)$ of Arnoldi steps performed.

## Main results

* `SaadSparse.Chapter06.norm_v₁`: $\|v_1\| = 1$ if $r_0 \neq 0$.
* `SaadSparse.Chapter06.grade_v₁`: the grade of $v_1$ is the backbone grade of $r_0$.
* `SaadSparse.Chapter06.krylov_v₁`: $\mathcal{K}_m(A, v_1)$ is the backbone Krylov subspace of
  $r_0$.

## Implementation notes

* The scalar field $\mathbb{K}$ is `𝕜` with `[RCLike 𝕜]`, so that it is $\mathbb{R}$ or
  $\mathbb{C}$.
* The backbone indexes the Arnoldi process by the residual $r_0$ itself, while the book runs it on
  $v_1$. The translation between the two concerns Algorithm 6.1, so it is in
  `NumlibSurface.SaadSparse.Chapter06.Section03`. This module comes between
  `NumlibSurface.SaadSparse.Chapter06.Section02`, whose grade and Krylov subspaces it uses, and
  Section 6.3, which needs $v_1$.
-/

open scoped Matrix

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The initial residual and the starting vector -/

/-- **Algorithms 6.4 and 6.9** of [saad2003iterative], line 1. The **initial residual** of the
system $Ax = b$ at the initial guess $x_0$ is $r_0 = b - Ax_0$. -/
noncomputable abbrev r₀ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : 𝔼 := b - op A x₀

/-- **Algorithms 6.4 and 6.9** of [saad2003iterative], line 1. The norm $\beta = \|r_0\|_2$ of the
initial residual. -/
noncomputable abbrev β (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : ℝ := ‖r₀ A b x₀‖

/-- **Algorithms 6.4 and 6.9** of [saad2003iterative], line 1. The **starting vector** of the
Arnoldi process is $v_1 = r_0 / \beta$.

If $r_0 = 0$, then $\beta = 0$ and $v_1 = 0$, by Lean's convention $\beta^{-1} = 0$ at
$\beta = 0$. -/
noncomputable def v₁ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : 𝔼 :=
  (β A b x₀ : 𝕜)⁻¹ • r₀ A b x₀

/-- The **first coordinate vector** $e_1 = (1, 0, \dots, 0) \in \mathbb{K}^m$, used in the
right-hand side $\beta e_1$ of the projected systems of FOM and GMRES. For $m = 0$ it is the
empty vector. -/
def e₁ (m : ℕ) : Fin m → 𝕜 := fun i => if (i : ℕ) = 0 then 1 else 0

/-- The number of Arnoldi steps that an algorithm of Chapter 6 of [saad2003iterative] actually
performs when it is asked for $m$ steps: $\min(m, \mu)$, where $\mu$ is the grade of $v_1$. This
is the instruction "if $h_{j+1,j} = 0$ then set $m := j$": the Arnoldi process stops at the
grade of $v_1$. -/
noncomputable def mEff (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℕ :=
  min m (grade A (v₁ A b x₀))

/-- The vector $c \, e_1 \in \mathbb{K}^m$ is the backbone vector `Krylov.firstVec c m`. -/
theorem smul_e₁_eq_firstVec (c : 𝕜) (m : ℕ) : c • e₁ m = Krylov.firstVec c m := by
  funext i
  by_cases h : (i : ℕ) = 0 <;> simp [e₁, Krylov.firstVec, h]

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The initial residual unfolds to $r_0 = b - Ax_0$. -/
theorem r₀_def : r₀ A b x₀ = b - op A x₀ := rfl

/-- The norm $\beta$, as a scalar of $\mathbb{K}$, unfolds to $\|b - Ax_0\|$. -/
theorem β_def : (β A b x₀ : 𝕜) = (‖b - op A x₀‖ : 𝕜) := rfl

/-- The norm $\beta$, as a scalar of $\mathbb{K}$, is $\|r_0\|$. -/
theorem β_eq_norm_r₀ : (β A b x₀ : 𝕜) = (‖r₀ A b x₀‖ : 𝕜) := rfl

/-- The starting vector unfolds to $v_1 = \|b - Ax_0\|^{-1} (b - Ax_0)$. -/
theorem v₁_def : v₁ A b x₀ = (‖b - op A x₀‖ : 𝕜)⁻¹ • (b - op A x₀) := rfl

/-- The number of Arnoldi steps that are actually performed never exceeds the grade of $v_1$. -/
theorem mEff_le (m : ℕ) : mEff A b x₀ m ≤ grade A (v₁ A b x₀) := min_le_right _ _

/-- For a nonzero vector $r$, the vector $r / \|r\|$ has norm $1$. This is the normalization
$v_1 = r_0 / \beta$ of the algorithms that start from a residual. -/
theorem norm_norm_inv_smul {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) :
    ‖(‖r‖⁻¹ : 𝕜) • r‖ = 1 := by
  rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hr)]

/-- If $r_0 \neq 0$, that is, if $x_0$ does not already solve the system, then $\|v_1\| = 1$. -/
theorem norm_v₁ (hr : r₀ A b x₀ ≠ 0) : ‖v₁ A b x₀‖ = 1 :=
  norm_norm_inv_smul hr

/-- The grade of $v_1$ with respect to $A$ is the backbone grade `Krylov.grade` of $r_0$ with
respect to the operator of $A$. This holds also for $r_0 = 0$, where both grades are $0$;
otherwise $v_1$ and $r_0$ are proportional. -/
theorem grade_v₁ : grade A (v₁ A b x₀) = Krylov.grade (op A) (r₀ A b x₀) := by
  rcases eq_or_ne (r₀ A b x₀) 0 with h | h
  · rw [v₁, h, smul_zero]
    exact grade_eq A 0
  · rw [v₁, grade_normalize A h, grade_eq]

/-- For every $m$, the Krylov subspace $\mathcal{K}_m(A, v_1)$ is the backbone Krylov subspace
`Krylov.subspace` of the operator of $A$ and $r_0$. This holds also for $r_0 = 0$; otherwise
$v_1$ and $r_0$ are proportional. -/
theorem krylov_v₁ (m : ℕ) : krylov A (v₁ A b x₀) m = Krylov.subspace (op A) (r₀ A b x₀) m := by
  rcases eq_or_ne (r₀ A b x₀) 0 with h | h
  · rw [v₁, h, smul_zero, krylov_eq]
  · have hc : ((‖r₀ A b x₀‖ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (by simpa using norm_ne_zero_iff.2 h)
    rw [v₁, krylov_smul A _ hc, krylov_eq]

end General

end SaadSparse.Chapter06
