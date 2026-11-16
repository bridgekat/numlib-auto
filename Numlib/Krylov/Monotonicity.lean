/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CG
import Numlib.Krylov.CR
import Numlib.Conditioning.LinearSystem

/-!
# Monotonicity of Krylov iterates on symmetric positive definite systems

Let $A$ be a symmetric coercive operator on a finite-dimensional inner product space $E$, let
$b \in E$, and let $x_k$ be a minimal-residual Krylov iterate at step $k$ for $Ax = b$, as computed
by MINRES, CR or GMRES. This file proves the monotonicity results of [fong2012cg], Theorems 2.3–2.5
and 3.1, for any such sequence of iterates. From $x_0 = 0$ the norm $\|x_k\|$ is nondecreasing and
the normwise relative backward error is nonincreasing; from any $x_0$ the errors $\|x^* - x_k\|$ and
$\|x^* - x_k\|_A$ are nonincreasing. In addition, $\|A x_k\|$ is nondecreasing from $x_0 = 0$ for
every operator $A$ ([choi2006iterative], Lemma 2.20).

The same argument applied to the Galerkin iterates gives the older counterparts for CG on the same
systems: $\|x_k\|$ is nondecreasing from $x_0 = 0$, a result of [steihaug1983conjugate] that appears
as the CG column of [fong2012cg], Table 5.1, and $\|x^* - x_k\|$ is nonincreasing
([hestenes1952methods], Theorem 6:3).

## Main results

* `Krylov.IsMinResidualIterate.eq_CR_iterate`: a minimal-residual iterate of a symmetric coercive
  system is the CR iterate.
* `Krylov.IsMinResidualIterate.norm_monotone`: $\|x_k\|$ is nondecreasing from $x_0 = 0$.
* `Krylov.IsMinResidualIterate.norm_error_antitone`: $\|x^* - x_k\|$ is nonincreasing.
* `Krylov.IsMinResidualIterate.energyNorm_error_antitone`: $\|x^* - x_k\|_A$ is nonincreasing.
* `Krylov.IsMinResidualIterate.norm_apply_monotone`: $\|A x_k\|$ is nondecreasing from $x_0 = 0$,
  for every operator $A$.
* `Krylov.IsMinResidualIterate.backwardError_antitone`: the backward error
  $\|r_k\| / (\alpha \|A\| \|x_k\| + \beta \|b\|)$ is nonincreasing from $x_0 = 0$.
* `Krylov.IsMinResidualIterate.norm_residual_div_norm_antitoneOn`: $\|r_k\| / \|x_k\|$ is
  nonincreasing for $k \ge 1$.
* `Krylov.IsGalerkinIterate.eq_CG_iterate`: a Galerkin iterate of a symmetric coercive system is the
  CG iterate.
* `Krylov.IsGalerkinIterate.norm_monotone`: the CG iterates have nondecreasing norm from $x_0 = 0$.
* `Krylov.IsGalerkinIterate.norm_error_antitone`: the CG errors $\|x^* - x_k\|$ are nonincreasing.

## Proof outline

A minimal-residual iterate of a symmetric coercive system is unique, so it equals the iterate of the
conjugate residual method `CR.iterate`. The monotonicity statements then follow from the sign
properties of the CR recurrence in `Numlib.Krylov.CR`. The Galerkin results follow in the same way
from the CG recurrence `CG.iterate`.

## Implementation notes

* A symmetric coercive operator (`LinearMap.IsSymmetricCoercive`) is symmetric and satisfies
  $\operatorname{Re} \langle Ax, x \rangle \ge c \|x\|^2$ for some $c > 0$. In finite dimension this
  means symmetric (or Hermitian) positive definite.
* The results are stated for any sequence of iterates that satisfies the specification
  `Krylov.IsMinResidualIterate` or `Krylov.IsGalerkinIterate`, not for one algorithm.
* The residual is $r_k = b - A x_k$, and $\|x\|_A = \sqrt{\operatorname{Re} \langle Ax, x \rangle}$
  is `energyNorm`.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive) {b : E}

namespace Krylov.IsMinResidualIterate

include hA

omit [FiniteDimensional 𝕜 E] in
/-- Let $A$ be a symmetric coercive operator on an inner product space $E$, and let $b, x_0 \in E$.
If $x$ is a minimal-residual iterate at step $k$ for $Ax = b$ from $x_0$, then $x$ is the
iterate at step $k$ of the conjugate residual method, `(CR.iterate A b x₀ k).x`. -/
theorem eq_CR_iterate {x₀ : E} {k : ℕ} {x : E} (hx : IsMinResidualIterate A b x₀ k x) :
    x = (CR.iterate A b x₀ k).x := by
  obtain ⟨y, -, huniq⟩ :=
    existsUnique_isMinResidualIterate_of_injective hA.isCoercive.injective b x₀ k
  exact (huniq x hx).trans (huniq _ (CR.isMinResidualIterate b x₀ hA k)).symm

/-- Let $A$ be a symmetric coercive operator on a finite-dimensional inner product space $E$ and let
$b \in E$. If $x_k$ is a minimal-residual iterate at step $k$ for $Ax = b$ from $x_0 = 0$, for
every $k$, then $\|x_k\|$ is nondecreasing in $k$. This is Theorem 2.3 of [fong2012cg]. -/
theorem norm_monotone {x : ℕ → E} (hx : ∀ k, IsMinResidualIterate A b 0 k (x k)) :
    Monotone fun k => ‖x k‖ := by
  have h : ∀ k, x k = (CR.iterate A b 0 k).x := fun k => eq_CR_iterate hA (hx k)
  simpa only [h] using CR.norm_iterate_monotone b hA

/-- Let $A$ be a symmetric coercive operator on a finite-dimensional inner product space $E$, let
$b, x_0 \in E$, and let $A x^* = b$. If $x_k$ is a minimal-residual iterate at step $k$ for
$Ax = b$ from $x_0$, for every $k$, then the error $\|x^* - x_k\|$ is nonincreasing in $k$. This
is Theorem 2.4 of [fong2012cg]. -/
theorem norm_error_antitone {x₀ : E} {x : ℕ → E} (hx : ∀ k, IsMinResidualIterate A b x₀ k (x k))
    {xstar : E} (hstar : A xstar = b) : Antitone fun k => ‖xstar - x k‖ := by
  have h : ∀ k, x k = (CR.iterate A b x₀ k).x := fun k => eq_CR_iterate hA (hx k)
  simpa only [h] using CR.norm_error_antitone b x₀ hA hstar

/-- Let $A$ be a symmetric coercive operator on a finite-dimensional inner product space $E$, let
$b, x_0 \in E$, and let $A x^* = b$. If $x_k$ is a minimal-residual iterate at step $k$ for
$Ax = b$ from $x_0$, for every $k$, then the energy-norm error $\|x^* - x_k\|_A$ is
nonincreasing in $k$. This is Theorem 2.5 of [fong2012cg]. -/
theorem energyNorm_error_antitone {x₀ : E} {x : ℕ → E}
    (hx : ∀ k, IsMinResidualIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - x k) := by
  have h : ∀ k, x k = (CR.iterate A b x₀ k).x := fun k => eq_CR_iterate hA (hx k)
  simpa only [h] using CR.energyNorm_error_antitone b x₀ hA hstar

omit hA [FiniteDimensional 𝕜 E] in
/-- Let $A$ be any linear operator on an inner product space $E$ and let $b \in E$. If $x_k$ is a
minimal-residual iterate at step $k$ for $Ax = b$ from $x_0 = 0$, for every $k$, then
$\|A x_k\|$ is nondecreasing in $k$. This is Lemma 2.20 of [choi2006iterative].

The result uses neither symmetry nor coercivity of $A$, and no finite dimension. The proof uses
that $A x_k \in A \mathcal{K}_k$ while $r_k = b - A x_k$ is orthogonal to $A \mathcal{K}_k$, so
$\|A x_k\|^2 = \|b\|^2 - \|r_k\|^2$, and $\|r_k\|$ is nonincreasing by
`Krylov.IsMinResidualIterate.norm_residual_antitone`. -/
theorem norm_apply_monotone {x : ℕ → E} (hx : ∀ k, IsMinResidualIterate A b 0 k (x k)) :
    Monotone fun k => ‖A (x k)‖ := by
  have key : ∀ k, ‖A (x k)‖ ^ 2 + ‖b - A (x k)‖ ^ 2 = ‖b‖ ^ 2 := by
    intro k
    have hmem : A (x k) ∈ (subspace A (b - A 0) k).map A :=
      Submodule.mem_map_of_mem (by simpa using (hx k).mem)
    have h0 : inner 𝕜 (A (x k)) (b - A (x k)) = (0 : 𝕜) :=
      (Submodule.mem_orthogonal _ _).1 (hx k).residual_mem_orthogonal _ hmem
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [show A (x k) + (b - A (x k)) = b by abel] at h
    nlinarith [h]
  intro i j hij
  have hr : ‖b - A (x j)‖ ≤ ‖b - A (x i)‖ := norm_residual_antitone hx hij
  have hsq : ‖A (x i)‖ ^ 2 ≤ ‖A (x j)‖ ^ 2 := by
    nlinarith [key i, key j, norm_nonneg (b - A (x i)), norm_nonneg (b - A (x j))]
  nlinarith [norm_nonneg (A (x i)), norm_nonneg (A (x j))]

/-- Let $A$ be a symmetric coercive operator on a finite-dimensional inner product space $E$, let
$b \in E$ with $b \neq 0$, and let $\alpha \ge 0$, $\beta > 0$ and $\nu \ge 0$ be real numbers.
If $x_k$ is a minimal-residual iterate at step $k$ for $Ax = b$ from $x_0 = 0$, for every $k$,
then the normwise relative backward error
$$\frac{\|b - A x_k\|}{\alpha \nu \|x_k\| + \beta \|b\|}$$
is nonincreasing in $k$. This is Theorem 3.1 of [fong2012cg].

The number $\nu$ stands for $\|A\|$, but the statement holds for any $\nu \ge 0$. The
denominator is positive at every step, so no division by zero occurs. -/
theorem backwardError_antitone {x : ℕ → E} (hx : ∀ k, IsMinResidualIterate A b 0 k (x k))
    {normA α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) (hnormA : 0 ≤ normA) (hb : b ≠ 0) :
    Antitone fun k => ‖b - A (x k)‖ / (α * normA * ‖x k‖ + β * ‖b‖) := by
  have hmono : Monotone fun k => ‖x k‖ := norm_monotone hA hx
  intro i j hij
  have hden : ∀ k : ℕ, 0 < α * normA * ‖x k‖ + β * ‖b‖ := by
    intro k
    have h1 : 0 ≤ α * normA * ‖x k‖ := by positivity
    have h2 : 0 < β * ‖b‖ := by positivity
    linarith
  rw [div_le_div_iff₀ (hden j) (hden i)]
  refine mul_le_mul (norm_residual_antitone hx hij) ?_ (le_of_lt (hden i)) (norm_nonneg _)
  have hx' : ‖x i‖ ≤ ‖x j‖ := hmono hij
  nlinarith [mul_nonneg hα hnormA]

/-- Let $A$ be a symmetric coercive operator on a finite-dimensional inner product space $E$ and let
$b \in E$ with $b \neq 0$. If $x_k$ is a minimal-residual iterate at step $k$ for $Ax = b$ from
$x_0 = 0$, for every $k$, then $\|b - A x_k\| / \|x_k\|$ is nonincreasing for $k \ge 1$. This is
the case $\beta = 0$ of (3.5) in [fong2012cg].

At $k = 0$ the iterate is $x_0 = 0$, and Lean's convention for division by zero gives the
quotient the value $0$. Therefore the statement is `AntitoneOn` on `Set.Ici 1`. -/
theorem norm_residual_div_norm_antitoneOn {x : ℕ → E}
    (hx : ∀ k, IsMinResidualIterate A b 0 k (x k)) (hb : b ≠ 0) :
    AntitoneOn (fun k => ‖b - A (x k)‖ / ‖x k‖) (Set.Ici 1) := by
  have hmono : Monotone fun k => ‖x k‖ := norm_monotone hA hx
  have h1 : 0 < ‖x 1‖ := by
    rw [norm_pos_iff, eq_CR_iterate hA (hx 1)]
    exact CR.iterate_one_x_ne_zero b hA hb
  intro i hi j hj hij
  simp only [Set.mem_Ici] at hi hj
  have hxi : 0 < ‖x i‖ := lt_of_lt_of_le h1 (hmono hi)
  have hxj : 0 < ‖x j‖ := lt_of_lt_of_le h1 (hmono hj)
  rw [div_le_div_iff₀ hxj hxi]
  exact mul_le_mul (norm_residual_antitone hx hij) (hmono hij) (le_of_lt hxi) (norm_nonneg _)

end Krylov.IsMinResidualIterate

namespace Krylov.IsGalerkinIterate

include hA

omit [FiniteDimensional 𝕜 E] in
/-- Let $A$ be a symmetric coercive operator on an inner product space $E$, and let $b, x_0 \in E$.
If $x$ is a Galerkin iterate at step $k$ for $Ax = b$ from $x_0$, then $x$ is the iterate at
step $k$ of the conjugate gradient method, `(CG.iterate A b x₀ k).x`. -/
theorem eq_CG_iterate {x₀ : E} {k : ℕ} {x : E} (hx : IsGalerkinIterate A b x₀ k x) :
    x = (CG.iterate A b x₀ k).x := by
  obtain ⟨y, -, huniq⟩ := existsUnique_isGalerkinIterate_of_isCoercive hA.isCoercive b x₀ k
  exact (huniq x hx).trans (huniq _ (CG.isGalerkinIterate b x₀ hA k)).symm

omit [FiniteDimensional 𝕜 E] in
/-- Let $A$ be a symmetric coercive operator on an inner product space $E$ and let $b \in E$. If
$x_k$ is a Galerkin iterate at step $k$ for $Ax = b$ from $x_0 = 0$, for every $k$, then
$\|x_k\|$ is nondecreasing in $k$.

This is a result of [steihaug1983conjugate], *The conjugate gradient method and trust regions in
large scale optimization*. It appears as the CG column of Table 5.1 of [fong2012cg]. The
statement does not need finite dimension. -/
theorem norm_monotone {x : ℕ → E} (hx : ∀ k, IsGalerkinIterate A b 0 k (x k)) :
    Monotone fun k => ‖x k‖ := by
  have h : ∀ k, x k = (CG.iterate A b 0 k).x := fun k => eq_CG_iterate hA (hx k)
  simpa only [h] using CG.norm_iterate_monotone b hA

/-- Let $A$ be a symmetric coercive operator on a finite-dimensional inner product space $E$, let
$b, x_0 \in E$, and let $A x^* = b$. If $x_k$ is a Galerkin iterate at step $k$ for $Ax = b$
from $x_0$, for every $k$, then the error $\|x^* - x_k\|$ is nonincreasing in $k$. This is
Theorem 6:3 of [hestenes1952methods], *Methods of conjugate gradients for solving linear
systems*. -/
theorem norm_error_antitone {x₀ : E} {x : ℕ → E} (hx : ∀ k, IsGalerkinIterate A b x₀ k (x k))
    {xstar : E} (hstar : A xstar = b) : Antitone fun k => ‖xstar - x k‖ := by
  have h : ∀ k, x k = (CG.iterate A b x₀ k).x := fun k => eq_CG_iterate hA (hx k)
  simpa only [h] using CG.norm_error_antitone b x₀ hA hstar

end Krylov.IsGalerkinIterate
