/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Conditioning.LinearSystem
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import NumlibSurface.SaadSparse.Chapter01.Basics

/-!
# Saad, Section 1.13: Basic concepts in linear systems

This module formalizes §1.13 of [saad2003iterative]: the three cases for the existence of a solution
of $Ax = b$ in §1.13.1, and the conditioning of a linear system in §1.13.2. For a nonsingular
$A \in \mathbb{K}^{n \times n}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, the condition
number is $\kappa_p(A) = \|A\|_p \|A^{-1}\|_p$. The module proves the first-order perturbation
theory (1.74)–(1.75): the solution $x(\varepsilon) = (A + \varepsilon E)^{-1}(b + \varepsilon e)$
has derivative $A^{-1}(e - Ex)$ at $\varepsilon = 0$. It also proves the relative perturbation bound
(1.76), the bound $\|x - \tilde x\|/\|x\| \le \kappa(A) \|r\|/\|b\|$ of the error by the residual
$r = b - A\tilde x$, and Example 1.5: the matrix $I + \alpha e_i e_j^T$, whose determinant is $1$,
has the condition number $(1 + |\alpha|)^2$, which is arbitrarily large.

The $p$-norm $\|A\|_p$ of (1.7) and the condition number $\kappa_p(A)$ are the backbone's
`Matrix.lpOpNorm` and `Matrix.condNumberLp` of `Numlib.Analysis.Matrix.OperatorNorm`. The
perturbation bounds specialize the backbone module `Numlib.Conditioning.LinearSystem`.

## Main results

* §1.13.1, `Matrix.existsUnique_mulVec_eq`: if $A$ is nonsingular, $Ax = b$ has a unique solution.
* §1.13.1, `Matrix.setOf_mulVec_eq` and `Matrix.infinite_setOf_mulVec_eq`: if
  $b \in \operatorname{Ran}(A)$, the solutions form the coset $x_0 + \operatorname{Null}(A)$, which
  is infinite when $A$ is singular.
* §1.13.1, `Matrix.not_exists_mulVec_eq`: if $b \notin \operatorname{Ran}(A)$, there is no solution.
* §1.13.2, `Matrix.det_smul_one`: $\det(\alpha I) = \alpha^n$, while $\kappa_p(\alpha I) = 1$.
* Equation (1.76), `Matrix.relative_error_le_of_perturbed`: the relative error of the solution of a
  perturbed system is at most $\kappa_p(A)/(1 - \|A^{-1}\|_p \|\Delta A\|_p)$ times the relative
  perturbation of the data.
* Equations (1.74)–(1.75), `Matrix.equation_1_75`: the solution of the perturbed system is
  differentiable in $\varepsilon$ at $0$, with derivative $A^{-1}(e - Ex)$.
* §1.13.2, `Matrix.relative_error_le_condNumberLp`: $\|x - \tilde x\|_p / \|x\|_p \le \kappa_p(A)
  \|b - A\tilde x\|_p / \|b\|_p$.
* Example 1.5, `Matrix.example_1_5`: $A = I + \alpha e_i e_j^T$ with $i \neq j$ has
  $A^{-1} = I - \alpha e_i e_j^T$ and $\kappa_\infty(A) = (1 + |\alpha|)^2$.

## Implementation notes

* §1.13.2 also uses the scaling invariance `Matrix.condNumberLp_smul`, the bound
  `Matrix.one_le_condNumberLp` and the identity $\kappa_p(\alpha I) = 1$,
  `Matrix.condNumberLp_smul_one`, of the backbone.
* The condition number is the backbone's `NormedRing.condNumber` of the operator $x \mapsto Ax$ on
  `PiLp p (fun _ : Fin n => 𝕜)` (`Matrix.condNumberLp_eq_condNumber`). The perturbation bounds are
  `relative_error_le_condNumber`, `relative_error_le_condNumber_mul_relative_residual` and
  `hasDerivAt_perturbed_solution` of `Numlib.Conditioning.LinearSystem`.
* The bridge that carries `hasDerivAt_perturbed_solution` to matrices is `Matrix.ringInverse_lpCLM`:
  the matrix inverse and the ring inverse of the induced operator agree, also at singular matrices,
  where both are $0$, because `Matrix.lpCLM` reflects invertibility (`Matrix.isUnit_lpCLM_iff`).
* Example 1.5 uses the norm $\|\cdot\|_\infty$ of the book, the maximum absolute row sum, which is
  Mathlib's scoped instance `Matrix.Norms.Operator` and not `Matrix.lpOpNorm ⊤`: Mathlib has no
  instance `Fact (1 ≤ ⊤)` for `PiLp ⊤`, and the rest of the formalization of §1.5 uses
  `Matrix.Norms.Operator` for $\|\cdot\|_\infty$.

## Deviations from the source

* **Example 1.5** (generalization). The book takes $i$ to be the first index and $j$ the last. The
  statement holds for any $i \neq j$. See `Matrix.example_1_5`.
-/

open Matrix

open scoped SaadSparse NormedRing ENNReal

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### Existence of a solution (§1.13.1) -/

/-- **Section 1.13.1** of [saad2003iterative], Case 1. Let $A \in \mathbb{K}^{n \times n}$ be
nonsingular. Then for every $b \in \mathbb{K}^n$ the system $Ax = b$ has a unique solution. -/
theorem existsUnique_mulVec_eq (A : Matrix (Fin n) (Fin n) 𝕜) (hA : IsUnit A) (b : Fin n → 𝕜) :
    ∃! x, A *ᵥ x = b := by
  refine ⟨A⁻¹ *ᵥ b, ?_, fun y hy => ?_⟩
  · exact mulVec_nonsing_inv_mulVec hA b
  · exact (nonsing_inv_mulVec_eq hA hy).symm

/-- **Section 1.13.1** of [saad2003iterative], Case 2. Let $A \in \mathbb{K}^{n \times n}$ and
$Ax_0 = b$. Then the set of solutions of $Ax = b$ is the coset
$$\{x : Ax = b\} = x_0 + \operatorname{Null}(A).$$
-/
theorem setOf_mulVec_eq (A : Matrix (Fin n) (Fin n) 𝕜) {b x₀ : Fin n → 𝕜} (hx₀ : A *ᵥ x₀ = b) :
    {x | A *ᵥ x = b} = (fun z => x₀ + z) '' {z | A *ᵥ z = 0} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hx
    exact ⟨x - x₀, by rw [mulVec_sub, hx, hx₀, sub_self], by abel⟩
  · rintro ⟨z, hz, rfl⟩
    rw [mulVec_add, hx₀, hz, add_zero]

/-- **Section 1.13.1** of [saad2003iterative], Case 2. Let $A \in \mathbb{K}^{n \times n}$ be
singular, and let $b = Ax_0$ be in the range of $A$. Then the system $Ax = b$ has infinitely
many solutions. -/
theorem infinite_setOf_mulVec_eq (A : Matrix (Fin n) (Fin n) 𝕜) (hA : ¬ IsUnit A)
    {b x₀ : Fin n → 𝕜} (hx₀ : A *ᵥ x₀ = b) : {x | A *ᵥ x = b}.Infinite := by
  obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp (mulVec_injective_iff_isUnit.not.mpr hA)
  have hker : A *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
  have hne0 : u - v ≠ 0 := sub_ne_zero_of_ne hne
  refine Set.infinite_of_injective_forall_mem (f := fun c : 𝕜 => x₀ + c • (u - v)) ?_ ?_
  · intro c d hcd
    have h : (c - d) • (u - v) = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact add_right_injective x₀ hcd
    rcases smul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne0
  · intro c
    simp only [Set.mem_ofPred_eq, mulVec_add, hx₀, mulVec_smul, hker, smul_zero, add_zero]

/-- **Section 1.13.1** of [saad2003iterative], Case 3. Let $A \in \mathbb{K}^{n \times n}$ and let
$b \in \mathbb{K}^n$ not be in the range of $A$. Then the system $Ax = b$ has no solution. -/
theorem not_exists_mulVec_eq (A : Matrix (Fin n) (Fin n) 𝕜) {b : Fin n → 𝕜}
    (hb : b ∉ Set.range (A *ᵥ ·)) : ¬ ∃ x, A *ᵥ x = b := fun ⟨x, hx⟩ => hb ⟨x, hx⟩

/-! ### The condition number (§1.13.2) -/

section Lp

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **Section 1.13.2** of [saad2003iterative]. For $\alpha \in \mathbb{K}$,
$\det(\alpha I) = \alpha^n$. Since $\kappa_p(\alpha I) = 1$ (`Matrix.condNumberLp_smul_one`),
the determinant gives no indication of the conditioning of a matrix. -/
theorem det_smul_one (c : 𝕜) : (c • (1 : Matrix (Fin n) (Fin n) 𝕜)).det = c ^ n := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin]

/-! ### Perturbation bounds -/

variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- **Equation (1.76)** of [saad2003iterative]. Let $1 \le p \le \infty$, let
$A \in \mathbb{K}^{n \times n}$ be nonsingular, and let $\Delta A \in \mathbb{K}^{n \times n}$
with $\|A^{-1}\|_p \|\Delta A\|_p < 1$. Let $Ax = b$ and $(A + \Delta A) y = b + \Delta b$, with
$x \neq 0$ and $b \neq 0$. Then
$$\frac{\|y - x\|_p}{\|x\|_p} \le \frac{\kappa_p(A)}{1 - \|A^{-1}\|_p \|\Delta A\|_p} \left(
  \frac{\|\Delta A\|_p}{\|A\|_p} + \frac{\|\Delta b\|_p}{\|b\|_p} \right).$$

With $\Delta A = \varepsilon E$ and $\Delta b = \varepsilon e$ this gives the bound $\varepsilon
\kappa(A) (\|e\|/\|b\| + \|E\|/\|A\|) + o(\varepsilon)$ of the book. The vectors are elements of
`PiLp p`, and $Ax$ is `Matrix.lpCLM p A x`. -/
theorem relative_error_le_of_perturbed (hA : IsUnit A) (ΔA : Matrix (Fin n) (Fin n) 𝕜)
    {b Δb x y : PiLp p (fun _ : Fin n => 𝕜)}
    (hx : lpCLM p A x = b) (hy : lpCLM p (A + ΔA) y = b + Δb)
    (hsmall : lpOpNorm p A⁻¹ * lpOpNorm p ΔA < 1) (hx0 : x ≠ 0) (hb : b ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ condNumberLp p A / (1 - lpOpNorm p A⁻¹ * lpOpNorm p ΔA)
      * (lpOpNorm p ΔA / lpOpNorm p A + ‖Δb‖ / ‖b‖) := by
  have hsym : ‖((lpEquiv p hA).symm : PiLp p (fun _ : Fin n => 𝕜) →L[𝕜]
      PiLp p (fun _ : Fin n => 𝕜))‖ = lpOpNorm p A⁻¹ := by
    rw [coe_lpEquiv_symm]
    rfl
  have h := relative_error_le_condNumber (lpEquiv p hA) (lpCLM p ΔA) (b := b) (Δb := Δb)
    (x := x) (y := y) (by rw [← hx]; rfl) (by rw [← hy, lpCLM_add]; rfl)
    (by rw [hsym]; exact hsmall) hx0 hb
  rw [hsym, coe_lpEquiv p hA] at h
  rw [condNumberLp_eq_condNumber p A]
  exact h

/-- **Equations (1.74)–(1.75)** of [saad2003iterative]. Let $1 \le p \le \infty$, let
$A \in \mathbb{K}^{n \times n}$ be nonsingular, and let $E \in \mathbb{K}^{n \times n}$ and
$b, e \in \mathbb{K}^n$. Then the solution
$$x(\varepsilon) = (A + \varepsilon E)^{-1} (b + \varepsilon e)$$
of the perturbed system is differentiable in $\varepsilon \in \mathbb{K}$ at $\varepsilon = 0$,
with derivative
$$x'(0) = A^{-1} (e - E x), \qquad x = A^{-1} b.$$

The proof is `hasDerivAt_perturbed_solution` of `Numlib.Conditioning.LinearSystem`, transported
to matrices by `Matrix.ringInverse_lpCLM`: the matrix inverse of $A + \varepsilon E$ is the ring
inverse of the induced operator, also where it is singular. Since $A$ is nonsingular,
$A + \varepsilon E$ is nonsingular for all small $\varepsilon$, so near $0$ the function is the
solution of the perturbed system. Together with the norm bound
`Matrix.relative_error_le_of_perturbed`, this gives the first-order form (1.76) of the book,
$\|x(\varepsilon) - x\|/\|x\| \le \varepsilon \kappa(A) (\|E\|/\|A\| + \|e\|/\|b\|) +
o(\varepsilon)$. -/
theorem equation_1_75 (hA : IsUnit A) (E : Matrix (Fin n) (Fin n) 𝕜)
    (b e : PiLp p (fun _ : Fin n => 𝕜)) :
    HasDerivAt (fun ε : 𝕜 => lpCLM p ((A + ε • E)⁻¹) (b + ε • e))
      (lpCLM p A⁻¹ (e - lpCLM p E (lpCLM p A⁻¹ b))) 0 := by
  have h := hasDerivAt_perturbed_solution (lpEquiv p hA) (lpCLM p E) b e
  simpa only [coe_lpEquiv p hA, coe_lpEquiv_symm p hA, ← lpCLM_smul, ← lpCLM_add,
    ringInverse_lpCLM] using h

/-- **Section 1.13.2** of [saad2003iterative], the error and the residual. Let $1 \le p \le \infty$,
let $A \in \mathbb{K}^{n \times n}$ be nonsingular, let $Ax = b$ with $b \neq 0$, and let
$\tilde x \in \mathbb{K}^n$. Then, with the residual $r = b - A\tilde x$,
$$\frac{\|x - \tilde x\|_p}{\|x\|_p} \le \kappa_p(A) \frac{\|r\|_p}{\|b\|_p}.$$
-/
theorem relative_error_le_condNumberLp (hA : IsUnit A) {b x : Fin n → 𝕜} (hx : A *ᵥ x = b)
    (hb : (WithLp.toLp p b : PiLp p (fun _ : Fin n => 𝕜)) ≠ 0) (y : Fin n → 𝕜) :
    ‖(WithLp.toLp p (x - y) : PiLp p (fun _ : Fin n => 𝕜))‖ / ‖(WithLp.toLp p x :
        PiLp p (fun _ : Fin n => 𝕜))‖ ≤
      condNumberLp p A *
        (‖(WithLp.toLp p (b - A *ᵥ y) : PiLp p (fun _ : Fin n => 𝕜))‖ /
          ‖(WithLp.toLp p b : PiLp p (fun _ : Fin n => 𝕜))‖) := by
  have hAx : lpEquiv p hA (WithLp.toLp p x) = WithLp.toLp p b := by
    rw [lpEquiv_apply]; congr 1
  have h := relative_error_le_condNumber_mul_relative_residual (lpEquiv p hA) hAx hb
    (y := WithLp.toLp p y)
  rw [condNumberLp_eq_condNumber p A, ← coe_lpEquiv p hA]
  exact h

end Lp

/-! ### Example 1.5 -/

section Example

variable {i j : Fin n}

/-- If $T^2 = 0$, then $(I + T)^{-1} = I - T$: the first two terms of the Neumann series invert
$I + T$. -/
private theorem inv_one_add_of_mul_self_eq_zero {T : Matrix (Fin n) (Fin n) 𝕜} (hT : T * T = 0) :
    (1 + T)⁻¹ = 1 - T := by
  refine inv_eq_right_inv ?_
  have h : (1 + T) * (1 - T) = 1 - T * T := by noncomm_ring
  rw [h, hT, sub_zero]

/-- For $i \neq j$, the rank-one matrix $e_i e_j^T$ of Example 1.5 satisfies $(e_i e_j^T)^2 = 0$. -/
private theorem single_mul_self_eq_zero (hij : i ≠ j) :
    (single i j (1 : 𝕜) : Matrix (Fin n) (Fin n) 𝕜) * single i j 1 = 0 := by
  ext a b
  simp only [Matrix.mul_apply, single_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : j = l
  · subst hl; simp [hij]
  · simp [hl]

open scoped Matrix.Norms.Operator in
/-- For $i \neq j$ and $\alpha \in \mathbb{K}$, $\|I + \alpha e_i e_j^T\|_\infty = 1 + |\alpha|$:
row $i$ has the two entries $1$ and $\alpha$, and every other row has the single entry $1$. -/
private theorem linfty_opNorm_one_add_smul_single (hij : i ≠ j) (α : 𝕜) :
    ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜)‖ = 1 + ‖α‖ := by
  have hii : (1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) i i = 1 := by
    simp [hij.symm]
  have hij' : (1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) i j = α := by
    simp [hij]
  have hrowi : (∑ l, ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) i l‖₊) = 1 + ‖α‖₊ := by
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n))) fun l _ hl => ?_,
      Finset.sum_pair hij, hii, hij']
    · simp
    · have hli : i ≠ l := fun h => hl (by simp [← h])
      have hlj : j ≠ l := fun h => hl (by simp [← h])
      simp [hli, hlj]
  have hrowk : ∀ k, k ≠ i →
      (∑ l, ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) k l‖₊) = 1 := by
    intro k hk
    rw [Finset.sum_eq_single k (fun l _ hl => ?_) fun h => absurd (Finset.mem_univ k) h]
    · simp [Ne.symm hk]
    · simp [Ne.symm hl, Ne.symm hk]
  have hsup : (Finset.univ.sup fun k =>
      ∑ l, ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) k l‖₊) = 1 + ‖α‖₊ := by
    refine le_antisymm (Finset.sup_le fun k _ => ?_) ?_
    · by_cases hk : k = i
      · subst hk; exact hrowi.le
      · rw [hrowk k hk]; exact le_self_add
    · rw [← hrowi]
      exact Finset.le_sup
        (f := fun k => ∑ l, ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) k l‖₊)
        (Finset.mem_univ i)
  rw [linfty_opNorm_def, hsup]
  simp

open scoped Matrix.Norms.Operator in
/-- **Example 1.5** of [saad2003iterative]. Let $i \neq j$, let $\alpha \in \mathbb{K}$, and let
$A = I + \alpha e_i e_j^T \in \mathbb{K}^{n \times n}$. Then
$$A^{-1} = I - \alpha e_i e_j^T, \qquad \|A\|_\infty = \|A^{-1}\|_\infty = 1 + |\alpha|, \qquad
  \kappa_\infty(A) = \|A\|_\infty \|A^{-1}\|_\infty = (1 + |\alpha|)^2.$$

**Generalization.** The book takes $i$ to be the first index and $j$ the last. The statement
holds for any $i \neq j$.

The point of the example in the book is that the condition number grows without bound as
$|\alpha| \to \infty$, although $\det A = 1$; the determinant is not part of the statement. The
norm is the norm $\|\cdot\|_\infty$ of the book, the maximum absolute row sum, which is
Mathlib's scoped instance `Matrix.Norms.Operator`, as in the rest of §1.5. The matrix
$e_i e_j^T$ is `Matrix.single i j 1`. The inverse is the first two terms of the Neumann series,
which is exact because $(e_i e_j^T)^2 = 0$. -/
theorem example_1_5 (hij : i ≠ j) (α : 𝕜) {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A = 1 + α • single i j 1) :
    A⁻¹ = 1 - α • single i j 1 ∧ ‖A‖ = 1 + ‖α‖ ∧ ‖A⁻¹‖ = 1 + ‖α‖ ∧
      ‖A‖ * ‖A⁻¹‖ = (1 + ‖α‖) ^ 2 := by
  have hSS : (α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) * (α • single i j 1) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, single_mul_self_eq_zero hij, smul_zero, smul_zero]
  have hinv : A⁻¹ = 1 - α • single i j 1 := by
    rw [hA]; exact inv_one_add_of_mul_self_eq_zero hSS
  have h1 : ‖A‖ = 1 + ‖α‖ := by rw [hA]; exact linfty_opNorm_one_add_smul_single hij α
  have h2 : ‖A⁻¹‖ = 1 + ‖α‖ := by
    rw [hinv, show (1 : Matrix (Fin n) (Fin n) 𝕜) - α • single i j 1
        = 1 + (-α) • single i j 1 by rw [neg_smul, ← sub_eq_add_neg],
      linfty_opNorm_one_add_smul_single hij (-α), norm_neg]
  exact ⟨hinv, h1, h2, by rw [h1, h2]; ring⟩

end Example

end Matrix
