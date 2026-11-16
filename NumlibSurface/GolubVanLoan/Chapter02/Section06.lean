/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Conditioning.LinearSystem
import Numlib.Conditioning.LinearSystem.Componentwise
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import NumlibSurface.GolubVanLoan.Chapter02.Section03
import NumlibSurface.GolubVanLoan.Chapter02.Section04

/-!
# Golub and Van Loan, Section 2.6: The sensitivity of square systems

This module formalizes §2.6 of [golub2013matrix] on the sensitivity of the solution of $Ax = b$, for
nonsingular $A \in \mathbb{R}^{n \times n}$, to perturbations of $A$ and $b$. It proves the SVD
expansion $x = \sum_i (u_i^T b / \sigma_i) v_i$ (2.6.1), the derivative of the solution
$x(\epsilon)$ of $(A + \epsilon F) x(\epsilon) = b + \epsilon f$, and the bounds (2.6.2) and (2.6.4)
on $\|x(\epsilon) - x\| / \|x\|$. The condition number is $\kappa(A) = \|A\| \|A^{-1}\|$ (2.6.3).
The module proves its characterizations (2.6.5)–(2.6.8): $\kappa_2 = \sigma_{\max}/\sigma_{\min}$,
$1/\kappa$ is the relative distance to the singular matrices, $\kappa$ is a normalized derivative of
$A \mapsto A^{-1}$, and condition numbers in different norms are equivalent. It also proves
$\kappa \ge 1$ and gives the examples (2.6.9) and $D_n$, which show that the determinant does not
measure conditioning. The rigorous normwise bounds are Lemma 2.6.1 and Theorem 2.6.2 with (2.6.11).
The componentwise bound is Theorem 2.6.3, with the Skeel condition number
$\| |A^{-1}| |A| \|_\infty$, and the module ends with the Oettli–Prager theorem (2.6.13).

The proofs specialize the backbone modules `Numlib.Conditioning.LinearSystem` and
`Numlib.Conditioning.LinearSystem.Componentwise` (the Skeel condition number and the Oettli–Prager
theorem), `Numlib.Analysis.Matrix.OperatorNorm` (`Matrix.condNumberLp`, `Matrix.lpEquiv`) and
`Numlib.LinearAlgebra.Matrix.SVD`.

## Main definitions

* Equation (2.6.3), `GolubVanLoan.Chapter02.kappa`: the condition number
  $\kappa_p(A) = \|A\|_p \|A^{-1}\|_p$, with $\kappa_p(A) = \infty$ for singular $A$.

## Main results

* Equation (2.6.1), `GolubVanLoan.Chapter02.equation_2_6_1`:
  $A^{-1} b = \sum_i (u_i^T b / \sigma_i) v_i$ for an SVD of $A$.
* §2.6.2, `GolubVanLoan.Chapter02.perturbed_solution_hasDerivAt`: $\dot x(0) = A^{-1}(f - Fx)$.
* Equation (2.6.2), `GolubVanLoan.Chapter02.equation_2_6_2`: a bound on
  $\|x(\epsilon) - x\|_p / \|x\|_p$ in terms of $\|A^{-1}\|_p$, $\|f\|_p$ and $\|F\|_p$.
* `GolubVanLoan.Chapter02.kappa_of_isUnit` and `GolubVanLoan.Chapter02.kappa_of_not_isUnit`: the
  value of $\kappa_p(A)$ for nonsingular and for singular $A$.
* Equation (2.6.4), `GolubVanLoan.Chapter02.equation_2_6_4`: the relative error of $x(\epsilon)$ is
  at most $\kappa_p(A)(\rho_A + \rho_b)$ up to a factor $1 + O(\epsilon)$.
* Equation (2.6.5), `GolubVanLoan.Chapter02.equation_2_6_5`: $\kappa_2(A) = \sigma_{\max}(A) /
  \sigma_{\min}(A)$.
* Equation (2.6.6), `GolubVanLoan.Chapter02.equation_2_6_6`: $1/\kappa_p(A)$ is the least relative
  distance $\|\Delta A\|_p / \|A\|_p$ to a singular matrix $A + \Delta A$.
* Equation (2.6.7), `GolubVanLoan.Chapter02.equation_2_6_7`: $\kappa_p(A)$ is a normalized
  derivative of $A \mapsto A^{-1}$.
* Equation (2.6.8), `GolubVanLoan.Chapter02.equation_2_6_8`: the equivalence of $\kappa_1$,
  $\kappa_2$ and $\kappa_\infty$ up to factors $n$ and $n^2$.
* §2.6.2, `GolubVanLoan.Chapter02.one_le_kappa`: $\kappa_p(A) \ge 1$.
* §2.6.2, `GolubVanLoan.Chapter02.kappa_two_eq_one_of_mem_orthogonalGroup`: $\kappa_2(Q) = 1$ for
  orthogonal $Q$.
* Equation (2.6.9), `GolubVanLoan.Chapter02.equation_2_6_9`: the matrix $B_n$ has $\det(B_n) = 1$
  and $\kappa_\infty(B_n) = n 2^{n-1}$.
* §2.6.3, `GolubVanLoan.Chapter02.condNumberLp_diag_tenth`: $D_n = \operatorname{diag}(10^{-1},
  \dots, 10^{-1})$ has $\kappa_p(D_n) = 1$ and $\det(D_n) = 10^{-n}$.
* Lemma 2.6.1, `GolubVanLoan.Chapter02.lemma_2_6_1`: $A + \Delta A$ is nonsingular and
  $\|y\|_p / \|x\|_p \le (1 + r)/(1 - r)$.
* Equation (2.6.11), `GolubVanLoan.Chapter02.equation_2_6_11`:
  $y - x = A^{-1} \Delta b - A^{-1} \Delta A \, y$.
* Theorem 2.6.2 with (2.6.10), `GolubVanLoan.Chapter02.theorem_2_6_2`: $\|y - x\|_p / \|x\|_p \le
  2\epsilon \kappa_p(A) / (1 - r)$.
* §2.6.5, `GolubVanLoan.Chapter02.skeelCond_eq_and_le_condNumberLp`: the Skeel condition number is
  at most $\kappa_\infty(A)$.
* Theorem 2.6.3 with (2.6.12), `GolubVanLoan.Chapter02.theorem_2_6_3`: the componentwise bound
  $\|y - x\|_\infty / \|x\|_\infty \le 2\epsilon \| |A^{-1}| |A| \|_\infty / (1 - r)$.
* Equation (2.6.13), `GolubVanLoan.Chapter02.equation_2_6_13`: the Oettli–Prager theorem on the
  componentwise backward error.

## Conventions

* Norms are the $p$-norms for `p : ℝ≥0∞` with `[Fact (1 ≤ p)]`: $\|x\|_p$ is `‖WithLp.toLp p x‖` and
  $\|A\|_p$ is `Matrix.lpOpNorm p A`. The phrase "any vector norm and consistent matrix norm" of the
  source is the operator statement of the backbone module `Numlib.Conditioning.LinearSystem` on any
  normed space, which this module applies to `PiLp p` through `Matrix.lpCLM` and `Matrix.lpEquiv`.
* The condition number $\kappa_p(A) = \|A\|_p \|A^{-1}\|_p$ is the real number
  `Matrix.condNumberLp p A`, used under an explicit hypothesis `IsUnit A`; it is $0$ for singular
  $A$. The convention $\kappa(A) = \infty$ of the source for singular $A$ is the definition
  `GolubVanLoan.Chapter02.kappa`.
* The source states (2.6.2) and (2.6.4) with a term $O(\epsilon^2)$. The theorems state rigorous
  bounds with the factor $1/(1 - |\epsilon| \|A^{-1}\| \|F\|) = 1 + O(\epsilon)$, which gives the
  $O(\epsilon^2)$ term.
* $\sigma_{\max}(A)$ and $\sigma_{\min}(A)$ in (2.6.5) are `GolubVanLoan.Chapter02.sigmaMax` and
  `GolubVanLoan.Chapter02.sigmaMin` of §2.4. The SVD $A = U \Sigma V^T$ in (2.6.1) is given by its
  three factors.

## Deviations from the source

* **Lemma 2.6.1** (reading). The source carries the nonsingularity of $A$ through the convention
  $\kappa(A) = \infty$. The lemma has the explicit hypothesis that $A$ is nonsingular. See
  `GolubVanLoan.Chapter02.lemma_2_6_1`.
* **Theorem 2.6.3** (typo). The source prints the hypothesis as $\delta \kappa_\infty(A) = r < 1$,
  with $\delta$ for $\epsilon$. See `GolubVanLoan.Chapter02.theorem_2_6_3`.

## Not formalized

* **The $2 \times 2$ example after Theorem 2.6.2**, which shows that the bound can be attained or
  not. It is a numerical example.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal

namespace GolubVanLoan.Chapter02

variable {n : ℕ}

/-! ### Matrices as operators on `PiLp p` -/

/-- For nonsingular $A \in \mathbb{R}^{n \times n}$, the condition number of the operator
`Matrix.lpEquiv p hA` on `PiLp p` is $\kappa_p(A)$. -/
private theorem condNumber_coe_lpEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) :
    NormedRing.condNumber
        (lpEquiv p hA : PiLp p (fun _ : Fin n => ℝ) →L[ℝ] PiLp p (fun _ : Fin n => ℝ)) =
      condNumberLp p A := by
  rw [coe_lpEquiv, condNumberLp_eq_condNumber]

/-- If $A$ is nonsingular, $\|\Delta A\|_p \le \epsilon \|A\|_p$ and $\epsilon \kappa_p(A) < 1$,
then $A + \Delta A$ is nonsingular, by Theorem 2.3.4 and
$\|A^{-1} \Delta A\|_p \le \epsilon \kappa_p(A)$. -/
private theorem isUnit_add_of_lpOpNorm_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {A ΔA : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {ε : ℝ}
    (hΔA : lpOpNorm p ΔA ≤ ε * lpOpNorm p A) (hr : ε * condNumberLp p A < 1) :
    IsUnit (A + ΔA) := by
  refine (theorem_2_3_4 p hA (lt_of_le_of_lt ?_ hr)).1
  calc lpOpNorm p (A⁻¹ * ΔA) ≤ lpOpNorm p A⁻¹ * lpOpNorm p ΔA := lpOpNorm_mul_le p _ _
    _ ≤ lpOpNorm p A⁻¹ * (ε * lpOpNorm p A) :=
        mul_le_mul_of_nonneg_left hΔA (lpOpNorm_nonneg _ _)
    _ = ε * condNumberLp p A := by rw [condNumberLp]; ring

/-! ### §2.6.1 An SVD analysis -/

/-- **Equation (2.6.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular,
and let $U, V \in \mathbb{R}^{n \times n}$ be orthogonal with $U^T A V =
\operatorname{diag}(\sigma_1, \dots, \sigma_n)$. Then for every $b \in \mathbb{R}^n$,
$$x = A^{-1} b = \sum_{i=1}^n \frac{u_i^T b}{\sigma_i} v_i.$$

The vectors $u_i$ and $v_i$ are the columns `U.col i` and `V.col i`. The theorem does not
require the $\sigma_i$ to be sorted or nonnegative. -/
theorem equation_2_6_1 {A U V : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hU : U ∈ orthogonalGroup (Fin n) ℝ) (hV : V ∈ orthogonalGroup (Fin n) ℝ) {σ : ℕ → ℝ}
    (h : Uᵀ * A * V = diagonal fun i : Fin n => σ i) (b : Fin n → ℝ) :
    A⁻¹ *ᵥ b = ∑ i : Fin n, ((U.col i ⬝ᵥ b) / σ i) • V.col i := by
  have h' : star U * A * V = rectDiagonal σ := by
    rw [rectDiagonal_eq_diagonal, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, h]
  rw [← pinv_eq_inv hA, pinv_eq_of_svd hU hV h', rectDiagonal_eq_diagonal, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, ← mulVec_mulVec, ← mulVec_mulVec]
  ext k
  simp only [mulVec, dotProduct, diagonal_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    col_apply, transpose_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_inv_mul]
  ring

/-! ### §2.6.2 Condition -/

/-- **Section 2.6.2** of [golub2013matrix], the derivative of the perturbed solution. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $F \in \mathbb{R}^{n \times n}$ and
$b, f \in \mathbb{R}^n$, and let $x(\epsilon) = (A + \epsilon F)^{-1}(b + \epsilon f)$ be the
solution of $(A + \epsilon F) x(\epsilon) = b + \epsilon f$. Then $x(\epsilon)$ is
differentiable at $\epsilon = 0$ and
$$\dot x(0) = A^{-1}(f - Fx), \qquad x = A^{-1} b.$$

The inverse is the matrix inverse of Mathlib, which is $0$ at a singular matrix;
$A + \epsilon F$ is nonsingular for small $|\epsilon|$. -/
theorem perturbed_solution_hasDerivAt {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (F : Matrix (Fin n) (Fin n) ℝ) (b f : Fin n → ℝ) :
    HasDerivAt (fun ε : ℝ => (A + ε • F)⁻¹ *ᵥ (b + ε • f)) (A⁻¹ *ᵥ (f - F *ᵥ (A⁻¹ *ᵥ b))) 0 := by
  have h := hasDerivAt_perturbed_solution (lpEquiv 2 hA) (lpCLM 2 F) (WithLp.toLp 2 b)
    (WithLp.toLp 2 f)
  rw [coe_lpEquiv, coe_lpEquiv_symm] at h
  have key : ∀ ε : ℝ,
      (Ring.inverse (lpCLM 2 A + ε • lpCLM 2 F)) (WithLp.toLp 2 b + ε • WithLp.toLp 2 f)
      = WithLp.toLp 2 ((A + ε • F)⁻¹ *ᵥ (b + ε • f)) := fun ε => by
    rw [← lpCLM_smul, ← lpCLM_add, ringInverse_lpCLM, lpCLM_apply, ← WithLp.toLp_smul,
      ← WithLp.toLp_add, WithLp.ofLp_toLp]
  simp_rw [key] at h
  exact (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 _).comp_hasDerivAt 0 h

/-- **Equation (2.6.2)** of [golub2013matrix], in rigorous form. Let $1 \le p \le \infty$, let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $F \in \mathbb{R}^{n \times n}$ and
$b, f \in \mathbb{R}^n$, and let $x \neq 0$ solve $Ax = b$. If
$|\epsilon| \|A^{-1}\|_p \|F\|_p < 1$, then $x(\epsilon) = (A + \epsilon F)^{-1}(b + \epsilon
f)$ satisfies
$$\frac{\|x(\epsilon) - x\|_p}{\|x\|_p} \le \frac{|\epsilon| \|A^{-1}\|_p}{1 - |\epsilon|
  \|A^{-1}\|_p \|F\|_p} \Big( \frac{\|f\|_p}{\|x\|_p} + \|F\|_p \Big).$$

The source states the first-order bound $|\epsilon| \|A^{-1}\| (\|f\|/\|x\| + \|F\|) +
O(\epsilon^2)$. The term $O(\epsilon^2)$ comes from the factor $1/(1 - |\epsilon| \|A^{-1}\|
\|F\|) = 1 + O(\epsilon)$. -/
theorem equation_2_6_2 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A F : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    {b f x : Fin n → ℝ} (hx : A *ᵥ x = b) (hx0 : x ≠ 0) {ε : ℝ}
    (hε : |ε| * lpOpNorm p A⁻¹ * lpOpNorm p F < 1) :
    ‖WithLp.toLp p ((A + ε • F)⁻¹ *ᵥ (b + ε • f) - x)‖ / ‖WithLp.toLp p x‖ ≤
      |ε| * lpOpNorm p A⁻¹ * (‖WithLp.toLp p f‖ / ‖WithLp.toLp p x‖ + lpOpNorm p F) /
        (1 - |ε| * lpOpNorm p A⁻¹ * lpOpNorm p F) := by
  have hsmall : lpOpNorm p A⁻¹ * lpOpNorm p (ε • F) < 1 := by
    rw [lpOpNorm_smul, Real.norm_eq_abs]; linarith
  have hunit : IsUnit (A + ε • F) := by
    refine (theorem_2_3_4 p hA (lt_of_le_of_lt (lpOpNorm_mul_le p _ _) hsmall)).1
  have h := relative_error_le_norm_inverse (lpEquiv p hA) (lpCLM p (ε • F))
    (b := WithLp.toLp p b) (Δb := WithLp.toLp p (ε • f)) (x := WithLp.toLp p x)
    (y := WithLp.toLp p ((A + ε • F)⁻¹ *ᵥ (b + ε • f)))
    (by simp [hx]) (by
      rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, WithLp.ofLp_toLp,
        mulVec_nonsing_inv_mulVec hunit, WithLp.toLp_add])
    (by rw [coe_lpEquiv_symm]; exact hsmall) (by simpa using hx0)
  rw [coe_lpEquiv_symm, ← WithLp.toLp_sub] at h
  change _ ≤ lpOpNorm p A⁻¹ / (1 - lpOpNorm p A⁻¹ * lpOpNorm p (ε • F)) *
    (‖WithLp.toLp p (ε • f)‖ / ‖WithLp.toLp p x‖ + lpOpNorm p (ε • F)) at h
  rw [lpOpNorm_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] at h
  refine h.trans_eq ?_
  rw [div_mul_eq_mul_div, mul_div_assoc]
  ring_nf

open Classical in
/-- **Equation (2.6.3)** of [golub2013matrix], the condition number. Let $1 \le p \le \infty$. For
$A \in \mathbb{R}^{n \times n}$, the **condition number** is
$$\kappa_p(A) = \|A\|_p \|A^{-1}\|_p$$
if $A$ is nonsingular, and $\kappa_p(A) = \infty$ if $A$ is singular.

The value is in `ℝ≥0∞`: it is `ENNReal.ofReal (Matrix.condNumberLp p A)` for nonsingular $A$ and
`⊤` otherwise. -/
noncomputable def kappa (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  if IsUnit A then ENNReal.ofReal (condNumberLp p A) else ⊤

/-- For nonsingular $A \in \mathbb{R}^{n \times n}$, `GolubVanLoan.Chapter02.kappa p A` is the real
condition number $\kappa_p(A) = \|A\|_p \|A^{-1}\|_p$ of the backbone,
`Matrix.condNumberLp p A`. -/
theorem kappa_of_isUnit (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) : kappa p A = ENNReal.ofReal (condNumberLp p A) :=
  ite_eq_left hA

/-- For singular $A \in \mathbb{R}^{n \times n}$, $\kappa_p(A) = \infty$. -/
theorem kappa_of_not_isUnit (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ¬ IsUnit A) : kappa p A = ⊤ :=
  ite_eq_right hA

/-- **Equation (2.6.4)** of [golub2013matrix], in rigorous form. Let $1 \le p \le \infty$, let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $F \in \mathbb{R}^{n \times n}$ and
$b, f \in \mathbb{R}^n$ with $b \neq 0$, and let $x \neq 0$ solve $Ax = b$. If
$|\epsilon| \|A^{-1}\|_p \|F\|_p < 1$, then $x(\epsilon) = (A + \epsilon F)^{-1}(b + \epsilon
f)$ satisfies
$$\frac{\|x(\epsilon) - x\|_p}{\|x\|_p} \le \frac{\kappa_p(A)}{1 - |\epsilon| \|A^{-1}\|_p
  \|F\|_p} (\rho_A + \rho_b),$$
where $\rho_A = |\epsilon| \|F\|_p / \|A\|_p$ and $\rho_b = |\epsilon| \|f\|_p / \|b\|_p$ are
the relative errors in $A$ and $b$.

The source states the first-order bound $\kappa(A)(\rho_A + \rho_b) + O(\epsilon^2)$. The
condition number is `Matrix.condNumberLp p A`. -/
theorem equation_2_6_4 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A F : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    {b f x : Fin n → ℝ} (hx : A *ᵥ x = b) (hx0 : x ≠ 0) (hb : b ≠ 0) {ε : ℝ}
    (hε : |ε| * lpOpNorm p A⁻¹ * lpOpNorm p F < 1) :
    ‖WithLp.toLp p ((A + ε • F)⁻¹ *ᵥ (b + ε • f) - x)‖ / ‖WithLp.toLp p x‖ ≤
      condNumberLp p A / (1 - |ε| * lpOpNorm p A⁻¹ * lpOpNorm p F) *
        (|ε| * lpOpNorm p F / lpOpNorm p A + |ε| * ‖WithLp.toLp p f‖ / ‖WithLp.toLp p b‖) := by
  have hsmall : lpOpNorm p A⁻¹ * lpOpNorm p (ε • F) < 1 := by
    rw [lpOpNorm_smul, Real.norm_eq_abs]; linarith
  have hunit : IsUnit (A + ε • F) :=
    (theorem_2_3_4 p hA (lt_of_le_of_lt (lpOpNorm_mul_le p _ _) hsmall)).1
  have h := relative_error_le_condNumber (lpEquiv p hA) (lpCLM p (ε • F))
    (b := WithLp.toLp p b) (Δb := WithLp.toLp p (ε • f)) (x := WithLp.toLp p x)
    (y := WithLp.toLp p ((A + ε • F)⁻¹ *ᵥ (b + ε • f)))
    (by simp [hx]) (by
      rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, WithLp.ofLp_toLp,
        mulVec_nonsing_inv_mulVec hunit, WithLp.toLp_add])
    (by rw [coe_lpEquiv_symm]; exact hsmall) (by simpa using hx0) (by simpa using hb)
  rw [condNumber_coe_lpEquiv, coe_lpEquiv_symm, ← WithLp.toLp_sub, coe_lpEquiv] at h
  change _ ≤ condNumberLp p A / (1 - lpOpNorm p A⁻¹ * lpOpNorm p (ε • F)) *
    (lpOpNorm p (ε • F) / lpOpNorm p A + ‖WithLp.toLp p (ε • f)‖ / ‖WithLp.toLp p b‖) at h
  rw [lpOpNorm_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] at h
  refine h.trans_eq ?_
  ring_nf

section L2

open scoped Matrix.Norms.L2Operator

/-- **Equation (2.6.5)** of [golub2013matrix]. For nonsingular $A \in \mathbb{R}^{n \times n}$,
$$\kappa_2(A) = \|A\|_2 \|A^{-1}\|_2 = \frac{\sigma_{\max}(A)}{\sigma_{\min}(A)}.$$
-/
theorem equation_2_6_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    condNumberLp 2 A = lpOpNorm 2 A * lpOpNorm 2 A⁻¹ ∧
      condNumberLp 2 A = sigmaMax A / sigmaMin A := by
  refine ⟨rfl, ?_⟩
  rw [sigmaMax_eq_iSup_colSingularValues, sigmaMin_eq_iInf_colSingularValues A le_rfl]
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [Subsingleton.elim A 0]
    simp [condNumberLp]
  · have h := condNumber_l2_eq_div_colSingularValues A ((isUnit_iff_isUnit_det A).1 hA)
    rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse] at h
    rw [condNumberLp, lpOpNorm_two, lpOpNorm_two]
    exact h

end L2

/-- **Equation (2.6.6)** of [golub2013matrix], a result of Kahan. Let $1 \le p \le \infty$, and let
$A \in \mathbb{R}^{n \times n}$ be nonsingular with $n \ge 1$. Then
$$\frac{1}{\kappa_p(A)} = \min_{A + \Delta A \text{ singular}} \frac{\|\Delta A\|_p}{\|A\|_p}.$$
So $\kappa_p(A)$ measures the relative distance from $A$ to the set of singular matrices.

The minimum is an `IsLeast` statement: the value $1/\kappa_p(A)$ is attained by some $\Delta A$,
and no singular $A + \Delta A$ is closer. -/
theorem equation_2_6_6 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hn : 0 < n) :
    IsLeast {r : ℝ | ∃ ΔA : Matrix (Fin n) (Fin n) ℝ, ¬ IsUnit (A + ΔA) ∧
      lpOpNorm p ΔA / lpOpNorm p A = r} (1 / condNumberLp p A) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial (PiLp p fun _ : Fin n => ℝ) := (WithLp.equiv p (Fin n → ℝ)).nontrivial
  have h := (lpEquiv p hA).isLeast_dist_singular
  rw [condNumber_lpEquiv, coe_lpEquiv] at h
  convert h using 1
  ext r
  constructor
  · rintro ⟨ΔA, hs, rfl⟩
    exact ⟨lpCLM p ΔA, by rwa [← lpCLM_add, isUnit_lpCLM_iff], rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨ΔA, rfl⟩ := (lpCLMEquiv (𝕜 := ℝ) (m := Fin n) (n := Fin n) p).surjective t
    rw [lpCLMEquiv_apply, ← lpCLM_add, isUnit_lpCLM_iff] at ht
    exact ⟨ΔA, ht, rfl⟩

/-- **Equation (2.6.7)** of [golub2013matrix]: the condition number is a normalized Fréchet
derivative of the map $A \mapsto A^{-1}$. Let $1 \le p \le \infty$, and let
$A \in \mathbb{R}^{n \times n}$ be nonsingular with $n \ge 1$. Then
$$\kappa_p(A) = \lim_{\epsilon \to 0^+} \sup_{\|\Delta A\|_p \le \epsilon \|A\|_p} \frac{\|(A +
  \Delta A)^{-1} - A^{-1}\|_p}{\epsilon \|A^{-1}\|_p}.$$

The supremum is the real supremum `iSup`, and $(A + \Delta A)^{-1}$ is the inverse of Mathlib,
which is $0$ at a singular matrix. -/
theorem equation_2_6_7 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hn : 0 < n) :
    Tendsto (fun ε : ℝ => (⨆ ΔA : {ΔA : Matrix (Fin n) (Fin n) ℝ //
        lpOpNorm p ΔA ≤ ε * lpOpNorm p A}, lpOpNorm p ((A + ΔA.1)⁻¹ - A⁻¹)) /
          (ε * lpOpNorm p A⁻¹)) (𝓝[>] 0) (𝓝 (condNumberLp p A)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial (PiLp p fun _ : Fin n => ℝ) := (WithLp.equiv p (Fin n → ℝ)).nontrivial
  have h := (lpEquiv p hA).tendsto_iSup_norm_inverse_add_sub_div
  rw [condNumber_lpEquiv, coe_lpEquiv, coe_lpEquiv_symm] at h
  refine h.congr fun ε => ?_
  congr 1
  let e : {ΔA : Matrix (Fin n) (Fin n) ℝ // lpOpNorm p ΔA ≤ ε * lpOpNorm p A} ≃
      {T : PiLp p (fun _ : Fin n => ℝ) →L[ℝ] PiLp p (fun _ : Fin n => ℝ) //
        ‖T‖ ≤ ε * ‖lpCLM p A‖} :=
    (lpCLMEquiv p).toEquiv.subtypeEquiv fun _ => Iff.rfl
  refine (Equiv.iSup_congr e fun ΔA => ?_).symm
  change ‖Ring.inverse (lpCLM p A + lpCLM p ΔA.1) - lpCLM p A⁻¹‖ = _
  rw [← lpCLM_add, ringInverse_lpCLM, ← lpCLM_sub]
  rfl

/-- **Equation (2.6.8)** of [golub2013matrix]: any two of the condition numbers $\kappa_1$,
$\kappa_2$ and $\kappa_\infty$ are equivalent. For $A \in \mathbb{R}^{n \times n}$,
$$\frac{1}{n} \kappa_2(A) \le \kappa_1(A) \le n \kappa_2(A), \qquad \frac{1}{n} \kappa_\infty(A)
  \le \kappa_2(A) \le n \kappa_\infty(A), \qquad \frac{1}{n^2} \kappa_1(A) \le \kappa_\infty(A)
  \le n^2 \kappa_1(A).$$

The condition numbers are `Matrix.condNumberLp`, which is $0$ at a singular matrix, so the
inequalities hold for every $A$. For $n = 0$ the Lean value of $1/n$ is $0$. -/
theorem equation_2_6_8 (A : Matrix (Fin n) (Fin n) ℝ) :
    1 / (n : ℝ) * condNumberLp 2 A ≤ condNumberLp 1 A ∧ condNumberLp 1 A ≤ n * condNumberLp 2 A ∧
      1 / (n : ℝ) * condNumberLp ∞ A ≤ condNumberLp 2 A ∧
      condNumberLp 2 A ≤ n * condNumberLp ∞ A ∧
      1 / (n : ℝ) ^ 2 * condNumberLp 1 A ≤ condNumberLp ∞ A ∧
      condNumberLp ∞ A ≤ (n : ℝ) ^ 2 * condNumberLp 1 A := by
  have hnn : ∀ q : ℝ≥0∞, [Fact (1 ≤ q)] → 0 ≤ condNumberLp q A := fun q _ =>
    mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  obtain ⟨h12, h21⟩ := condNumberLp_le_card_rpow_mul_condNumberLp (p := 1) (q := 2)
    (by norm_num) A
  obtain ⟨h2t, ht2⟩ := condNumberLp_le_card_rpow_mul_condNumberLp (p := 2) (q := ∞) le_top A
  obtain ⟨h1t, ht1⟩ := condNumberLp_le_card_rpow_mul_condNumberLp (p := 1) (q := ∞) le_top A
  norm_num at h12 h21 h2t ht2 h1t ht1
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  refine ⟨?_, h12, ?_, h2t, ?_, ht1⟩
  · rw [one_div_mul_eq_div]
    exact div_le_of_le_mul₀ hn0 (hnn 1) (h21.trans_eq (mul_comm _ _))
  · rw [one_div_mul_eq_div]
    exact div_le_of_le_mul₀ hn0 (hnn 2) (ht2.trans_eq (mul_comm _ _))
  · rw [one_div_mul_eq_div]
    exact div_le_of_le_mul₀ (by positivity) (hnn ∞) (h1t.trans_eq (mul_comm _ _))

section L2

open scoped Matrix.Norms.L2Operator

/-- **Section 2.6.2** of [golub2013matrix]. Let $1 \le p \le \infty$ and $n \ge 1$. For every
$A \in \mathbb{R}^{n \times n}$, $\kappa_p(A) \ge 1$.

For singular $A$ this holds because $\kappa_p(A) = \infty$. -/
theorem one_le_kappa (p : ℝ≥0∞) [Fact (1 ≤ p)] (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    1 ≤ kappa p A := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  by_cases hA : IsUnit A
  · rw [kappa_of_isUnit p hA]
    exact ENNReal.one_le_ofReal.2 (one_le_condNumberLp p hA)
  · rw [kappa_of_not_isUnit p hA]
    exact le_top

/-- **Section 2.6.2** of [golub2013matrix]: orthogonal matrices are perfectly conditioned in the
2-norm. Let $n \ge 1$ and let $Q \in \mathbb{R}^{n \times n}$ be orthogonal. Then
$$\kappa_2(Q) = \|Q\|_2 \|Q^T\|_2 = 1.$$
-/
theorem kappa_two_eq_one_of_mem_orthogonalGroup (hn : 0 < n) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) : kappa 2 Q = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hQu : IsUnit Q :=
    ⟨⟨Q, star Q, mem_unitaryGroup_iff.1 hQ, mem_unitaryGroup_iff'.1 hQ⟩, rfl⟩
  have h := condNumber_l2_of_mem_unitaryGroup hQ
  rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse] at h
  rw [kappa_of_isUnit 2 hQu, condNumberLp, lpOpNorm_two, lpOpNorm_two, h, ENNReal.ofReal_one]

end L2

/-! ### §2.6.3 Determinants and nearness to singularity -/

/-- The entries of the matrix $B_n$ of (2.6.9) on natural number indices: $1$ on the diagonal, $-1$
above it and $0$ below it. -/
private def bEntry (i k : ℕ) : ℝ :=
  if i = k then 1 else if i < k then -1 else 0

/-- The entries of $B_n^{-1}$ on natural number indices: $1$ on the diagonal, $2^{j-i-1}$ at the
position $(i, j)$ above it and $0$ below it. -/
private def cEntry (k j : ℕ) : ℝ :=
  if k = j then 1 else if k < j then 2 ^ (j - k - 1) else 0

private theorem bEntry_of_lt {i k : ℕ} (h : k < i) : bEntry i k = 0 := by
  simp [bEntry, show i ≠ k by omega, show ¬ i < k by omega]

private theorem bEntry_of_gt {i k : ℕ} (h : i < k) : bEntry i k = -1 := by
  simp [bEntry, h.ne, h]

private theorem cEntry_of_gt {k j : ℕ} (h : j < k) : cEntry k j = 0 := by
  simp [cEntry, show k ≠ j by omega, show ¬ k < j by omega]

/-- The columns of $B_n^{-1}$ double: $c_{k,j+1} = 2 c_{kj} - \delta_{kj} + \delta_{k,j+1}$. -/
private theorem cEntry_succ (k j : ℕ) :
    cEntry k (j + 1) = 2 * cEntry k j - (if k = j then 1 else 0) +
      (if k = j + 1 then 1 else 0) := by
  rcases lt_trichotomy k j with h | rfl | h
  · have e : j + 1 - k - 1 = (j - k - 1) + 1 := by omega
    simp only [cEntry]
    rw [e]
    simp only [show k ≠ j + 1 by omega, show k < j + 1 by omega, h.ne, h, ↓reduceIte, pow_succ]
    ring
  · norm_num [cEntry]
  · rcases (show k = j + 1 ∨ j + 1 < k by omega) with rfl | h'
    · simp [cEntry]
    · rw [cEntry_of_gt h, cEntry_of_gt h']
      simp [show k ≠ j by omega, show k ≠ j + 1 by omega]

/-- For $j + 1 < n$, $\sum_k b_{ik} c_{k,j+1} = 2 \sum_k b_{ik} c_{kj} - b_{ij} + b_{i,j+1}$. -/
private theorem sum_bEntry_mul_cEntry_succ {n i j : ℕ} (hj : j + 1 < n) :
    ∑ k ∈ range n, bEntry i k * cEntry k (j + 1) =
      2 * ∑ k ∈ range n, bEntry i k * cEntry k j - bEntry i j + bEntry i (j + 1) := by
  have h : ∀ k, bEntry i k * cEntry k (j + 1) = 2 * (bEntry i k * cEntry k j) -
      (if k = j then bEntry i k else 0) + (if k = j + 1 then bEntry i k else 0) := fun k => by
    rw [cEntry_succ]
    split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.sum_ite_eq', ite_eq_left (mem_range.2 (by omega)), ite_eq_left (mem_range.2 hj)]

/-- For $j < i$, row $i$ of $B_n$ times column $j$ of $B_n^{-1}$ is $0$. -/
private theorem sum_bEntry_mul_cEntry_of_lt {n i j : ℕ} (hji : j < i) :
    ∑ k ∈ range n, bEntry i k * cEntry k j = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i ≤ k
  · rw [cEntry_of_gt (by omega), mul_zero]
  · rw [bEntry_of_lt (by omega), zero_mul]

/-- For $i < n$, row $i$ of $B_n$ times column $i$ of $B_n^{-1}$ is $1$. -/
private theorem sum_bEntry_mul_cEntry_self {n i : ℕ} (hi : i < n) :
    ∑ k ∈ range n, bEntry i k * cEntry k i = 1 := by
  rw [Finset.sum_eq_single_of_mem i (mem_range.2 hi)]
  · simp [bEntry, cEntry]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [bEntry_of_lt h, zero_mul]
    · rw [cEntry_of_gt h, mul_zero]

/-- For $j > i$, row $i$ of $B_n$ times column $j$ of $B_n^{-1}$ is $0$; the proof is by induction
on $j$. -/
private theorem sum_bEntry_mul_cEntry_of_gt {n i : ℕ} (d : ℕ) (hj : i + 1 + d < n) :
    ∑ k ∈ range n, bEntry i k * cEntry k (i + 1 + d) = 0 := by
  induction d with
  | zero =>
    rw [add_zero, sum_bEntry_mul_cEntry_succ (by omega), sum_bEntry_mul_cEntry_self (by omega),
      bEntry_of_gt (by omega : i < i + 1)]
    norm_num [bEntry]
  | succ d ih =>
    rw [show i + 1 + (d + 1) = i + 1 + d + 1 by ring, sum_bEntry_mul_cEntry_succ (by omega),
      ih (by omega), bEntry_of_gt (by omega : i < i + 1 + d),
      bEntry_of_gt (by omega : i < i + 1 + d + 1)]
    ring

/-- $B_n B_n^{-1} = I$ on natural number indices. -/
private theorem sum_bEntry_mul_cEntry {n i j : ℕ} (hi : i < n) (hj : j < n) :
    ∑ k ∈ range n, bEntry i k * cEntry k j = if i = j then 1 else 0 := by
  rcases lt_trichotomy j i with hji | rfl | hij
  · rw [ite_eq_right hji.ne', sum_bEntry_mul_cEntry_of_lt hji]
  · rw [ite_eq_left rfl, sum_bEntry_mul_cEntry_self hi]
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - i - 1, by omega⟩
    rw [ite_eq_right (by omega), sum_bEntry_mul_cEntry_of_gt d hj]

/-- For $i \le m$, the row sums of $|B_n|$ satisfy $\sum_{k < m} |b_{ik}| = m - i$. -/
private theorem sum_abs_bEntry {i m : ℕ} (hi : i ≤ m) :
    ∑ k ∈ range m, |bEntry i k| = ((m - i : ℕ) : ℝ) := by
  induction m, hi using Nat.le_induction with
  | base =>
    rw [Nat.sub_self, Nat.cast_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [bEntry_of_lt (mem_range.1 hk), abs_zero]
  | succ m hm ih =>
    rw [Finset.sum_range_succ, ih, show m + 1 - i = (m - i) + 1 by omega, Nat.cast_succ]
    congr 1
    rcases hm.eq_or_lt with rfl | h
    · simp [bEntry]
    · rw [bEntry_of_gt h, abs_neg, abs_one]

/-- For $i < m$, the row sums of $|B_n^{-1}|$ satisfy $\sum_{k < m} |c_{ik}| = 2^{m-i-1}$. -/
private theorem sum_abs_cEntry {i m : ℕ} (hi : i < m) :
    ∑ k ∈ range m, |cEntry i k| = 2 ^ (m - i - 1) := by
  induction m, hi using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun k hk => ?_]
    · simp [cEntry]
    · rw [cEntry_of_gt (mem_range.1 hk), abs_zero]
  | succ m hm ih =>
    rw [Finset.sum_range_succ, ih, show m + 1 - i - 1 = (m - i - 1) + 1 by omega, pow_succ]
    have hc : cEntry i m = 2 ^ (m - i - 1) := by
      simp [cEntry, show i ≠ m by omega, show i < m by omega]
    rw [hc, abs_of_pos (by positivity)]
    ring

/-- If a function $f$ on `Fin n` takes its largest value at the index $0$, then its supremum is
$f(0)$. -/
private theorem iSup_eq_of_le_zero (hn : 0 < n) {f : Fin n → ℝ} (h : ∀ i, f i ≤ f ⟨0, hn⟩) :
    ⨆ i, f i = f ⟨0, hn⟩ :=
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  le_antisymm (ciSup_le h) (le_ciSup (Set.finite_range f).bddAbove _)

/-- **Equation (2.6.9)** of [golub2013matrix]. Let $n \ge 1$, and let
$B_n \in \mathbb{R}^{n \times n}$ be the unit upper triangular matrix with every entry above the
diagonal equal to $-1$. Then
$$\det(B_n) = 1, \qquad \kappa_\infty(B_n) = n \, 2^{n-1}.$$
So the size of the determinant does not measure the conditioning of a matrix. -/
theorem equation_2_6_9 (hn : 0 < n) :
    (of fun i j : Fin n => if i = j then (1 : ℝ) else if i < j then -1 else 0).det = 1 ∧
      condNumberLp ∞ (of fun i j : Fin n => if i = j then (1 : ℝ) else if i < j then -1 else 0) =
        n * 2 ^ (n - 1) := by
  set B : Matrix (Fin n) (Fin n) ℝ := of fun i j => if i = j then 1 else if i < j then -1 else 0
  set C : Matrix (Fin n) (Fin n) ℝ := of fun i j => cEntry i j
  have hB : ∀ i j : Fin n, B i j = bEntry i j := fun i j => by
    simp only [B, bEntry, of_apply, Fin.ext_iff, Fin.lt_def]
  have hC : ∀ i j : Fin n, C i j = cEntry i j := fun _ _ => rfl
  have hBC : B * C = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp_rw [hB, hC]
    rw [Fin.sum_univ_eq_sum_range (fun k => bEntry i k * cEntry k j) n,
      sum_bEntry_mul_cEntry i.isLt j.isLt]
    simp [Fin.ext_iff]
  have hinv : B⁻¹ = C := inv_eq_right_inv hBC
  refine ⟨?_, ?_⟩
  · rw [det_of_isUpperTriangular fun i j (hji : j < i) => ?_]
    · simp [B]
    · simp [B, hji.ne', not_lt.2 hji.le]
  · have hBrow : ∀ i : Fin n, ∑ j, |B i j| = ((n - i : ℕ) : ℝ) := fun i => by
      simp_rw [hB]
      rw [Fin.sum_univ_eq_sum_range (fun k => |bEntry i k|) n, sum_abs_bEntry i.isLt.le]
    have hCrow : ∀ i : Fin n, ∑ j, |C i j| = 2 ^ (n - i - 1) := fun i => by
      simp_rw [hC]
      rw [Fin.sum_univ_eq_sum_range (fun k => |cEntry i k|) n, sum_abs_cEntry i.isLt]
    rw [condNumberLp, equation_2_3_10, equation_2_3_10, hinv]
    simp_rw [hBrow, hCrow]
    rw [iSup_eq_of_le_zero hn fun i => by dsimp only; exact_mod_cast Nat.sub_le n i,
      iSup_eq_of_le_zero hn fun i =>
        pow_le_pow_right₀ one_le_two (by dsimp only; omega)]
    simp

/-- **Section 2.6.3** of [golub2013matrix]. Let $1 \le p \le \infty$ and $n \ge 1$, and let $D_n =
\operatorname{diag}(10^{-1}, \dots, 10^{-1}) \in \mathbb{R}^{n \times n}$. Then
$$\kappa_p(D_n) = 1, \qquad \det(D_n) = 10^{-n}.$$
So $D_n$ is perfectly conditioned although its determinant is small. -/
theorem condNumberLp_diag_tenth (p : ℝ≥0∞) [Fact (1 ≤ p)] (hn : 0 < n) :
    condNumberLp p (diagonal fun _ : Fin n => (10 : ℝ)⁻¹) = 1 ∧
      (diagonal fun _ : Fin n => (10 : ℝ)⁻¹).det = 10 ^ (-(n : ℤ)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨?_, ?_⟩
  · rw [← smul_one_eq_diagonal]
    exact condNumberLp_smul_one p (by norm_num)
  · rw [det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
      _root_.zpow_neg, zpow_natCast]

/-! ### §2.6.4 A rigorous norm bound -/

/-- **Lemma 2.6.1** of [golub2013matrix]. Let $1 \le p \le \infty$, let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $b \in \mathbb{R}^n$ with $b \neq 0$, and
let $Ax = b$. Let $\Delta A \in \mathbb{R}^{n \times n}$ and $\Delta b \in \mathbb{R}^n$ with
$\|\Delta A\|_p \le \epsilon \|A\|_p$ and $\|\Delta b\|_p \le \epsilon \|b\|_p$, and let
$(A + \Delta A) y = b + \Delta b$. If $r = \epsilon \kappa_p(A) < 1$, then $A + \Delta A$ is
nonsingular and
$$\frac{\|y\|_p}{\|x\|_p} \le \frac{1 + r}{1 - r}.$$

**Reading.** The source carries the nonsingularity of $A$ through the convention
$\kappa(A) = \infty$ for singular $A$. Here it is an explicit hypothesis, and $\kappa_p(A)$ is
`Matrix.condNumberLp p A`. -/
theorem lemma_2_6_1 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A ΔA : Matrix (Fin n) (Fin n) ℝ}
    {b Δb x y : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hy : (A + ΔA) *ᵥ y = b + Δb) {ε : ℝ} (hΔA : lpOpNorm p ΔA ≤ ε * lpOpNorm p A)
    (hΔb : ‖WithLp.toLp p Δb‖ ≤ ε * ‖WithLp.toLp p b‖) (hr : ε * condNumberLp p A < 1) :
    IsUnit (A + ΔA) ∧
      ‖WithLp.toLp p y‖ / ‖WithLp.toLp p x‖ ≤
        (1 + ε * condNumberLp p A) / (1 - ε * condNumberLp p A) := by
  refine ⟨isUnit_add_of_lpOpNorm_le p hA hΔA hr, ?_⟩
  have h := norm_add_div_le_of_norm_le_mul (lpEquiv p hA) (lpCLM p ΔA)
    (b := WithLp.toLp p b) (Δb := WithLp.toLp p Δb) (x := WithLp.toLp p x)
    (y := WithLp.toLp p y) (by simp [hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, WithLp.ofLp_toLp, hy, WithLp.toLp_add])
    (by rw [coe_lpEquiv]; exact hΔA) hΔb (by rwa [condNumber_coe_lpEquiv]) (by simpa using hb)
  rwa [condNumber_coe_lpEquiv] at h

/-- **Equation (2.6.11)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular,
let $Ax = b$, and let $(A + \Delta A) y = b + \Delta b$. Then
$$y - x = A^{-1} \Delta b - A^{-1} \Delta A \, y.$$
-/
theorem equation_2_6_11 {A ΔA : Matrix (Fin n) (Fin n) ℝ} {b Δb x y : Fin n → ℝ}
    (hA : IsUnit A) (hx : A *ᵥ x = b) (hy : (A + ΔA) *ᵥ y = b + Δb) :
    y - x = A⁻¹ *ᵥ Δb - A⁻¹ *ᵥ (ΔA *ᵥ y) := by
  rw [sub_eq_inv_mulVec_of_mulVec_eq hA hx hy, mulVec_sub]

/-- **Theorem 2.6.2** of [golub2013matrix], with (2.6.10). Under the hypotheses of Lemma 2.6.1, that
is, $1 \le p \le \infty$, $A$ nonsingular, $Ax = b$ with $b \neq 0$,
$(A + \Delta A) y = b + \Delta b$, $\|\Delta A\|_p \le \epsilon \|A\|_p$,
$\|\Delta b\|_p \le \epsilon \|b\|_p$ and $r = \epsilon \kappa_p(A) < 1$,
$$\frac{\|y - x\|_p}{\|x\|_p} \le \frac{2\epsilon}{1 - r} \kappa_p(A).$$
-/
theorem theorem_2_6_2 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A ΔA : Matrix (Fin n) (Fin n) ℝ}
    {b Δb x y : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hy : (A + ΔA) *ᵥ y = b + Δb) {ε : ℝ} (hΔA : lpOpNorm p ΔA ≤ ε * lpOpNorm p A)
    (hΔb : ‖WithLp.toLp p Δb‖ ≤ ε * ‖WithLp.toLp p b‖) (hr : ε * condNumberLp p A < 1) :
    ‖WithLp.toLp p (y - x)‖ / ‖WithLp.toLp p x‖ ≤
      2 * ε / (1 - ε * condNumberLp p A) * condNumberLp p A := by
  have h := relative_error_le_of_norm_le_mul (lpEquiv p hA) (lpCLM p ΔA)
    (b := WithLp.toLp p b) (Δb := WithLp.toLp p Δb) (x := WithLp.toLp p x)
    (y := WithLp.toLp p y) (by simp [hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, WithLp.ofLp_toLp, hy, WithLp.toLp_add])
    (by rw [coe_lpEquiv]; exact hΔA) hΔb (by rwa [condNumber_coe_lpEquiv]) (by simpa using hb)
  rwa [condNumber_coe_lpEquiv, ← WithLp.toLp_sub] at h

/-! ### §2.6.5 More refined bounds -/

/-- **Section 2.6.5** of [golub2013matrix], the Skeel condition number. For
$A \in \mathbb{R}^{n \times n}$, the Skeel condition number `Matrix.skeelCond A` is
$\| |A^{-1}| |A| \|_\infty$, and
$$\| |A^{-1}| |A| \|_\infty \le \kappa_\infty(A).$$

Here $|A|$ is the entrywise absolute value. Both sides are $0$ when $A$ is singular, because the
inverse of Mathlib is then $0$. -/
theorem skeelCond_eq_and_le_condNumberLp (A : Matrix (Fin n) (Fin n) ℝ) :
    skeelCond A = lpOpNorm ∞ (A⁻¹.abs * A.abs) ∧ skeelCond A ≤ condNumberLp ∞ A :=
  ⟨(lpOpNorm_top _).symm, skeelCond_le_condNumberLp_top A⟩

/-- **Theorem 2.6.3** of [golub2013matrix], with (2.6.12). Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular, let $b \in \mathbb{R}^n$ with $b \neq 0$, and let $Ax = b$. Let
$\Delta A \in \mathbb{R}^{n \times n}$ and $\Delta b \in \mathbb{R}^n$ with
$|\Delta A| \le \epsilon |A|$ and $|\Delta b| \le \epsilon |b|$ entrywise, and let
$(A + \Delta A) y = b + \Delta b$. If $r = \epsilon \kappa_\infty(A) < 1$, then $A + \Delta A$
is nonsingular and
$$\frac{\|y - x\|_\infty}{\|x\|_\infty} \le \frac{2\epsilon}{1 - r} \| |A^{-1}| |A| \|_\infty.$$

**Typo.** The source prints the hypothesis as $\delta \kappa_\infty(A) = r < 1$; the intended
quantity is $\epsilon$. -/
theorem theorem_2_6_3 {A ΔA : Matrix (Fin n) (Fin n) ℝ} {b Δb x y : Fin n → ℝ} (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hb : b ≠ 0) (hy : (A + ΔA) *ᵥ y = b + Δb) {ε : ℝ}
    (hΔA : ΔA.abs ≤ₑ ε • A.abs) (hΔb : |Δb| ≤ ε • |b|) (hr : ε * condNumberLp ∞ A < 1) :
    IsUnit (A + ΔA) ∧
      ‖WithLp.toLp ∞ (y - x)‖ / ‖WithLp.toLp ∞ x‖ ≤
        2 * ε / (1 - ε * condNumberLp ∞ A) * lpOpNorm ∞ (A⁻¹.abs * A.abs) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
  have hε0 : 0 ≤ ε := by
    have h := hΔb i
    simp only [Pi.abs_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h hi
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg (abs_pos.2 hi)
    linarith [abs_nonneg (Δb i)]
  have hΔA' : lpOpNorm ∞ ΔA ≤ ε * lpOpNorm ∞ A := by
    rw [lpOpNorm_top, lpOpNorm_top]
    exact linfty_opNorm_le_mul_of_abs_entrywiseLE hε0 hΔA
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have hsk := skeelCond_le_condNumberLp_top A
  have hsmall : ε * skeelCond A < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsk hε0) hr
  refine ⟨isUnit_add_of_lpOpNorm_le ∞ hA hΔA' hr, ?_⟩
  have hsk0 : 0 ≤ skeelCond A := by
    rw [(skeelCond_eq_and_le_condNumberLp A).1]
    exact lpOpNorm_nonneg _ _
  have h := (norm_sub_le_of_abs_le_abs hA hx hy hε0 hΔA hΔb hsmall hx0).2
  rw [PiLp.norm_toLp, PiLp.norm_toLp, ← (skeelCond_eq_and_le_condNumberLp A).1]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hsk0)
  refine div_le_div_of_nonneg_left (by positivity) (by linarith) ?_
  linarith [mul_le_mul_of_nonneg_left hsk hε0]

/-- **Equation (2.6.13)** of [golub2013matrix] (the Oettli–Prager theorem). Let
$A, E \in \mathbb{R}^{n \times n}$ and $b, f, \hat x \in \mathbb{R}^n$, and let
$g = |E| |\hat x| + |f|$. Then:
* for every $\omega \ge 0$, there are $\Delta A$ and $\Delta b$ with
  $(A + \Delta A) \hat x = b + \Delta b$, $|\Delta A| \le \omega |E|$ and
  $|\Delta b| \le \omega |f|$ if and only if $|b - A \hat x| \le \omega g$;
* if every row $i$ with $g_i = 0$ has $(b - A\hat x)_i = 0$, the least such $\omega \ge 0$ is
  $\omega_{\min} = \max_i |A \hat x - b|_i / g_i$;
* if some row $i$ has $g_i = 0$ and $(b - A\hat x)_i \neq 0$, no such $\omega \ge 0$ exists,
  which is the value $\omega_{\min} = \infty$ of the source;
* if $A \hat x = b$, then $\omega_{\min} = 0$.

All inequalities between matrices and vectors are entrywise. The value $\omega_{\min}$ is
`Matrix.componentwiseBackwardError A E b f x`, in which a row with $g_i = 0$ contributes $0$. -/
theorem equation_2_6_13 (A E : Matrix (Fin n) (Fin n) ℝ) (b f x : Fin n → ℝ) :
    (∀ ω : ℝ, 0 ≤ ω →
      ((∃ (ΔA : Matrix (Fin n) (Fin n) ℝ) (Δb : Fin n → ℝ), (A + ΔA) *ᵥ x = b + Δb ∧
          ΔA.abs ≤ₑ ω • E.abs ∧ |Δb| ≤ ω • |f|) ↔
        |b - A *ᵥ x| ≤ ω • (E.abs *ᵥ |x| + |f|))) ∧
    ((∀ i, (E.abs *ᵥ |x| + |f|) i = 0 → (b - A *ᵥ x) i = 0) →
      IsLeast {ω : ℝ | 0 ≤ ω ∧ ∃ (ΔA : Matrix (Fin n) (Fin n) ℝ) (Δb : Fin n → ℝ),
          (A + ΔA) *ᵥ x = b + Δb ∧ ΔA.abs ≤ₑ ω • E.abs ∧ |Δb| ≤ ω • |f|}
        (componentwiseBackwardError A E b f x)) ∧
    ((∃ i, (E.abs *ᵥ |x| + |f|) i = 0 ∧ (b - A *ᵥ x) i ≠ 0) →
      ¬ ∃ ω : ℝ, 0 ≤ ω ∧ ∃ (ΔA : Matrix (Fin n) (Fin n) ℝ) (Δb : Fin n → ℝ),
          (A + ΔA) *ᵥ x = b + Δb ∧ ΔA.abs ≤ₑ ω • E.abs ∧ |Δb| ≤ ω • |f|) ∧
    (A *ᵥ x = b → componentwiseBackwardError A E b f x = 0) := by
  refine ⟨fun ω hω => exists_perturbation_iff_abs_residual_le A E b f x hω,
    isLeast_componentwiseBackwardError A E b f x, ?_, fun hx => ?_⟩
  · rintro ⟨i, hs, hr⟩ ⟨ω, hω, hex⟩
    have h := (exists_perturbation_iff_abs_residual_le A E b f x hω).1 hex i
    simp only [Pi.abs_apply, Pi.smul_apply, smul_eq_mul, hs, mul_zero] at h
    exact hr (abs_nonpos_iff.1 h)
  · simp [componentwiseBackwardError, hx]

end GolubVanLoan.Chapter02
