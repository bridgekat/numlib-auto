/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.ConditionEstimation
import Numlib.Direct.Refinement
import NumlibSurface.GolubVanLoan.Chapter02.Section06
import NumlibSurface.GolubVanLoan.Chapter03.Section04

/-!
# Golub and Van Loan, Section 3.5: Improving and estimating accuracy

This module formalizes §3.5 of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$, and let $\hat x$ be the solution of $Ax = b$ computed by Gaussian elimination
with partial pivoting. Heuristic I says that $\hat x$ has a relatively small residual, and (3.5.2)
says that its relative error is about $u \kappa_\infty(A)$. The module proves the rigorous
inequalities behind these statements. It treats scaling by nonsingular matrices $D_1$, $D_2$ (3.5.3)
and row–column equilibration, iterative improvement $r = b - A\hat x$, $Ly = Pr$, $Uz = y$,
$x_{new} = \hat x + z$ (3.5.4), and its mixed precision form (3.5.5).

For condition estimation, the module proves the implication $Ay = d \Rightarrow \|A^{-1}\|_\infty
\ge \|y\|_\infty / \|d\|_\infty$ of Cline, Moler, Stewart and Wilkinson. It defines back
substitution with a right-hand side chosen during the solve (3.5.6), the condition estimator
Algorithm 3.5.1 for an upper triangular $T$, and the estimate of $\kappa_\infty(A)$ from $PA = LU$
of §3.5.4. In exact arithmetic each estimate is a lower bound for the condition number. The proofs
use `Numlib.Direct.Refinement` and `Numlib.Direct.ConditionEstimation`.

## Main definitions

* §3.5.2, `GolubVanLoan.Chapter03.IsEquilibrated`: every row and every column of the matrix has
  $\infty$-norm in $[1/\beta, 1]$.
* (3.5.4), `GolubVanLoan.Chapter03.iterativeImprovementStep`: one step of iterative improvement with
  $PA = LU$.
* (3.5.5), `GolubVanLoan.Chapter03.mixedPrecisionImprovement`: $k$ passes of iterative improvement
  from $x = 0$, with the residual in higher precision.
* (3.5.6), `GolubVanLoan.Chapter03.backSubstChosenRHS`: column back substitution that chooses $d(k)$
  during the solve.
* §3.5.4, `GolubVanLoan.Chapter03.signChoice`: the choice $d(k) = -\operatorname{sign}(p(k))$.
* §3.5.4, `GolubVanLoan.Chapter03.linftyNormRounded`: the rounded $\infty$-norm of a matrix.
* Algorithm 3.5.1, `GolubVanLoan.Chapter03.algorithm_3_5_1`: the condition estimator for an upper
  triangular matrix.
* §3.5.4, `GolubVanLoan.Chapter03.luCondEstimate`: the estimate $\hat\kappa_\infty = \|A\|_\infty
  \|z\|_\infty / \|r\|_\infty$ from $PA = LU$.
* Algorithm 3.5.1, `GolubVanLoan.Chapter03.lookaheadChoice`: the exact look-ahead choice of $d(k)$.

## Main results

* Heuristic I, `GolubVanLoan.Chapter03.heuristic_I`: $\|b - A\hat x\|_\infty \le n^2 (1 + u)
  \gamma_{3n} \rho \|A\|_\infty \|\hat x\|_\infty$ for every computed solution of Gaussian
  elimination with partial pivoting.
* (3.5.2), `GolubVanLoan.Chapter03.equation_3_5_2`: a backward error
  $\|E\|_\infty \le \varepsilon \|A\|_\infty$ gives the relative error bound
  $2\varepsilon\kappa_\infty(A) / (1 - \varepsilon\kappa_\infty(A))$.
* (3.5.3), `GolubVanLoan.Chapter03.equation_3_5_3`: $Ax = b$ is the scaled system
  $(D_1^{-1} A D_2) y = D_1^{-1} b$ with $x = D_2 y$, and relative errors correspond.
* (3.5.4), `GolubVanLoan.Chapter03.equation_3_5_4`: in exact arithmetic one step of iterative
  improvement gives $A x_{new} = b$.
* (3.5.5), `GolubVanLoan.Chapter03.equation_3_5_5`: in exact arithmetic $k \ge 1$ passes of mixed
  precision improvement return the solution.
* §3.5.4, `GolubVanLoan.Chapter03.condEstimate_lowerBound`: $Ay = d$ implies $\|y\|_\infty \le
  \|A^{-1}\|_\infty \|d\|_\infty$, so $\|A\|_\infty \|y\|_\infty / \|d\|_\infty \le
  \kappa_\infty(A)$.
* (3.5.6), `GolubVanLoan.Chapter03.equation_3_5_6`: the exact output $(y, d)$ of (3.5.6) satisfies
  $Ty = d$.
* §3.5.4, `GolubVanLoan.Chapter03.backSubstChosenRHS_sign`: with
  $d(k) = -\operatorname{sign}(p(k))$, $d$ is a sign vector and
  $\|T\|_\infty \|y\|_\infty \le \kappa_\infty(T)$.
* §3.5.4, `GolubVanLoan.Chapter03.luCondEstimate_le`: in exact arithmetic the estimate from
  $PA = LU$ is at most $\kappa_\infty(A)$.
* Algorithm 3.5.1, `GolubVanLoan.Chapter03.algorithm_3_5_1_spec`: in exact arithmetic the estimator
  solves $Ty_0 = d$ for a sign vector $d$, returns $\kappa = \|y_0\|_\infty \|T\|_\infty \le
  \kappa_\infty(T)$ and a unit vector $y$ with $\|Ty\|_\infty \ge 1 / \|T^{-1}\|_\infty$.

## Conventions

* The $\infty$-norm of a vector is the sup norm on `Fin n → ℝ`. The $\infty$-norm of a matrix is the
  scoped `Matrix.Norms.Operator` norm, which is `Matrix.lpOpNorm ⊤` (`Matrix.lpOpNorm_top`), and
  $\kappa_\infty(A)$ is `Matrix.condNumberLp ⊤ A`.
* A computed quantity is an element of the run set of its program in the rounding model `fp`, with
  the hook `fp.round`. Exact arithmetic is the run at `Id` with the hook `pure`.

## Implementation notes

* The iterative improvement programs use the rounding hook as the other algorithms of the chapter
  do. The mixed precision program takes two hooks: the working precision `rnd` and the residual
  precision `rndHi`. The residual is computed with `rndHi` and stored in working precision by one
  more `rnd`.
* In Algorithm 3.5.1 every flop is rounded, including the flops of the look-ahead scores. The
  absolute values, the comparison and the maximum $\|y\|_\infty$ are exact.

## Deviations from the source

* **Heuristic I** (reading). The source states $\|b - A\hat x\|_\infty \approx u \|A\|_\infty \|\hat
  x\|_\infty$. The theorem states a rigorous bound under the hypotheses of (3.4.9). See
  `GolubVanLoan.Chapter03.heuristic_I`.
* **(3.5.2)** (reading). The source states $\|\hat x - x\|_\infty / \|x\|_\infty \approx u
  \kappa_\infty(A)$. The theorem states the bound $2\varepsilon\kappa_\infty(A) / (1 -
  \varepsilon\kappa_\infty(A))$ for a backward error of size $\varepsilon$. See
  `GolubVanLoan.Chapter03.equation_3_5_2`.
* **(3.5.3)** (generalization). The source takes $D_1$ and $D_2$ diagonal. The theorem holds for any
  nonsingular $D_1$, $D_2$. See `GolubVanLoan.Chapter03.equation_3_5_3`.
* **Algorithm 3.5.1** (reading). The source says $\|Ty\|_\infty \approx 1/\|T^{-1}\|_\infty$ and
  $\kappa \approx \kappa_\infty(T)$. The theorem states the inequalities that hold in exact
  arithmetic. See `GolubVanLoan.Chapter03.algorithm_3_5_1_spec`.

## Not formalized

* **(3.5.1) as an approximation, the "correct digits" statements, and Heuristics II and III.** They
  have no rigorous reading beyond the theorems of this module.
* **The Forsythe–Moler estimate.**
* **Skeel's criterion.**
* **Simple row scaling.**
* **How close the estimate of Algorithm 3.5.1 is to $\kappa_\infty(T)$.**
-/

open FloatingPoint Matrix

open scoped Matrix.Norms.Operator

namespace GolubVanLoan.Chapter03

variable {n : ℕ}

/-! ### Residuals and accuracy (§3.5.1) -/

/-- Let $A, E \in \mathbb{R}^{n \times n}$ and $b, x \in \mathbb{R}^n$. If $(A + E) x = b$, then the
residual satisfies $\|b - Ax\|_\infty \le \|E\|_\infty \|x\|_\infty$. -/
theorem norm_residual_le_of_add_mulVec_eq {A E : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ}
    (h : (A + E) *ᵥ x = b) : ‖b - A *ᵥ x‖ ≤ ‖E‖ * ‖x‖ := by
  have : b - A *ᵥ x = E *ᵥ x := by rw [← h, add_mulVec]; abel
  rw [this]
  exact linfty_opNorm_mulVec E x

/-- **Heuristic I** of [golub2013matrix], §3.5.1: Gaussian elimination produces a solution $\hat x$
with a relatively small residual. Let $A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$,
let the unit roundoff satisfy $u < 1$ and $3nu < 1$, and let $\rho \ge 0$. Let
$(F, \mathrm{piv})$ be an output of Algorithm 3.4.1 on $A$ whose diagonal entries $f_{jj}$ are
all nonzero, and assume that the computed upper factor satisfies
$|\hat u_{ij}| \le \rho \|A\|_\infty$ for all $i, j$. Then every solution $\hat x$ computed from
$F$, $\mathrm{piv}$ and $b$ by `GolubVanLoan.Chapter03.solvePLU` satisfies
$$\|b - A\hat x\|_\infty \le n^2 (1 + u) \gamma_{3n} \rho \|A\|_\infty \|\hat x\|_\infty.$$

**Reading.** The source states $\|b - A\hat x\|_\infty \approx u \|A\|_\infty \|\hat
x\|_\infty$. The theorem states the rigorous bound that this approximation rests on, under the
hypotheses of (3.4.9).

The upper factor is `GolubVanLoan.Chapter03.packedU F`, and $\gamma_{3n}$ is
`FloatingPoint.gamma fp.u (3 * n)`. The proof combines `GolubVanLoan.Chapter03.equation_3_4_9`
with `GolubVanLoan.Chapter03.norm_residual_le_of_add_mulVec_eq`. -/
theorem heuristic_I {fp : RoundingModel ℝ} (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j, out.1 j j ≠ 0) →
      (∀ i j, |packedU out.1 i j| ≤ ρ * ‖A‖) →
      ∀ x ∈ (solvePLU fp.round out.1 out.2 b).run,
        ‖b - A *ᵥ x‖ ≤ (n : ℝ) ^ 2 * (1 + fp.u) * gamma fp.u (3 * n) * ρ * ‖A‖ * ‖x‖ := by
  intro out hout hpiv hU x hx
  obtain ⟨E, hAx, hE⟩ := equation_3_4_9 hu hn A b hρ out hout hpiv hU x hx
  exact (norm_residual_le_of_add_mulVec_eq hAx).trans
    (mul_le_mul_of_nonneg_right hE (norm_nonneg _))

/-- **Equation (3.5.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular,
let $E \in \mathbb{R}^{n \times n}$, and let $b, x, y \in \mathbb{R}^n$ with $Ax = b$,
$b \neq 0$ and $(A + E) y = b$. Let $\varepsilon \ge 0$ with
$\|E\|_\infty \le \varepsilon \|A\|_\infty$ and $\varepsilon \kappa_\infty(A) < 1$. Then
$$\frac{\|y - x\|_\infty}{\|x\|_\infty} \le \frac{2\varepsilon}{1 - \varepsilon\kappa_\infty(A)}
  \kappa_\infty(A).$$

**Reading.** The source states $\|\hat x - x\|_\infty / \|x\|_\infty \approx u
\kappa_\infty(A)$. The theorem is the rigorous form for a backward error of size $\varepsilon$;
for $\varepsilon$ of order $u$ it gives the printed estimate to first order.

The proof combines Theorem 2.6.2 with the backward error. -/
theorem equation_3_5_2 {A E : Matrix (Fin n) (Fin n) ℝ} {b x y : Fin n → ℝ} (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hb : b ≠ 0) (hy : (A + E) *ᵥ y = b) {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ‖E‖ ≤ ε * ‖A‖) (hr : ε * condNumberLp ⊤ A < 1) :
    ‖y - x‖ / ‖x‖ ≤ 2 * ε / (1 - ε * condNumberLp ⊤ A) * condNumberLp ⊤ A := by
  have h := GolubVanLoan.Chapter02.theorem_2_6_2 ⊤ (ΔA := E) (Δb := 0) (y := y) hA hx hb
    (by rw [add_zero]; exact hy)
    (by rw [lpOpNorm_top, lpOpNorm_top]; exact hE)
    (by rw [WithLp.toLp_zero, norm_zero]; exact mul_nonneg hε (norm_nonneg _)) hr
  simpa only [PiLp.norm_toLp] using h

/-! ### Scaling (§3.5.2) -/

/-- **Equation (3.5.3)** of [golub2013matrix], its exact part. Let
$D_1, D_2 \in \mathbb{R}^{n \times n}$ be nonsingular, and let $A \in \mathbb{R}^{n \times n}$
and $b \in \mathbb{R}^n$. Then for every $x$,
$$Ax = b \iff (D_1^{-1} A D_2)(D_2^{-1} x) = D_1^{-1} b,$$
and for all $y, \hat y \in \mathbb{R}^n$ the relative error of $D_2 \hat y$ against $D_2 y$ in
the norm $\|z\|_{D_2} = \|D_2^{-1} z\|_\infty$ is the relative error of $\hat y$ against $y$:
$$\frac{\|D_2^{-1}(D_2 \hat y - D_2 y)\|_\infty}{\|D_2^{-1} D_2 y\|_\infty} = \frac{\|\hat y -
  y\|_\infty}{\|y\|_\infty}.$$

**Generalization.** The source takes $D_1$ and $D_2$ diagonal. The theorem holds for any
nonsingular $D_1$ and $D_2$.

The estimate "$\approx u \kappa_\infty(D_1^{-1} A D_2)$" of the source is (3.5.2) for the scaled
system, `GolubVanLoan.Chapter03.equation_3_5_2`. Both quotients are $0$ when $y = 0$, by the
convention $x / 0 = 0$. -/
theorem equation_3_5_3 {D₁ D₂ : Matrix (Fin n) (Fin n) ℝ} (h₁ : IsUnit D₁) (h₂ : IsUnit D₂)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (∀ x, A *ᵥ x = b ↔ (D₁⁻¹ * A * D₂) *ᵥ (D₂⁻¹ *ᵥ x) = D₁⁻¹ *ᵥ b) ∧
      ∀ y ŷ : Fin n → ℝ, ‖D₂⁻¹ *ᵥ (D₂ *ᵥ ŷ - D₂ *ᵥ y)‖ / ‖D₂⁻¹ *ᵥ (D₂ *ᵥ y)‖ =
        ‖ŷ - y‖ / ‖y‖ := by
  have hD : D₂⁻¹ * D₂ = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 h₂)
  refine ⟨fun x => scaled_mulVec_eq_iff (isUnit_nonsing_inv_iff.2 h₁) h₂ A x b,
    fun y ŷ => ?_⟩
  rw [← mulVec_sub, mulVec_mulVec, mulVec_mulVec, hD, one_mulVec, one_mulVec]

/-- **Section 3.5.2** of [golub2013matrix], row–column equilibration. A matrix
$M \in \mathbb{R}^{n \times n}$ is **equilibrated** with parameter $\beta$ if the $\infty$-norm
of each row and of each column of $M$ lies in the interval $[1/\beta, 1]$.

The source asks to choose $D_1$ and $D_2$ so that $D_1^{-1} A D_2$ has this property. Row $i$ is
`M i` and column $j$ is `Mᵀ j`, each with the sup norm. -/
def IsEquilibrated (β : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, 1 / β ≤ ‖M i‖ ∧ ‖M i‖ ≤ 1) ∧ ∀ j, 1 / β ≤ ‖Mᵀ j‖ ∧ ‖Mᵀ j‖ ≤ 1

/-! ### Iterative improvement (§3.5.3) -/

section Improvement

variable {M : Type → Type} [Monad M]

variable (rnd : ℝ → M ℝ)

/-- **Equation (3.5.4)** of [golub2013matrix], one step of iterative improvement with $PA = LU$:
```
r = b - A x̂
Solve Ly = Pr.
Solve Uz = y.
x_new = x̂ + z
```
Given $A$, a packed factor $F$ with pivot vector $\mathrm{piv}$, $b$ and $\hat x$, the program
returns $x_{new}$.

The residual is computed row by row, $r_i = \mathrm{fl}(b_i - \mathrm{fl}(A(i,:) \cdot \hat
x))$, with the dot product `FloatingPoint.dotAccum` of Algorithm 1.1.1. The two solves are
`GolubVanLoan.Chapter03.solvePLU`, and the update is rounded entry by entry. -/
noncomputable def iterativeImprovementStep (A F : Matrix (Fin n) (Fin n) ℝ) (piv : Fin n → Fin n)
    (b x : Fin n → ℝ) : M (Fin n → ℝ) := do
  let r ← (List.finRange n).foldlM (fun (r : Fin n → ℝ) i => do
    let s ← dotAccum rnd (List.finRange n) (A i) x 0
    let ri ← rnd (b i - s)
    pure (Function.update r i ri)) 0
  let z ← solvePLU rnd F piv r
  (List.finRange n).foldlM (fun (y : Fin n → ℝ) i => do
    let yi ← rnd (x i + z i)
    pure (Function.update y i yi)) x

/-- **Equation (3.5.5)** of [golub2013matrix], mixed precision iterative improvement. Once $PA = LU$
is computed, start from $x = 0$ and repeat $k$ times:
```
r = b - Ax (higher precision)
Solve Ly = Pr for y and Uz = y for z.
x = x + z
```
The program returns the last $x$.

The residual is computed with the hook `rndHi`, which stands for the arithmetic with $2t$
digits, and is stored in working precision by one more `rnd`. Every other operation uses the
working hook `rnd`. -/
noncomputable def mixedPrecisionImprovement (rndHi : ℝ → M ℝ) (A F : Matrix (Fin n) (Fin n) ℝ)
    (piv : Fin n → Fin n) (b : Fin n → ℝ) (k : ℕ) : M (Fin n → ℝ) :=
  (List.range k).foldlM (fun (x : Fin n → ℝ) _ => do
    let r ← (List.finRange n).foldlM (fun (r : Fin n → ℝ) i => do
      let s ← dotAccum rndHi (List.finRange n) (A i) x 0
      let t ← rndHi (b i - s)
      let ri ← rnd t
      pure (Function.update r i ri)) 0
    let z ← solvePLU rnd F piv r
    (List.finRange n).foldlM (fun (y : Fin n → ℝ) i => do
      let yi ← rnd (x i + z i)
      pure (Function.update y i yi)) x) 0

end Improvement

/-- Let $A \in \mathbb{R}^{n \times n}$, and let $F$ be a packed matrix and $\mathrm{piv}$ a pivot
vector such that $PA = LU$ exactly, where $P$ is the permutation matrix encoded by
$\mathrm{piv}$, $L$ is `GolubVanLoan.Chapter03.packedL F` and $U$ is
`GolubVanLoan.Chapter03.packedU F`. If every diagonal entry $u_{ii}$ is nonzero, then for every
$r \in \mathbb{R}^n$ the exact output $z$ of `GolubVanLoan.Chapter03.solvePLU` on $F$,
$\mathrm{piv}$ and $r$ satisfies $Az = r$. -/
theorem mulVec_solvePLU_id {A F : Matrix (Fin n) (Fin n) ℝ} {piv : Fin n → Fin n}
    (hLU : IsLU ((pivPerm piv).permMatrix ℝ * A) (packedL F) (packedU F))
    (hd : ∀ i, packedU F i i ≠ 0) (r : Fin n → ℝ) :
    A *ᵥ Id.run (solvePLU pure F piv r) = r := by
  change A *ᵥ Id.run (algorithm_3_1_2 pure (packedU F)
    (Id.run (algorithm_3_1_1 pure (packedL F) (applyPiv piv r)))) = r
  rw [algorithm_3_1_1_eq_forwardSubst, algorithm_3_1_2_eq_backSubst, (applyPiv_eq _ _).1]
  exact mulVec_luSolve_permMatrix r hLU hd

/-- The exact residual loop computes $b - Ax$. -/
private theorem residual_id (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    (List.finRange n).foldl (fun (r : Fin n → ℝ) i =>
      Function.update r i (b i - (0 + ((List.finRange n).map fun k => A i k * x k).sum))) 0 =
      b - A *ᵥ x := by
  funext i
  rw [List.foldl_update_eq_ite
    (fun i => b i - (0 + ((List.finRange n).map fun k => A i k * x k).sum))]
  simp [mulVec, dotProduct, Fin.sum_univ_def]

/-- The exact correction loop computes $x + z$. -/
private theorem update_add_id (x z : Fin n → ℝ) :
    (List.finRange n).foldl (fun (y : Fin n → ℝ) i => Function.update y i (x i + z i)) x =
      x + z := by
  funext i
  rw [List.foldl_update_eq_ite (fun i => x i + z i)]
  simp

/-- **Equation (3.5.4)** of [golub2013matrix], in exact arithmetic:
$A x_{new} = A\hat x + Az = (b - r) + r = b$. Let $A \in \mathbb{R}^{n \times n}$, and let $F$
and $\mathrm{piv}$ give an exact factorization $PA = LU$ where $L$ is
`GolubVanLoan.Chapter03.packedL F` and $U$ is `GolubVanLoan.Chapter03.packedU F`, and with every
$u_{ii}$ nonzero. Then for all $b, \hat x \in \mathbb{R}^n$, the exact output $x_{new}$ of one
step of iterative improvement from $\hat x$ satisfies
$$A x_{new} = b.$$

The hypothesis on the diagonal of $U$ makes $A$ nonsingular. The proof uses
`GolubVanLoan.Chapter03.mulVec_solvePLU_id`. -/
theorem equation_3_5_4 {A F : Matrix (Fin n) (Fin n) ℝ} {piv : Fin n → Fin n}
    (hLU : IsLU ((pivPerm piv).permMatrix ℝ * A) (packedL F) (packedU F))
    (hd : ∀ i, packedU F i i ≠ 0) (b x : Fin n → ℝ) :
    A *ᵥ Id.run (iterativeImprovementStep pure A F piv b x) = b := by
  have h : Id.run (iterativeImprovementStep pure A F piv b x) =
      x + Id.run (solvePLU pure F piv (b - A *ᵥ x)) := by
    simp only [iterativeImprovementStep, dotAccum_pure, pure_bind, List.foldlM_pure]
    rw [← residual_id A b x, ← update_add_id]
    rfl
  rw [h, mulVec_add, mulVec_solvePLU_id hLU hd]
  abel

/-- **Equation (3.5.5)** of [golub2013matrix], in exact arithmetic. Let
$A \in \mathbb{R}^{n \times n}$, and let $F$ and $\mathrm{piv}$ give an exact factorization
$PA = LU$ where $L$ is `GolubVanLoan.Chapter03.packedL F` and $U$ is
`GolubVanLoan.Chapter03.packedU F`, and with every $u_{ii}$ nonzero. Let $b \in \mathbb{R}^n$
and $k \ge 1$. If both hooks are exact, the output $x$ of $k$ passes of mixed precision
iterative improvement satisfies
$$Ax = b.$$

The first pass reaches the solution by (3.5.4), and a pass from the solution stays there. -/
theorem equation_3_5_5 {A F : Matrix (Fin n) (Fin n) ℝ} {piv : Fin n → Fin n}
    (hLU : IsLU ((pivPerm piv).permMatrix ℝ * A) (packedL F) (packedU F))
    (hd : ∀ i, packedU F i i ≠ 0) (b : Fin n → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    A *ᵥ Id.run (mixedPrecisionImprovement pure pure A F piv b k) = b := by
  have hstep : ∀ x : Fin n → ℝ, Id.run (do
      let r ← (List.finRange n).foldlM (fun (r : Fin n → ℝ) i => do
        let s ← dotAccum pure (List.finRange n) (A i) x 0
        let t ← pure (b i - s)
        let ri ← pure t
        pure (Function.update r i ri)) 0
      let z ← solvePLU pure F piv r
      (List.finRange n).foldlM (fun (y : Fin n → ℝ) i => do
        let yi ← pure (x i + z i)
        pure (Function.update y i yi)) x : Id _) =
      x + Id.run (solvePLU pure F piv (b - A *ᵥ x)) := fun x => by
    simp only [dotAccum_pure, pure_bind, List.foldlM_pure]
    rw [← residual_id A b x, ← update_add_id]
    rfl
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [mixedPrecisionImprovement, List.idRun_foldlM, add_comm, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil, hstep, mulVec_add, mulVec_solvePLU_id hLU hd]
  abel

/-! ### Condition estimation (§3.5.4) -/

/-- **Section 3.5.4** of [golub2013matrix], the implication of Cline, Moler, Stewart and Wilkinson.
Let $A \in \mathbb{R}^{n \times n}$ be nonsingular and let $y, d \in \mathbb{R}^n$ with
$Ay = d$. Then
$$\|y\|_\infty \le \|A^{-1}\|_\infty \|d\|_\infty, \qquad \frac{\|A\|_\infty
  \|y\|_\infty}{\|d\|_\infty} \le \kappa_\infty(A).$$

The source writes the first inequality as $\|A^{-1}\|_\infty \ge \|y\|_\infty / \|d\|_\infty$.
The second inequality says that the estimate $\hat\kappa_\infty = \|A\|_\infty \|y\|_\infty /
\|d\|_\infty$ never exceeds $\kappa_\infty(A)$; it also holds for $d = 0$, where the quotient is
$0$ by the convention $x / 0 = 0$. -/
theorem condEstimate_lowerBound {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {y d : Fin n → ℝ}
    (hy : A *ᵥ y = d) :
    ‖y‖ ≤ ‖A⁻¹‖ * ‖d‖ ∧ ‖A‖ * ‖y‖ / ‖d‖ ≤ condNumberLp ⊤ A := by
  have h₁ := norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec ⊤ hA y
  rw [lpSeminorm_apply, lpSeminorm_apply, PiLp.norm_toLp, PiLp.norm_toLp, hy,
    lpOpNorm_top] at h₁
  have h₂ := lpCondEstimate_le_condNumberLp ⊤ hA d
  have hy' : A⁻¹ *ᵥ d = y := by
    rw [← hy, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hA), one_mulVec]
  rw [lpCondEstimate, hy', lpSeminorm_apply, lpSeminorm_apply, PiLp.norm_toLp, PiLp.norm_toLp,
    lpOpNorm_top] at h₂
  exact ⟨h₁, h₂⟩

/-! ### Back substitution with a chosen right-hand side (3.5.6) -/

section ChosenRHS

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n : ℕ}

/-- **Equation (3.5.6)** of [golub2013matrix], the column version of back substitution with the
right-hand side chosen during the solve. The source notes that this procedure is normally used
to solve $Ty = d$, but in the condition estimation setting the right-hand side can be picked
freely:
```
p(1:n) = 0
for k = n:-1:1
    Choose d(k).
    y(k) = (d(k) - p(k))/T(k,k)
    p(1:k-1) = p(1:k-1) + y(k) T(1:k-1,k)
end
```
The program returns $(y, d)$.

The choice is a function `choose k p` of the step $k$ and of the running vector $p$. It is
exact; examples are the sign of $p(k)$ and the look-ahead of Algorithm 3.5.1. Every difference,
quotient, product and sum is rounded. -/
noncomputable def backSubstChosenRHS (choose : Fin n → (Fin n → ℝ) → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) : M ((Fin n → ℝ) × (Fin n → ℝ)) := do
  let st ← (List.finRange n).reverse.foldlM
    (fun (st : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) k => do
      let t ← rnd (choose k st.2.2 - st.2.2 k)
      let yk ← rnd (t / T k k)
      let p ← ((List.finRange n).filter (· < k)).foldlM (fun (p : Fin n → ℝ) i => do
        let q ← rnd (yk * T i k)
        let pi ← rnd (p i + q)
        pure (Function.update p i pi)) st.2.2
      pure (Function.update st.1 k yk, Function.update st.2.1 k (choose k st.2.2), p)) (0, 0, 0)
  pure (st.1, st.2.1)

/-- Let the list of indices `List.finRange n` in decreasing order be
$p \mathbin{+\!\!+} [x] \mathbin{+\!\!+} q$. Then an index $j$ lies in $p$, the indices
processed before $x$, if and only if $x < j$. -/
theorem mem_prefix_reverse_finRange_iff {p q : List (Fin n)} {x : Fin n}
    (h : (List.finRange n).reverse = p ++ x :: q) (j : Fin n) : j ∈ p ↔ x < j := by
  have hs : (List.finRange n).reverse.Pairwise (fun a b => b < a) :=
    List.pairwise_reverse.2 (List.pairwise_lt_finRange n)
  constructor
  · intro hj
    rw [h] at hs
    exact (List.pairwise_append.1 hs).2.2 j hj x List.mem_cons_self
  · intro hxj
    exact List.mem_prefix_of_pairwise hs h (List.mem_reverse.2 (List.mem_finRange j)) (ne_of_gt hxj)
      (lt_asymm hxj)

/-- The exact run of (3.5.6). Let $T \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, and
let $(y, d)$ be the exact output of `GolubVanLoan.Chapter03.backSubstChosenRHS` for a choice
function `choose`. Then for every $j$,
$$y_j t_{jj} = d_j - \sum_{l > j} t_{jl} y_l,$$
and every $d_j$ is a value `choose j q` for some vector $q$. -/
theorem backSubstChosenRHS_id {choose : Fin n → (Fin n → ℝ) → ℝ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hd : ∀ i, T i i ≠ 0) :
    (∀ j, (Id.run (backSubstChosenRHS pure choose T)).1 j * T j j =
      (Id.run (backSubstChosenRHS pure choose T)).2 j -
        ∑ l ∈ Finset.univ.filter (j < ·), T j l * (Id.run (backSubstChosenRHS pure choose T)).1 l) ∧
      ∀ j, ∃ q, (Id.run (backSubstChosenRHS pure choose T)).2 j = choose j q := by
  let step : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n →
      (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) := fun st k =>
    (Function.update st.1 k ((choose k st.2.2 - st.2.2 k) / T k k),
      Function.update st.2.1 k (choose k st.2.2),
      ((List.finRange n).filter (· < k)).foldl (fun p i => Function.update p i
        (p i + (choose k st.2.2 - st.2.2 k) / T k k * T i k)) st.2.2)
  have hrun : Id.run (backSubstChosenRHS pure choose T) =
      (((List.finRange n).reverse.foldl step (0, 0, 0)).1,
        ((List.finRange n).reverse.foldl step (0, 0, 0)).2.1) := by
    simp only [backSubstChosenRHS, pure_bind, List.foldlM_pure]
    rfl
  rw [hrun]
  let I : List (Fin n) → (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Prop := fun pr st =>
    (∀ j ∈ pr, st.1 j * T j j = st.2.1 j - ∑ l ∈ Finset.univ.filter (j < ·), T j l * st.1 l) ∧
    (∀ j ∈ pr, ∃ q, st.2.1 j = choose j q) ∧
    (∀ i, i ∉ pr → st.2.2 i = ∑ j ∈ Finset.univ.filter (· ∈ pr), T i j * st.1 j)
  have hI : I (List.finRange n).reverse ((List.finRange n).reverse.foldl step (0, 0, 0)) := by
    refine List.foldl_prefix_induction step I ⟨by simp, by simp, fun i _ => by simp⟩ ?_
    rintro pr x q hl ⟨y, d, p⟩ ⟨h₁, h₂, h₃⟩
    dsimp only at h₁ h₂ h₃
    have hmem := mem_prefix_reverse_finRange_iff hl
    have hxpr : x ∉ pr := fun h => lt_irrefl x ((hmem x).1 h)
    have hy' : ∀ j, j ≠ x → Function.update y x ((choose x p - p x) / T x x) j = y j :=
      fun j hj => Function.update_of_ne hj _ _
    have hp' : ∀ i, ((List.finRange n).filter (· < x)).foldl (fun p' i => Function.update p' i
        (p' i + (choose x p - p x) / T x x * T i x)) p i =
        if i < x then p i + (choose x p - p x) / T x x * T i x else p i := fun i => by
      rw [List.foldl_update_of_nodup ((List.nodup_finRange n).filter _)
        (fun i y => y i + (choose x p - p x) / T x x * T i x) (fun _ _ _ _ _ e => by rw [e])]
      simp
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun i hi => ?_⟩
    · rcases List.mem_append.1 hj with hj | hj
      · have hxj : x < j := (hmem j).1 hj
        simp only [step]
        rw [hy' j (ne_of_gt hxj), Function.update_of_ne (ne_of_gt hxj), h₁ j hj]
        congr 1
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [hy' l (ne_of_gt (hxj.trans (Finset.mem_filter.1 hl).2))]
      · rw [List.mem_singleton.1 hj]
        simp only [step, Function.update_self]
        rw [div_mul_cancel₀ _ (hd x), h₃ x hxpr]
        congr 1
        refine Finset.sum_congr (by ext l; simp [hmem]) fun l hl => ?_
        rw [Function.update_of_ne (ne_of_gt (Finset.mem_filter.1 hl).2)]
    · rcases List.mem_append.1 hj with hj | hj
      · obtain ⟨q', hq'⟩ := h₂ j hj
        refine ⟨q', ?_⟩
        simp only [step]
        rw [Function.update_of_ne (ne_of_gt ((hmem j).1 hj)), hq']
      · rw [List.mem_singleton.1 hj]
        exact ⟨p, by simp [step]⟩
    · have hix : i ≠ x := fun h => hi (List.mem_append.2 (Or.inr (h ▸ List.mem_singleton_self x)))
      have hipr : i ∉ pr := fun h => hi (List.mem_append.2 (Or.inl h))
      have hlt : i < x := by
        rcases lt_or_gt_of_ne hix with h | h
        · exact h
        · exact absurd ((hmem i).2 h) hipr
      simp only [step]
      rw [hp' i]
      simp only [hlt, ↓reduceIte]
      rw [h₃ i hipr]
      have hsplit : Finset.univ.filter (· ∈ pr ++ [x]) =
          insert x (Finset.univ.filter (· ∈ pr)) := by
        ext j; simp [or_comm]
      rw [hsplit, Finset.sum_insert (by simp [hxpr]), Function.update_self]
      rw [add_comm]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [hy' j (fun h => hxpr (h ▸ (Finset.mem_filter.1 hj).2))]
  exact ⟨fun j => hI.1 j (List.mem_reverse.2 (List.mem_finRange j)),
    fun j => hI.2.1 j (List.mem_reverse.2 (List.mem_finRange j))⟩

/-- **Equation (3.5.6)** of [golub2013matrix] solves the system that it builds. Let
$T \in \mathbb{R}^{n \times n}$ be upper triangular with nonzero diagonal entries. For every
choice function, the exact output $(y, d)$ of back substitution with the right-hand side chosen
during the solve satisfies
$$Ty = d.$$
-/
theorem equation_3_5_6 {choose : Fin n → (Fin n → ℝ) → ℝ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i ≠ 0) :
    T *ᵥ (Id.run (backSubstChosenRHS pure choose T)).1 =
      (Id.run (backSubstChosenRHS pure choose T)).2 := by
  funext j
  rw [mulVec_apply_of_isUpperTriangular hT, mul_comm, (backSubstChosenRHS_id hd).1 j]
  ring

/-- **Section 3.5.4** of [golub2013matrix], the sign choice $d(k) = -\operatorname{sign}(p(k))$: the
value is $-1$ if $p(k) \ge 0$ and $+1$ otherwise. -/
noncomputable def signChoice (k : Fin n) (p : Fin n → ℝ) : ℝ := if 0 ≤ p k then -1 else 1

/-- **Section 3.5.4** of [golub2013matrix], the estimate from the sign choice. Let $n \ge 1$ and let
$T \in \mathbb{R}^{n \times n}$ be upper triangular with nonzero diagonal entries. Let $(y, d)$
be the exact output of (3.5.6) with $d(k) = -\operatorname{sign}(p(k))$. Then $|d_j| = 1$ for
every $j$, and
$$\|T\|_\infty \|y\|_\infty \le \kappa_\infty(T).$$

Since $d$ is a vector of unit $\infty$-norm, the source obtains the estimate
$\hat\kappa_\infty = \|T\|_\infty \|y\|_\infty$. The theorem says that this estimate is a lower
bound for $\kappa_\infty(T)$. -/
theorem backSubstChosenRHS_sign [NeZero n] {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i ≠ 0) :
    (∀ j, |(Id.run (backSubstChosenRHS pure signChoice T)).2 j| = 1) ∧
      ‖T‖ * ‖(Id.run (backSubstChosenRHS pure signChoice T)).1‖ ≤ condNumberLp ⊤ T := by
  have hsign : ∀ j, |(Id.run (backSubstChosenRHS pure signChoice T)).2 j| = 1 := fun j => by
    obtain ⟨q, hq⟩ := (backSubstChosenRHS_id (choose := signChoice) hd).2 j
    rw [hq, signChoice]
    split_ifs <;> simp
  refine ⟨hsign, ?_⟩
  have hU : IsUnit T := hT.isUnit_iff.2 hd
  have := linfty_opNorm_mul_norm_le_condNumberLp_top_of_mulVec_eq hU (equation_3_5_6 hT hd)
    fun j => by rw [Real.norm_eq_abs]; exact hsign j
  rwa [lpOpNorm_top] at this

end ChosenRHS

/-! ### The condition estimator (Algorithm 3.5.1) and the estimate from $PA = LU$ (§3.5.4) -/

section Estimator

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n : ℕ}

/-- The $\infty$-norm of $A \in \mathbb{R}^{m \times n}$ computed as the largest rounded row sum of
absolute values, the $O(n^2)$ formula (2.3.10). Each row sum $\mathrm{fl}(\cdots
\mathrm{fl}(|a_{i1}| + |a_{i2}|) \cdots)$ is rounded at every addition, and the maximum of the
row sums is exact. -/
noncomputable def linftyNormRounded {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : M ℝ := do
  let r ← (List.finRange m).foldlM (fun (r : Fin m → ℝ) i => do
    let s ← (List.finRange n).foldlM (fun (c : ℝ) j => rnd (c + |A i j|)) 0
    pure (Function.update r i s)) 0
  pure ‖r‖

/-- **Algorithm 3.5.1** of [golub2013matrix] (Condition Estimator). Let
$T \in \mathbb{R}^{n \times n}$ be a nonsingular upper triangular matrix. The algorithm computes
a vector $y$ of unit $\infty$-norm and a scalar $\kappa$ so that
$\|Ty\|_\infty \approx 1/\|T^{-1}\|_\infty$ and $\kappa \approx \kappa_\infty(T)$.
```
p(1:n) = 0
for k = n:-1:1
    y(k)⁺ = (1 - p(k))/T(k,k)
    y(k)⁻ = (-1 - p(k))/T(k,k)
    p(k)⁺ = p(1:k-1) + T(1:k-1,k) y(k)⁺
    p(k)⁻ = p(1:k-1) + T(1:k-1,k) y(k)⁻
    if |y(k)⁺| + ‖p(k)⁺‖₁ ≥ |y(k)⁻| + ‖p(k)⁻‖₁
        y(k) = y(k)⁺,  p(1:k-1) = p(k)⁺
    else
        y(k) = y(k)⁻,  p(1:k-1) = p(k)⁻
    end
end
κ = ‖y‖_∞ ‖T‖_∞
y = y/‖y‖_∞
```
The program returns $(\kappa, y)$.

Every flop is rounded, including the flops of the look-ahead scores. The absolute values, the
comparison and the maximum $\|y\|_\infty$ are exact, and $\|T\|_\infty$ is
`GolubVanLoan.Chapter03.linftyNormRounded`. -/
noncomputable def algorithm_3_5_1 (T : Matrix (Fin n) (Fin n) ℝ) : M (ℝ × (Fin n → ℝ)) := do
  let st ← (List.finRange n).reverse.foldlM (fun (st : (Fin n → ℝ) × (Fin n → ℝ)) k => do
    let tp ← rnd (1 - st.2 k)
    let yp ← rnd (tp / T k k)
    let tm ← rnd (-1 - st.2 k)
    let ym ← rnd (tm / T k k)
    let pp ← ((List.finRange n).filter (· < k)).foldlM (fun (q : Fin n → ℝ) i => do
      let a ← rnd (T i k * yp)
      let b ← rnd (q i + a)
      pure (Function.update q i b)) st.2
    let pm ← ((List.finRange n).filter (· < k)).foldlM (fun (q : Fin n → ℝ) i => do
      let a ← rnd (T i k * ym)
      let b ← rnd (q i + a)
      pure (Function.update q i b)) st.2
    let sp ← ((List.finRange n).filter (· < k)).foldlM (fun (c : ℝ) i => rnd (c + |pp i|)) |yp|
    let sm ← ((List.finRange n).filter (· < k)).foldlM (fun (c : ℝ) i => rnd (c + |pm i|)) |ym|
    if sm ≤ sp then pure (Function.update st.1 k yp, pp)
    else pure (Function.update st.1 k ym, pm)) (0, 0)
  let tn ← linftyNormRounded rnd T
  let κ ← rnd (‖st.1‖ * tn)
  let y ← (List.finRange n).foldlM (fun (y : Fin n → ℝ) i => do
    let yi ← rnd (st.1 i / ‖st.1‖)
    pure (Function.update y i yi)) st.1
  pure (κ, y)

/-- **Section 3.5.4** of [golub2013matrix], condition estimation from $PA = LU$:

1. Apply the lower triangular version of Algorithm 3.5.1 to $U^T$ and obtain a large-norm
   solution of $U^T y = d$.
2. Solve the triangular systems $L^T r = y$, $Lw = Pr$ and $Uz = w$.
3. Set $\hat\kappa_\infty = \|A\|_\infty \|z\|_\infty / \|r\|_\infty$.

The program takes $A$, the packed factor $F$ and the pivot vector $\mathrm{piv}$, and returns
$\hat\kappa_\infty$.

The lower triangular version of Algorithm 3.5.1 on $U^T$ is Algorithm 3.5.1 on $U^T$ with its
rows and columns in reversed order, which is an upper triangular matrix. The system $L^T r = y$
is solved by Algorithm 3.1.2, and $Lw = Pr$, $Uz = w$ by `GolubVanLoan.Chapter03.solvePLU`. -/
noncomputable def luCondEstimate (A F : Matrix (Fin n) (Fin n) ℝ) (piv : Fin n → Fin n) : M ℝ := do
  let out ← algorithm_3_5_1 rnd ((packedU F)ᵀ.submatrix Fin.rev Fin.rev)
  let r ← algorithm_3_1_2 rnd (packedL F)ᵀ (out.2 ∘ Fin.rev)
  let z ← solvePLU rnd F piv r
  let an ← linftyNormRounded rnd A
  let t ← rnd (an * ‖z‖)
  rnd (t / ‖r‖)

/-- In exact arithmetic the rounded $\infty$-norm `GolubVanLoan.Chapter03.linftyNormRounded` is the
$\infty$-norm $\|A\|_\infty$. -/
theorem linftyNormRounded_id {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (linftyNormRounded pure A) = ‖A‖ := by
  have hrow : ∀ i, (List.finRange n).foldl (fun (c : ℝ) j => c + |A i j|) 0 = ∑ j, |A i j| :=
    fun i => by rw [List.foldl_add_eq_add_sum_map, zero_add, Fin.sum_univ_def]
  have hr : (List.finRange m).foldl (fun (r : Fin m → ℝ) i => Function.update r i
      ((List.finRange n).foldl (fun (c : ℝ) j => c + |A i j|) 0)) 0 = fun i => ∑ j, |A i j| := by
    funext i
    rw [List.foldl_update_eq_ite
      (fun i => (List.finRange n).foldl (fun (c : ℝ) j => c + |A i j|) 0)]
    beta_reduce
    rw [hrow]
    simp
  have h : Id.run (linftyNormRounded pure A) = ‖fun i => ∑ j, |A i j|‖ := by
    simp only [linftyNormRounded, pure_bind, List.foldlM_pure]
    rw [← hr]
    rfl
  -- the `O(n²)` formula (2.3.10): the sup norm of the vector of row sums
  rw [h, ← lpOpNorm_top, GolubVanLoan.Chapter02.equation_2_3_10, Pi.norm_def,
    Finset.sup_univ_eq_ciSup, NNReal.coe_iSup]
  simp only [coe_nnnorm, Real.norm_eq_abs]
  exact iSup_congr fun i => abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg (A i j))

/-- **Section 3.5.4** of [golub2013matrix]: "note that $\|z\|_\infty \le \|A^{-1}\|_\infty
\|r\|_\infty$". Let $A \in \mathbb{R}^{n \times n}$ be nonsingular, and let $F$ and
$\mathrm{piv}$ give an exact factorization $PA = LU$ where $L$ is
`GolubVanLoan.Chapter03.packedL F` and $U$ is `GolubVanLoan.Chapter03.packedU F`, and with every
$u_{ii}$ nonzero. Then the exact estimate $\hat\kappa_\infty$ of
`GolubVanLoan.Chapter03.luCondEstimate` satisfies
$$\hat\kappa_\infty \le \kappa_\infty(A).$$

The bound holds whatever Step 1 produced, because $Az = r$. -/
theorem luCondEstimate_le {A F : Matrix (Fin n) (Fin n) ℝ} {piv : Fin n → Fin n} (hA : IsUnit A)
    (hLU : IsLU ((pivPerm piv).permMatrix ℝ * A) (packedL F) (packedU F))
    (hd : ∀ i, packedU F i i ≠ 0) :
    Id.run (luCondEstimate pure A F piv) ≤ condNumberLp ⊤ A := by
  set r := Id.run (algorithm_3_1_2 pure (packedL F)ᵀ
    ((Id.run (algorithm_3_5_1 pure ((packedU F)ᵀ.submatrix Fin.rev Fin.rev))).2 ∘ Fin.rev))
  set z := Id.run (solvePLU pure F piv r)
  have hz : A *ᵥ z = r := mulVec_solvePLU_id hLU hd r
  have h : Id.run (luCondEstimate pure A F piv) = ‖A‖ * ‖z‖ / ‖r‖ := by
    change Id.run (linftyNormRounded pure A) * ‖z‖ / ‖r‖ = _
    rw [linftyNormRounded_id]
  rw [h]
  exact (condEstimate_lowerBound hA hz).2

end Estimator

/-! ### What Algorithm 3.5.1 provably computes -/

section EstimatorSpec

variable {n : ℕ}

/-- The exact look-ahead choice of Algorithm 3.5.1: $d(k) = +1$ if the score
$|y(k)^+| + \|p(k)^+\|_1$ is at least $|y(k)^-| + \|p(k)^-\|_1$, and $d(k) = -1$ otherwise. Here
$y(k)^\pm = (\pm 1 - p(k)) / t_{kk}$ and $p(k)^\pm_i = p_i + t_{ik} y(k)^\pm$ for $i < k$. -/
noncomputable def lookaheadChoice (T : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (p : Fin n → ℝ) :
    ℝ :=
  if |(-1 - p k) / T k k| + ∑ i ∈ Finset.univ.filter (· < k),
        |p i + T i k * ((-1 - p k) / T k k)| ≤
      |(1 - p k) / T k k| + ∑ i ∈ Finset.univ.filter (· < k),
        |p i + T i k * ((1 - p k) / T k k)| then 1 else -1

/-- A running sum over the indices before $k$ is the sum over them. -/
private theorem foldl_filter_add (k : Fin n) (f : Fin n → ℝ) (c : ℝ) :
    ((List.finRange n).filter (· < k)).foldl (fun c i => c + f i) c =
      c + ∑ i ∈ Finset.univ.filter (· < k), f i := by
  rw [List.foldl_add_eq_add_sum_map, ← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
  congr 2
  ext i
  simp

/-- The exact step of the loop of Algorithm 3.5.1 is the step of back substitution with the
look-ahead choice, on the components $(y, p)$. -/
private theorem step_3_5_1_eq (T : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (y p : Fin n → ℝ) :
    (let yp := (1 - p k) / T k k
     let ym := (-1 - p k) / T k k
     let pp := ((List.finRange n).filter (· < k)).foldl
       (fun q i => Function.update q i (q i + T i k * yp)) p
     let pm := ((List.finRange n).filter (· < k)).foldl
       (fun q i => Function.update q i (q i + T i k * ym)) p
     if ((List.finRange n).filter (· < k)).foldl (fun c i => c + |pm i|) |ym| ≤
         ((List.finRange n).filter (· < k)).foldl (fun c i => c + |pp i|) |yp|
       then (Function.update y k yp, pp) else (Function.update y k ym, pm)) =
    (Function.update y k ((lookaheadChoice T k p - p k) / T k k),
      ((List.finRange n).filter (· < k)).foldl (fun q i => Function.update q i
        (q i + (lookaheadChoice T k p - p k) / T k k * T i k)) p) := by
  have hnd := (List.nodup_finRange n).filter (· < k)
  have hq : ∀ c : ℝ, ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + T i k * c)) p =
      ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + c * T i k)) p := fun c => by
    funext i
    rw [List.foldl_update_of_nodup hnd (fun i y => y i + T i k * c) (fun _ _ _ _ _ e => by rw [e]),
      List.foldl_update_of_nodup hnd (fun i y => y i + c * T i k) (fun _ _ _ _ _ e => by rw [e])]
    beta_reduce
    rw [mul_comm]
  have hval : ∀ c : ℝ, ∀ i, i < k → ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + T i k * c)) p i = p i + T i k * c :=
    fun c i hi => by
      rw [List.foldl_update_of_nodup hnd (fun i y => y i + T i k * c)
        (fun _ _ _ _ _ e => by rw [e])]
      simp [hi]
  have hscore : ∀ c : ℝ, ((List.finRange n).filter (· < k)).foldl (fun s i => s + |((List.finRange
      n).filter (· < k)).foldl (fun q i => Function.update q i (q i + T i k * c)) p i|) |c| =
      |c| + ∑ i ∈ Finset.univ.filter (· < k), |p i + T i k * c| := fun c => by
    rw [foldl_filter_add]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hval c i (Finset.mem_filter.1 hi).2]
  simp only [hscore, lookaheadChoice]
  split_ifs with h
  · rw [hq]
  · rw [hq]

/-- **Algorithm 3.5.1** of [golub2013matrix], what it provably computes. Let $n \ge 1$ and let
$T \in \mathbb{R}^{n \times n}$ be upper triangular with nonzero diagonal entries. Let
$(\kappa, y)$ be the exact output of Algorithm 3.5.1 on $T$. Then there are
$y_0, d \in \mathbb{R}^n$ with $|d_k| = 1$ for every $k$ and $Ty_0 = d$, such that
$$\kappa = \|y_0\|_\infty \|T\|_\infty, \qquad y = y_0 / \|y_0\|_\infty, \qquad \kappa \le
  \kappa_\infty(T), \qquad \|y\|_\infty = 1, \qquad 1 \le \|T^{-1}\|_\infty \|Ty\|_\infty.$$

**Reading.** The source says that $\|Ty\|_\infty \approx 1/\|T^{-1}\|_\infty$ and
$\kappa \approx \kappa_\infty(T)$. The theorem states the half of these claims that holds in
exact arithmetic: $\kappa$ is a lower bound for $\kappa_\infty(T)$, and
$\|Ty\|_\infty \ge 1/\|T^{-1}\|_\infty$. How close $\kappa$ is to $\kappa_\infty(T)$ is not
formalized.

The vector $y_0$ is the unnormalized $y$ of the loop, and $d$ is the look-ahead choice
`GolubVanLoan.Chapter03.lookaheadChoice`. -/
theorem algorithm_3_5_1_spec [NeZero n] {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i ≠ 0) :
    ∃ y₀ d : Fin n → ℝ, (∀ i, |d i| = 1) ∧ T *ᵥ y₀ = d ∧
      (Id.run (algorithm_3_5_1 pure T)).1 = ‖y₀‖ * ‖T‖ ∧
      (Id.run (algorithm_3_5_1 pure T)).2 = (fun i => y₀ i / ‖y₀‖) ∧
      (Id.run (algorithm_3_5_1 pure T)).1 ≤ condNumberLp ⊤ T ∧
      ‖(Id.run (algorithm_3_5_1 pure T)).2‖ = 1 ∧
      1 ≤ ‖T⁻¹‖ * ‖T *ᵥ (Id.run (algorithm_3_5_1 pure T)).2‖ := by
  set out := Id.run (backSubstChosenRHS pure (lookaheadChoice T) T)
  -- the exact loop of Algorithm 3.5.1 is back substitution with the look-ahead choice
  let stepBS : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n →
      (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) := fun st k =>
    (Function.update st.1 k ((lookaheadChoice T k st.2.2 - st.2.2 k) / T k k),
      Function.update st.2.1 k (lookaheadChoice T k st.2.2),
      ((List.finRange n).filter (· < k)).foldl (fun p i => Function.update p i
        (p i + (lookaheadChoice T k st.2.2 - st.2.2 k) / T k k * T i k)) st.2.2)
  let step35 : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → (Fin n → ℝ) × (Fin n → ℝ) := fun st k =>
    let yp := (1 - st.2 k) / T k k
    let ym := (-1 - st.2 k) / T k k
    let pp := ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + T i k * yp)) st.2
    let pm := ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + T i k * ym)) st.2
    if ((List.finRange n).filter (· < k)).foldl (fun c i => c + |pm i|) |ym| ≤
        ((List.finRange n).filter (· < k)).foldl (fun c i => c + |pp i|) |yp|
      then (Function.update st.1 k yp, pp) else (Function.update st.1 k ym, pm)
  have hsim : ∀ (l : List (Fin n)) (y d p : Fin n → ℝ),
      l.foldl step35 (y, p) = ((l.foldl stepBS (y, d, p)).1, (l.foldl stepBS (y, d, p)).2.2) := by
    intro l
    induction l with
    | nil => intro y d p; rfl
    | cons k l ih =>
      intro y d p
      rw [List.foldl_cons, List.foldl_cons]
      have h := step_3_5_1_eq T k y p
      change step35 (y, p) k = _ at h
      rw [h]
      exact ih _ _ _
  have hout : out = (((List.finRange n).reverse.foldl stepBS (0, 0, 0)).1,
      ((List.finRange n).reverse.foldl stepBS (0, 0, 0)).2.1) := by
    simp only [out, backSubstChosenRHS, pure_bind, List.foldlM_pure]
    rfl
  set Y := ((List.finRange n).reverse.foldl step35 (0, 0)).1 with hY
  have hYout : Y = out.1 := by
    rw [hY, hsim _ 0 0 0, hout]
  have hrun : Id.run (algorithm_3_5_1 pure T) = (‖Y‖ * Id.run (linftyNormRounded pure T),
      (List.finRange n).foldl (fun y i => Function.update y i (Y i / ‖Y‖)) Y) := by
    simp only [algorithm_3_5_1, pure_bind, ite_pure, List.foldlM_pure]
    rfl
  have hy : (List.finRange n).foldl (fun y i => Function.update y i (Y i / ‖Y‖)) Y =
      fun i => Y i / ‖Y‖ := by
    funext i
    rw [List.foldl_update_eq_ite (fun i => Y i / ‖Y‖)]
    simp
  have hsign : ∀ i, |out.2 i| = 1 := fun i => by
    obtain ⟨q, hq⟩ := (backSubstChosenRHS_id (choose := lookaheadChoice T) hd).2 i
    rw [hq, lookaheadChoice]
    split_ifs <;> simp
  have hTy : T *ᵥ out.1 = out.2 := equation_3_5_6 hT hd
  have hU : IsUnit T := hT.isUnit_iff.2 hd
  have hy0 : out.1 ≠ 0 := by
    intro h0
    have := hsign 0
    rw [← hTy, h0, mulVec_zero] at this
    simp at this
  have hκ := linfty_opNorm_mul_norm_le_condNumberLp_top_of_mulVec_eq hU hTy
    fun j => by rw [Real.norm_eq_abs]; exact hsign j
  rw [lpOpNorm_top] at hκ
  have hsmul : (fun i => out.1 i / ‖out.1‖) = (‖out.1‖⁻¹ : ℝ) • out.1 := by
    funext i
    simp [div_eq_inv_mul]
  refine ⟨out.1, out.2, hsign, hTy, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, linftyNormRounded_id, hYout]
  · rw [hrun, hy, hYout]
  · rw [hrun, linftyNormRounded_id, hYout, mul_comm]
    exact hκ
  · rw [hrun, hy, hYout, hsmul, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hy0)]
  · rw [hrun, hy, hYout, hsmul]
    have := one_le_lpOpNorm_top_inv_mul_norm_mulVec_inv_norm_smul hU hy0
    rwa [lpOpNorm_top] at this

end EstimatorSpec

end GolubVanLoan.Chapter03
