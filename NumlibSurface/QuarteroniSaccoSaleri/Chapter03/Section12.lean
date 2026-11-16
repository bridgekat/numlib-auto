/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.Refinement
import Numlib.LinearAlgebra.Matrix.Complexify
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section11

/-!
# Quarteroni, Sacco and Saleri, Section 3.12: Improving the accuracy of GEM

This module formalizes Section 3.12 of [quarteroni2000numerical], on two ways to improve the
accuracy of Gaussian elimination for a linear system $Ax = b$ with $A \in \mathbb{R}^{n \times n}$.
The first is scaling: the system is replaced by $(D_1 A D_2) y = D_1 b$ with nonsingular diagonal
matrices $D_1, D_2$ and $y = D_2^{-1} x$. Remark 3.7 introduces the Skeel condition numbers
$\operatorname{cond}(A) = \| |A^{-1}|\,|A| \|_\infty$ and $\operatorname{cond}(A, x) = \|
|A^{-1}|\,|A|\,|x| \|_\infty / \|x\|_\infty$, which are invariant under row scaling. The second is
iterative refinement: from an iterate $x^{(i)}$, compute the residual $r^{(i)} = b - A x^{(i)}$,
solve $A z = r^{(i)}$ approximately by $z = C r^{(i)}$, and set $x^{(i+1)} = x^{(i)} + z$. In the
book $C = (\hat L \hat U)^{-1}$ is the solve with the computed LU factors.

In exact arithmetic the error obeys $x^{(k)} - x = (I - CA)^k (x^{(0)} - x)$, and the iteration
converges for every right-hand side if and only if $\rho(I - CA) < 1$. In floating-point arithmetic
the two convergence statements of the book, for fixed-precision and for mixed-precision refinement,
are stated in the rigorous form of Theorems 12.2 and 12.1 of [higham2002accuracy]: the relative
error contracts by an explicit factor $\rho < 1$ at each step, up to an explicit floor. The proofs
specialize the backbone modules `Numlib.Direct.Refinement`,
`Numlib.Conditioning.LinearSystem.Componentwise` and `Numlib.LinearAlgebra.Matrix.Complexify`.

## Main definitions

* Section 3.12.2, `QuarteroniSaccoSaleri.Chapter03.iterativeRefinementStep`: one step
  $x \mapsto x + C(b - Ax)$ of iterative refinement with an approximate inverse $C$.

## Main results

* Section 3.12.1, `QuarteroniSaccoSaleri.Chapter03.scaledSystem`: $Ax = b$ if and only if
  $(D_1 A D_2)(D_2^{-1} x) = D_1 b$, and if and only if $D_1 A x = D_1 b$.
* Remark 3.7, `QuarteroniSaccoSaleri.Chapter03.remark_3_7`: the formulas for the Skeel condition
  numbers $\operatorname{cond}(A)$ and $\operatorname{cond}(A, x)$.
* Remark 3.7, `QuarteroniSaccoSaleri.Chapter03.remark_3_7_iSup`: $\operatorname{cond}(A)$ is the
  supremum of $\operatorname{cond}(A, x)$ over $x \neq 0$.
* Remark 3.7, `QuarteroniSaccoSaleri.Chapter03.remark_3_7_scaling`: $\operatorname{cond}(A, x)$ does
  not change when $A$ is replaced by $DA$ for a nonsingular diagonal $D$.
* Section 3.12.2, `QuarteroniSaccoSaleri.Chapter03.iterativeRefinementStep_eq`: the refinement step
  is the stationary iteration $x \mapsto (I - CA)x + Cb$.
* Section 3.12.2, `QuarteroniSaccoSaleri.Chapter03.iterativeRefinement_exact`: with the exact
  inverse, or with an exact LU solve, one step gives the solution.
* Section 3.12.2, `QuarteroniSaccoSaleri.Chapter03.iterativeRefinement_convergence`: the error
  formula $x^{(k)} - x = (I - CA)^k (x^{(0)} - x)$, and convergence for every right-hand side if and
  only if $\rho(I - CA) < 1$.
* Section 3.12.2, `QuarteroniSaccoSaleri.Chapter03.iterativeRefinement_fixedPrecision`: in fixed
  precision, the relative error contracts by a factor $\rho < 1$ up to a floor of about
  $2(n + 1) \operatorname{cond}(A, x) u$.
* Section 3.12.2, `QuarteroniSaccoSaleri.Chapter03.iterativeRefinement_mixedPrecision`: in mixed
  precision, the relative error contracts by a factor $\rho < 1$ up to a floor of the order of $u$.

## Conventions

* A scaling matrix is `Matrix.diagonal d` for `d : Fin n → ℝ` with nonzero entries.
* The norms $\|\cdot\|_\infty$ are those of Section 3.1: the sup norm of `Fin n → ℝ` and the induced
  operator norm of matrices (`Matrix.Norms.Operator`). The Skeel condition numbers are the backbone
  definitions `Matrix.skeelCond` and `Matrix.skeelCondAt`.
* One step of iterative refinement is the map
  `QuarteroniSaccoSaleri.Chapter03.iterativeRefinementStep` applied to `C A b`. The iterate
  `(iterativeRefinementStep C A b)^[i] x₀` is the iterate of index $i$ from the initial vector
  $x^{(0)}$.
* The spectral radius of a real matrix is `Matrix.complexSpectralRadius`, as in Chapter 1.

## Implementation notes

* One step of iterative refinement in floating-point arithmetic (the exact error identity, its
  $\infty$-norm form and its form in the rounding model) is a general fact and is in the backbone:
  `Refinement.step_error`, `Refinement.norm_step_error_le` and `Refinement.step_error_fp`.
* The computed steps of the two finite-precision theorems are the backbone predicates
  `Refinement.RoundsStepLU` (residual in the working precision) and `Refinement.RoundsStepLUMixed`
  (residual in a second, finer rounding model, rounded once to the working precision). The two
  theorems specialize `Refinement.norm_sub_le_of_forall_roundsStepLU` and
  `Refinement.norm_sub_le_of_forall_roundsStepLUMixed`.

## Deviations from the source

* **Remark 3.7** (typo). The book prints $\operatorname{cond}(A, x) = \| |A^{-1}|\,A\,|x|\,x
  \|_\infty / \|x\|_\infty$. The library uses $\| |A^{-1}|\,|A|\,|x| \|_\infty / \|x\|_\infty$, the
  definition of Skeel and of [higham2002accuracy], §7.2. See
  `QuarteroniSaccoSaleri.Chapter03.remark_3_7`.
* **Section 3.12.2, convergence in exact arithmetic** (reading). The convergence of iterative
  refinement is stated as convergence of the iterates from every $x^{(0)}$ to one limit, for every
  $b$. See `QuarteroniSaccoSaleri.Chapter03.iterativeRefinement_convergence`.
* **Section 3.12.2, fixed-precision refinement** (reading). The display
  $\rho \simeq 2n \operatorname{cond}(A, x) u$ is not a proposition as printed. It is read as
  Theorem 12.2 of [higham2002accuracy], with explicit constants. See
  `QuarteroniSaccoSaleri.Chapter03.iterativeRefinement_fixedPrecision`.
* **Section 3.12.2, mixed-precision refinement** (reading). The display $\rho \simeq u$ is not a
  proposition as printed. It is read as Theorem 12.1 of [higham2002accuracy], with explicit
  constants. See `QuarteroniSaccoSaleri.Chapter03.iterativeRefinement_mixedPrecision`.

## Not formalized

* **Example 3.10**, a numerical run.
* **The heuristic estimate** $\|D_2^{-1}(\hat x - x)\| / \|D_2^{-1} x\| \simeq u K_\infty(D_1 A
  D_2)$, which is (3.69) for the scaled system.
* **The heuristic estimate** $K_\infty(A) \simeq \beta^{t(1 - 1/p)}$.
* **The stopping test** of step 4 of iterative refinement.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### Section 3.12.1: Scaling, and Remark 3.7 -/

/-- **Section 3.12.1** of [quarteroni2000numerical], scaling. Let $A \in \mathbb{R}^{n \times n}$
and $x, b \in \mathbb{R}^n$, and let $D_1 = \operatorname{diag}(d_1)$ and
$D_2 = \operatorname{diag}(d_2)$ have nonzero diagonal entries. $D_1$ scales the equations and
$D_2$ scales the unknowns. Then
$$Ax = b \iff (D_1 A D_2)\,(D_2^{-1} x) = D_1 b,$$
so that $Ax = b$ is equivalent to the scaled system $(D_1 A D_2) y = D_1 b$ with
$y = D_2^{-1} x$. Row scaling alone gives $Ax = b \iff D_1 A x = D_1 b$.

The proof specializes `Matrix.scaled_mulVec_eq_iff`. -/
theorem scaledSystem {d₁ d₂ : Fin n → ℝ} (h₁ : ∀ i, d₁ i ≠ 0) (h₂ : ∀ i, d₂ i ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (x b : Fin n → ℝ) :
    (A *ᵥ x = b ↔ (diagonal d₁ * A * diagonal d₂) *ᵥ ((diagonal d₂)⁻¹ *ᵥ x) = diagonal d₁ *ᵥ b) ∧
      (A *ᵥ x = b ↔ (diagonal d₁ * A) *ᵥ x = diagonal d₁ *ᵥ b) := by
  have hu : ∀ {d : Fin n → ℝ}, (∀ i, d i ≠ 0) → IsUnit (diagonal d) := fun hd => by
    rw [isUnit_iff_isUnit_det, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => hd i
  have hu₁ := hu h₁
  have hu₂ := hu h₂
  refine ⟨scaled_mulVec_eq_iff hu₁ hu₂ A x b, ?_⟩
  have h := scaled_mulVec_eq_iff hu₁ isUnit_one A x b
  rwa [Matrix.mul_one, inv_one, one_mulVec] at h

open scoped Matrix.Norms.Operator in
/-- **Remark 3.7** of [quarteroni2000numerical], the Skeel condition numbers. For
$A \in \mathbb{R}^{n \times n}$, the Skeel condition number of $A$ is
$$\operatorname{cond}(A) = \| |A^{-1}|\,|A| \|_\infty,$$
and for every $x \in \mathbb{R}^n$ the Skeel condition number of the system is
$$\operatorname{cond}(A, x) = \frac{\| |A^{-1}|\,|A|\,|x| \|_\infty}{\|x\|_\infty}.$$
Here $|M|$ is the matrix of the absolute values of the entries of $M$.

**Typo.** The book prints $\operatorname{cond}(A, x) = \| |A^{-1}|\,A\,|x|\,x \|_\infty /
\|x\|_\infty$. The intended formula restores the absolute values of $A$ and removes the extra
$x$, as in the definition of Skeel and in [higham2002accuracy], §7.2.

The two numbers are `Matrix.skeelCond A` and `Matrix.skeelCondAt A x`. At $x = 0$ the quotient
is $0 / 0 = 0$ in Lean. -/
theorem remark_3_7 (A : Matrix (Fin n) (Fin n) ℝ) :
    skeelCond A = ‖A⁻¹.abs * A.abs‖ ∧
      ∀ x : Fin n → ℝ, skeelCondAt A x = ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ / ‖x‖ :=
  ⟨by rw [skeelCond], fun x => by rw [skeelCondAt]⟩

/-- **Remark 3.7** of [quarteroni2000numerical], $\operatorname{cond}(A) = \sup_{x \neq 0}
\operatorname{cond}(A, x)$. Let $A \in \mathbb{R}^{n \times n}$ with $n \ge 1$. Then the Skeel
condition number $\operatorname{cond}(A)$ is the supremum of $\operatorname{cond}(A, x)$ over
all nonzero $x \in \mathbb{R}^n$.

The proof specializes `Matrix.skeelCond_eq_iSup_skeelCondAt`, whose supremum is over all $x$.
The value $\operatorname{cond}(A, 0) = 0$ does not change this supremum. -/
theorem remark_3_7_iSup [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    skeelCond A = ⨆ x : {x : Fin n → ℝ // x ≠ 0}, skeelCondAt A x := by
  rw [skeelCond_eq_iSup_skeelCondAt]
  have hbdd : BddAbove (Set.range fun x : Fin n → ℝ => skeelCondAt A x) :=
    ⟨skeelCond A, by rintro _ ⟨x, rfl⟩; exact skeelCondAt_le_skeelCond x⟩
  have hbdd' : BddAbove (Set.range fun x : {x : Fin n → ℝ // x ≠ 0} => skeelCondAt A x) :=
    ⟨skeelCond A, by rintro _ ⟨x, rfl⟩; exact skeelCondAt_le_skeelCond x.1⟩
  have hne : Nonempty {x : Fin n → ℝ // x ≠ 0} := ⟨⟨Pi.single 0 1, by simp⟩⟩
  refine le_antisymm (ciSup_le fun x => ?_) (ciSup_le fun x => le_ciSup hbdd x.1)
  rcases eq_or_ne x 0 with rfl | hx
  · refine le_ciSup_of_le hbdd' hne.some ?_
    rw [skeelCondAt, norm_zero, div_zero]
    exact skeelCondAt_nonneg _
  · exact le_ciSup hbdd' ⟨x, hx⟩

/-- **Remark 3.7** of [quarteroni2000numerical], invariance under row scaling. Let
$A \in \mathbb{R}^{n \times n}$, $x \in \mathbb{R}^n$, and let $D = \operatorname{diag}(d)$ have
nonzero diagonal entries. Then
$$\operatorname{cond}(DA, x) = \operatorname{cond}(A, x).$$
The condition number $K(A)$ does not have this property.

The proof specializes `Matrix.skeelCondAt_diagonal_mul`. -/
theorem remark_3_7_scaling {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : skeelCondAt (diagonal d * A) x = skeelCondAt A x :=
  skeelCondAt_diagonal_mul hd x

/-! ### Section 3.12.2: Iterative refinement -/

section Refinement

variable (C A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)

/-- **Section 3.12.2** of [quarteroni2000numerical], one step of iterative refinement (steps 1 to
3). Let $C, A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$. From the current iterate
$x^{(i)}$, compute the residual $r^{(i)} = b - A x^{(i)}$, solve $Az = r^{(i)}$ approximately by
$z = C r^{(i)}$, and set
$$x^{(i+1)} = x^{(i)} + C\,(b - A x^{(i)}).$$

In the book $C = (\hat L \hat U)^{-1}$ is the solve with the computed LU factors of $A$. This
definition is the matrix form of the backbone `Refinement.step`; see
`QuarteroniSaccoSaleri.Chapter03.iterativeRefinementStep_eq`. -/
noncomputable def iterativeRefinementStep (x : Fin n → ℝ) : Fin n → ℝ :=
  x + C *ᵥ (b - A *ᵥ x)

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **Section 3.12.2** of [quarteroni2000numerical], the refinement step as a stationary iteration.
Let $C, A \in \mathbb{R}^{n \times n}$, $b, x \in \mathbb{R}^n$ and $1 \le p \le \infty$. The
refinement step from $x$, viewed in $\ell^p$, is the backbone step `Refinement.step` for the
operators of $C$ and $A$, and
$$x + C(b - Ax) = (I - CA)\,x + Cb.$$

The operators are `Matrix.lpCLM p C` and `Matrix.lpCLM p A` on `PiLp p (fun _ : Fin n => ℝ)`.
The second equality specializes `Refinement.step_eq_stationary_step`. -/
theorem iterativeRefinementStep_eq (x : Fin n → ℝ) :
    toLp p (iterativeRefinementStep C A b x) =
        Refinement.step (lpCLM p C) (lpCLM p A) (toLp p b) (toLp p x) ∧
      iterativeRefinementStep C A b x = (1 - C * A) *ᵥ x + C *ᵥ b := by
  constructor
  · rw [Refinement.step, lpCLM_apply, lpCLM_apply, ofLp_toLp, iterativeRefinementStep, toLp_add]
    rfl
  · rw [iterativeRefinementStep, sub_mulVec, one_mulVec, mulVec_sub, mulVec_mulVec]
    abel

/-- The iterates of the refinement step, viewed in $\ell^p$, are the iterates of the backbone step
`Refinement.step`. -/
private theorem toLp_iterate (x₀ : Fin n → ℝ) (k : ℕ) :
    toLp p ((iterativeRefinementStep C A b)^[k] x₀) =
      (Refinement.step (lpCLM p C) (lpCLM p A) (toLp p b))^[k] (toLp p x₀) :=
  (Function.Semiconj.iterate_right (fun x => (iterativeRefinementStep_eq C A b p x).1) k) x₀

variable {C A b}

/-- **Section 3.12.2** of [quarteroni2000numerical], exactness: "in absence of rounding errors, the
process would stop at the first step, yielding the exact solution". Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular and let $x^* \in \mathbb{R}^n$ solve $Ax^* = b$.
Then for every $x \in \mathbb{R}^n$:

* one refinement step from $x$ with $C = A^{-1}$ gives $x^*$;
* for every LU factorization $A = LU$ (with $L$ unit lower triangular and $U$ upper triangular)
  whose pivots $u_{ii}$ are nonzero, $x + U^{-1}(L^{-1}(b - Ax)) = x^*$, where the solve is by
  forward and backward substitution.

The LU factorization is `Matrix.IsLU A L U`, and the solve is `Matrix.luSolve L U`. The proof
specializes `Refinement.step_eq_of_eq_inverse` and `Matrix.mulVec_luSolve`. -/
theorem iterativeRefinement_exact (hA : IsUnit A) {xs : Fin n → ℝ} (hxs : A *ᵥ xs = b)
    (x : Fin n → ℝ) :
    iterativeRefinementStep A⁻¹ A b x = xs ∧
      ∀ L U : Matrix (Fin n) (Fin n) ℝ, IsLU A L U → (∀ i, U i i ≠ 0) →
        x + luSolve L U (b - A *ᵥ x) = xs := by
  have hAd := (isUnit_iff_isUnit_det A).1 hA
  have h1 : iterativeRefinementStep A⁻¹ A b x = xs := by
    refine toLp_injective 2 ?_
    rw [(iterativeRefinementStep_eq A⁻¹ A b 2 x).1]
    refine Refinement.step_eq_of_eq_inverse ?_ (xs := toLp 2 xs) ?_ _
    · rw [← lpCLM_mul, nonsing_inv_mul _ hAd, lpCLM_one]
    · rw [lpCLM_apply, ofLp_toLp, hxs]
  refine ⟨h1, fun L U h hd => ?_⟩
  have hz : luSolve L U (b - A *ᵥ x) = A⁻¹ *ᵥ (b - A *ᵥ x) := by
    have := mulVec_luSolve (b - A *ᵥ x) h hd
    calc luSolve L U (b - A *ᵥ x) = A⁻¹ *ᵥ (A *ᵥ luSolve L U (b - A *ᵥ x)) :=
          (nonsing_inv_mulVec_mulVec hA _).symm
      _ = A⁻¹ *ᵥ (b - A *ᵥ x) := by rw [this]
  rw [hz]
  exact h1

/-- **Section 3.12.2** of [quarteroni2000numerical], convergence in exact arithmetic. Let
$C, A \in \mathbb{R}^{n \times n}$ and $1 \le p \le \infty$, and let $x^{(k)}$ be the iterates
of iterative refinement with the approximate inverse $C$ from $x^{(0)}$.

* For every $b$ and every solution $x^*$ of $Ax^* = b$, and for all $x^{(0)}$ and $k$,
$$x^{(k)} - x^* = (I - CA)^k (x^{(0)} - x^*), \qquad \|x^{(k)} - x^*\|_p \le \|I - CA\|_p^k\,
  \|x^{(0)} - x^*\|_p.$$
* The following are equivalent: for every $b \in \mathbb{R}^n$ there is an $x$ such that the
  iterates converge to $x$ from every $x^{(0)}$; and $\rho(I - CA) < 1$.

**Reading.** The formal statement reads the convergence of iterative refinement as convergence
of the iterates from every start to one and the same limit, for every right-hand side. The
backbone `Refinement.forall_tendsto_iff_spectralRadius_lt_one` lets the limit depend on the
start, and needs $C$ to be onto instead: for $C = 0$ every iterate equals $x^{(0)}$, so the
iterates converge, but $\rho(I) = 1$.

The norm $\|I - CA\|_p$ is `Matrix.lpOpNorm p (1 - C * A)`, and $\rho$ is
`Matrix.complexSpectralRadius`. The proof specializes `Refinement.iterate_sub_eq`,
`Refinement.norm_iterate_sub_le` and Theorem 1.5 of Chapter 1
(`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`). -/
theorem iterativeRefinement_convergence (C A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ (b xs : Fin n → ℝ), A *ᵥ xs = b → ∀ (x₀ : Fin n → ℝ) (k : ℕ),
      (iterativeRefinementStep C A b)^[k] x₀ - xs = ((1 - C * A) ^ k) *ᵥ (x₀ - xs) ∧
        ‖toLp p ((iterativeRefinementStep C A b)^[k] x₀ - xs)‖ ≤
          lpOpNorm p (1 - C * A) ^ k * ‖toLp p (x₀ - xs)‖) ∧
    ((∀ b : Fin n → ℝ, ∃ x, ∀ x₀,
        Tendsto (fun k => (iterativeRefinementStep C A b)^[k] x₀) atTop (𝓝 x)) ↔
      complexSpectralRadius (1 - C * A) < 1) := by
  refine ⟨fun b xs hxs x₀ k => ⟨Refinement.iterate_sub_eq_mulVec C A hxs x₀ k, ?_⟩, ?_⟩
  · have h := Refinement.norm_iterate_sub_le (C := lpCLM p C) (A := lpCLM p A) (b := toLp p b)
      (xs := toLp p xs) (by rw [lpCLM_apply, ofLp_toLp, hxs]) (toLp p x₀) k
    rw [← toLp_iterate, ← toLp_sub, ← toLp_sub, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub] at h
    exact h
  · exact Refinement.forall_exists_forall_tendsto_iff_complexSpectralRadius_lt_one C A

end Refinement

/-! ### Section 3.12.2: Iterative refinement in finite precision -/

section FinitePrecision

open FloatingPoint
open scoped Matrix.Norms.Operator

variable [NeZero n] {m : RoundingModel ℝ} {A L U : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ}

/-- Division of a recursion $a_{k+1} \le \rho a_k + \varphi c$ by a number $c > 0$. -/
private theorem div_recursion {a : ℕ → ℝ} {ρ φ c : ℝ} (hc : 0 < c)
    (h : ∀ k, a (k + 1) ≤ ρ * a k + φ * c) (k : ℕ) : a (k + 1) / c ≤ ρ * (a k / c) + φ :=
  (div_le_div_of_nonneg_right (h k) hc.le).trans_eq
    (by rw [add_div, mul_div_assoc, mul_div_assoc, div_self hc.ne', mul_one])

/-- **Section 3.12.2** of [quarteroni2000numerical], fixed-precision iterative refinement, in the
form of Theorem 12.2 of [higham2002accuracy]. Let $n \ge 1$, and consider a floating-point
arithmetic with roundoff unit $u$ such that $3nu < 1$. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular, and let $Ax = b$ with $x \neq 0$. Let $\hat L$, $\hat U$ be the computed LU factors
of $A$, with nonzero pivots $\hat u_{jj}$. Let $x^{(0)}, x^{(1)}, \dots$ be iterates of
refinement (steps 1 to 3) computed in this arithmetic, with the residual in the working
precision. Let $\gamma_k = ku / (1 - ku)$, let $\operatorname{cond}(A)$ and
$\operatorname{cond}(A, x)$ be the Skeel condition numbers of Remark 3.7, and put
$$\theta = \gamma_{3n} \| |A^{-1}|\,|\hat L|\,|\hat U| \|_\infty, \qquad \rho = \frac{\theta +
  \gamma_{n+1} \operatorname{cond}(A)}{1 - 2u - \theta}, \qquad \varphi = \frac{2 \gamma_{n+1}
  \operatorname{cond}(A, x) + u(1 + \theta)}{1 - 2u - \theta}.$$
If $2\theta + \gamma_{n+1} \operatorname{cond}(A) + 2u < 1$, then $\rho < 1$, and with
$e_i = \|x - x^{(i)}\|_\infty / \|x\|_\infty$:
$$e_{i+1} \le \rho\, e_i + \varphi \quad \text{for all } i, \qquad e_k \le \rho^k e_0 +
  \frac{\varphi}{1 - \rho} \quad \text{for all } k, \qquad \limsup_{k \to \infty} e_k \le
  \frac{\varphi}{1 - \rho}.$$

**Reading.** The book states that the relative error decreases with
$\rho \simeq 2n \operatorname{cond}(A, x) u$, if $\| |A^{-1}|\,|\hat L|\,|\hat U| \|_\infty$ is
sufficiently small. This is not a proposition as printed: it uses $\simeq$, and "sufficiently
small" has no quantifier. The formal statement is Theorem 12.2 of [higham2002accuracy], the
source that the book cites. "Sufficiently small" is the hypothesis $2\theta + \gamma_{n+1}
\operatorname{cond}(A) + 2u < 1$, and $\simeq$ is replaced by the explicit constants. The book's
$2n \operatorname{cond}(A, x) u$ is the limiting accuracy: the floor $\varphi$ is approximately
$2(n + 1) \operatorname{cond}(A, x) u$. The contraction factor $\rho$ is approximately $u \|
|A^{-1}| (3n |\hat L|\,|\hat U| + (n + 1) |A|) \|_\infty$, the number $\eta$ of
[higham2002accuracy].

The proof specializes `Refinement.norm_sub_le_of_forall_roundsStepLU`. The computed factors
satisfy `FloatingPoint.RoundsLU m A L U`, each computed step satisfies `Refinement.RoundsStepLU`,
and `FloatingPoint.gamma m.u k` is the constant $\gamma_k$. -/
theorem iterativeRefinement_fixedPrecision (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hx0 : x ≠ 0) (hLU : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0)
    {xs : ℕ → Fin n → ℝ} (hstep : ∀ i, Refinement.RoundsStepLU m A L U b (xs i) (xs (i + 1)))
    {θ ρ φ : ℝ} (hθ : θ = gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖)
    (hρ : ρ = (θ + gamma m.u (n + 1) * skeelCond A) / (1 - 2 * m.u - θ))
    (hφ : φ = (2 * gamma m.u (n + 1) * skeelCondAt A x + m.u * (1 + θ)) / (1 - 2 * m.u - θ))
    (hsmall : 2 * θ + gamma m.u (n + 1) * skeelCond A + 2 * m.u < 1) :
    ρ < 1 ∧ (∀ i, ‖x - xs (i + 1)‖ / ‖x‖ ≤ ρ * (‖x - xs i‖ / ‖x‖) + φ) ∧
      (∀ k, ‖x - xs k‖ / ‖x‖ ≤ ρ ^ k * (‖x - xs 0‖ / ‖x‖) + φ / (1 - ρ)) ∧
      limsup (fun k => ‖x - xs k‖ / ‖x‖) atTop ≤ φ / (1 - ρ) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hφx : φ * ‖x‖ = (2 * gamma m.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
      + m.u * (1 + θ) * ‖x‖) / (1 - 2 * m.u - θ) := by
    rw [hφ, skeelCondAt, div_mul_eq_mul_div]
    congr 1
    field_simp
  obtain ⟨hρ1, hrec, -, -⟩ := Refinement.norm_sub_le_of_forall_roundsStepLU (ρ := ρ)
    (φ := φ * ‖x‖) hcard hA hx hLU hd hstep hθ (by rw [hρ, skeelCond]) hφx
    (by rw [skeelCond] at hsmall; exact hsmall)
  have hθ0 : 0 ≤ θ := by
    rw [hθ]; exact mul_nonneg (gamma_nonneg m.u_nonneg hcard) (norm_nonneg _)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hcard1 : ((n + 1 : ℕ) : ℝ) * m.u < 1 := by
    have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ 3 * n)
    nlinarith [m.u_nonneg]
  have hγ1 := gamma_nonneg m.u_nonneg hcard1
  have hc0 : 0 ≤ skeelCond A := by rw [skeelCond]; exact norm_nonneg _
  have hcx0 := skeelCondAt_nonneg (A := A) x
  have hu0 := m.u_nonneg
  have hpos : 0 < 1 - 2 * m.u - θ := by linarith [mul_nonneg hγ1 hc0]
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hφ0 : 0 ≤ φ := by rw [hφ]; positivity
  have hrec' : ∀ i, ‖x - xs (i + 1)‖ / ‖x‖ ≤ ρ * (‖x - xs i‖ / ‖x‖) + φ :=
    div_recursion (a := fun k => ‖x - xs k‖) hxn hrec
  refine ⟨hρ1, hrec', fun k =>
    Refinement.le_pow_mul_add_div_of_forall_le_mul_add (a := fun k => ‖x - xs k‖ / ‖x‖) hρ0 hρ1
      hφ0 hrec' k, ?_⟩
  exact Refinement.limsup_le_div_of_forall_le_mul_add hρ0 hρ1 hφ0 (fun k => by positivity) hrec'

/-- **Section 3.12.2** of [quarteroni2000numerical], mixed-precision iterative refinement, in the
form of Theorem 12.1 of [higham2002accuracy]. Let $n \ge 1$, and consider a working
floating-point arithmetic with roundoff unit $u$ such that $3nu < 1$, and a second, finer
arithmetic with roundoff unit $\bar u$ such that $(n + 1) \bar u < 1$. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, and let $Ax = b$ with $x \neq 0$. Let $\hat L$,
$\hat U$ be the LU factors of $A$ computed in the working arithmetic, with nonzero pivots
$\hat u_{jj}$. Let $x^{(0)}, x^{(1)}, \dots$ be iterates of refinement (steps 1 to 3) computed
in the working arithmetic, except that the residual $r^{(i)} = b - Ax^{(i)}$ is computed in the
finer arithmetic and then rounded once to the working precision. Let $\gamma_k = ku / (1 - ku)$
and $\bar\gamma_k = k \bar u / (1 - k \bar u)$, and put
$$\theta = \gamma_{3n} \| |A^{-1}|\,|\hat L|\,|\hat U| \|_\infty, \qquad \rho = \frac{\theta +
  (u + (1 + u) \bar\gamma_{n+1}) \operatorname{cond}(A)}{1 - 2u - \theta}, \qquad \varphi =
  \frac{2(1 + u) \bar\gamma_{n+1} \operatorname{cond}(A, x) + u(1 + \theta)}{1 - 2u - \theta}.$$
If $2\theta + (u + (1 + u) \bar\gamma_{n+1}) \operatorname{cond}(A) + 2u < 1$, then $\rho < 1$,
and with $e_i = \|x - x^{(i)}\|_\infty / \|x\|_\infty$:
$$e_{i+1} \le \rho\, e_i + \varphi \quad \text{for all } i, \qquad e_k \le \rho^k e_0 +
  \frac{\varphi}{1 - \rho} \quad \text{for all } k, \qquad \limsup_{k \to \infty} e_k \le
  \frac{\varphi}{1 - \rho}.$$
Moreover, if the finer arithmetic has double the working precision, $\bar u \le u^2$, and
$2(n + 1) \bar u \le 1$, then
$$\varphi \le \frac{u \left(1 + \theta + 4(1 + u)(n + 1)\, u \operatorname{cond}(A,
  x)\right)}{1 - 2u - \theta}.$$

**Reading.** The book states that the relative error decreases with $\rho \simeq u$,
independently of the condition number of $A$. This is not a proposition as printed. The formal
statement is Theorem 12.1 of [higham2002accuracy], the source that the book cites, with explicit
constants in place of $\simeq$. The book's $u$ is the limiting accuracy: by the last bound, the
floor $\varphi$ is of the order of $u$ and, to first order in $u$, independent of the condition
number.

Each computed step satisfies `Refinement.RoundsStepLUMixed`, a predicate with the two rounding
models. The proof specializes `Refinement.norm_sub_le_of_forall_roundsStepLUMixed`. -/
theorem iterativeRefinement_mixedPrecision {m' : RoundingModel ℝ}
    (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) (hcard' : ((n + 1 : ℕ) : ℝ) * m'.u < 1) (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hx0 : x ≠ 0) (hLU : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0)
    {xs : ℕ → Fin n → ℝ}
    (hstep : ∀ i, Refinement.RoundsStepLUMixed m m' A L U b (xs i) (xs (i + 1)))
    {θ ρ φ : ℝ} (hθ : θ = gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖)
    (hρ : ρ = (θ + (m.u + (1 + m.u) * gamma m'.u (n + 1)) * skeelCond A) / (1 - 2 * m.u - θ))
    (hφ : φ = (2 * (1 + m.u) * gamma m'.u (n + 1) * skeelCondAt A x + m.u * (1 + θ))
      / (1 - 2 * m.u - θ))
    (hsmall : 2 * θ + (m.u + (1 + m.u) * gamma m'.u (n + 1)) * skeelCond A + 2 * m.u < 1) :
    ρ < 1 ∧ (∀ i, ‖x - xs (i + 1)‖ / ‖x‖ ≤ ρ * (‖x - xs i‖ / ‖x‖) + φ) ∧
      (∀ k, ‖x - xs k‖ / ‖x‖ ≤ ρ ^ k * (‖x - xs 0‖ / ‖x‖) + φ / (1 - ρ)) ∧
      limsup (fun k => ‖x - xs k‖ / ‖x‖) atTop ≤ φ / (1 - ρ) ∧
      (m'.u ≤ m.u ^ 2 → 2 * ((n + 1 : ℕ) * m'.u) ≤ 1 →
        φ ≤ m.u * (1 + θ + 4 * (1 + m.u) * (n + 1) * m.u * skeelCondAt A x)
          / (1 - 2 * m.u - θ)) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hφx : φ * ‖x‖ = (2 * (1 + m.u) * gamma m'.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
      + m.u * (1 + θ) * ‖x‖) / (1 - 2 * m.u - θ) := by
    rw [hφ, skeelCondAt, div_mul_eq_mul_div]
    congr 1
    field_simp
  obtain ⟨hρ1, hrec, -, -, hfloor⟩ := Refinement.norm_sub_le_of_forall_roundsStepLUMixed (ρ := ρ)
    (φ := φ * ‖x‖) hcard hcard' hA hx hLU hd hstep hθ (by rw [hρ, skeelCond]) hφx
    (by rw [skeelCond] at hsmall; exact hsmall)
  have hθ0 : 0 ≤ θ := by
    rw [hθ]; exact mul_nonneg (gamma_nonneg m.u_nonneg hcard) (norm_nonneg _)
  have hγ1 := gamma_nonneg m'.u_nonneg hcard'
  have hc0 : 0 ≤ skeelCond A := by rw [skeelCond]; exact norm_nonneg _
  have hcx0 := skeelCondAt_nonneg (A := A) x
  have hu0 := m.u_nonneg
  have hpos : 0 < 1 - 2 * m.u - θ := by
    have : 0 ≤ (m.u + (1 + m.u) * gamma m'.u (n + 1)) * skeelCond A := by positivity
    linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hφ0 : 0 ≤ φ := by rw [hφ]; positivity
  have hrec' : ∀ i, ‖x - xs (i + 1)‖ / ‖x‖ ≤ ρ * (‖x - xs i‖ / ‖x‖) + φ :=
    div_recursion (a := fun k => ‖x - xs k‖) hxn hrec
  refine ⟨hρ1, hrec', fun k =>
    Refinement.le_pow_mul_add_div_of_forall_le_mul_add (a := fun k => ‖x - xs k‖ / ‖x‖) hρ0 hρ1
      hφ0 hrec' k,
    Refinement.limsup_le_div_of_forall_le_mul_add hρ0 hρ1 hφ0 (fun k => by positivity) hrec',
    fun hu2 hn2 => ?_⟩
  have h := hfloor hu2 hn2
  have hcx : ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ = skeelCondAt A x * ‖x‖ := by
    rw [skeelCondAt, div_mul_cancel₀ _ hxn.ne']
  rw [hcx] at h
  have h' : φ * ‖x‖ ≤ (m.u * (1 + θ + 4 * (1 + m.u) * (n + 1) * m.u * skeelCondAt A x)
      / (1 - 2 * m.u - θ)) * ‖x‖ := by
    refine h.trans (le_of_eq ?_)
    rw [div_mul_eq_mul_div]
    congr 1
    ring
  exact le_of_mul_le_mul_right h' hxn

end FinitePrecision

end QuarteroniSaccoSaleri.Chapter03
