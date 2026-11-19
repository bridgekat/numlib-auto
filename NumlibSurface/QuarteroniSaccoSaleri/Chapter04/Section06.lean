/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Conditioning.LinearSystem
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 4.6: Stopping Criteria

This module formalizes Section 4.6 of [quarteroni2000numerical]. The setting is the linear iterative
method $x^{(k+1)} = B x^{(k)} + f$ of (4.2), consistent with $Ax = b$ in the sense of Definition
4.1, with solution $x = A^{-1} b$ and errors $e^{(k)} = x^{(k)} - x$. The error after $k$ steps
satisfies $\|e^{(k)}\| \le \|B^k\| \|e^{(0)}\|$, so the iteration reaches the error reduction
$\|e^{(k)}\| \le \varepsilon \|e^{(0)}\|$ (4.68) once $\|B^k\| \le \varepsilon$, which amounts to
$k \ge -\log \varepsilon / R_k(B)$ (4.69). Section 4.6.1 bounds the error by the increment
$x^{(k+1)} - x^{(k)}$ when $\|B\| < 1$ (4.71)–(4.72). Section 4.6.2 bounds the error by the residual
$b - A x^{(k)}$, in absolute terms through $\|A^{-1}\|$ and in relative terms through the condition
number $K(A)$.

The proofs specialize the backbone modules `Numlib.Stationary.Basic` (the error and increment
recursions of the affine iteration, and the a priori and a posteriori bounds of the contraction
case) and `Numlib.Conditioning.LinearSystem` (the relation between residual and error through the
condition number).

## Main results

* Section 4.6, `QuarteroniSaccoSaleri.Chapter04.norm_error_le_convergenceFactor`:
  $\|e^{(k)}\| \le \|B^k\| \|e^{(0)}\|$.
* Equations (4.68)–(4.69), `QuarteroniSaccoSaleri.Chapter04.equation_4_69`:
  $\|B^k\| \le \varepsilon$ gives $\|e^{(k)}\| \le \varepsilon \|e^{(0)}\|$, and
  $\|B^k\| \le \varepsilon$ if and only if $k \ge -\log \varepsilon / R_k(B)$.
* Equation (4.71), `QuarteroniSaccoSaleri.Chapter04.equation_4_71`: $e^{(k+1)} = B e^{(k)}$ and
  $\|e^{(k+1)}\| \le \|B\| \|e^{(k)}\|$.
* Equation (4.72), `QuarteroniSaccoSaleri.Chapter04.equation_4_72`: if $\|B\| < 1$, then $\|x -
  x^{(k+1)}\| \le \|B\| / (1 - \|B\|) \, \|x^{(k+1)} - x^{(k)}\|$.
* Section 4.6.1, `QuarteroniSaccoSaleri.Chapter04.equation_4_72_apriori`: if $\|B\| < 1$, then
  $\|x - x^{(k+1)}\| \le \|B\|^{k+1} / (1 - \|B\|) \, \|x^{(1)} - x^{(0)}\|$.
* Section 4.6.1, `QuarteroniSaccoSaleri.Chapter04.increment_succ_le`: the ratio of two consecutive
  increments is at most $\|B\|$.
* Section 4.6.2, `QuarteroniSaccoSaleri.Chapter04.residual_stopping_abs`:
  $\|b - A y\| \le \varepsilon$ gives $\|x - y\| \le \|A^{-1}\| \varepsilon$.
* Section 4.6.2, `QuarteroniSaccoSaleri.Chapter04.residual_stopping_rel`:
  $\|b - A y\| / \|b\| \le \varepsilon$ gives $\|x - y\| / \|x\| \le K(A) \varepsilon$.

## Conventions

* The iteration is the linear method (4.2) of Section 4.1,
  `QuarteroniSaccoSaleri.Chapter04.affineStep B f`, and its $k$-th iterate from $x^{(0)}$ is
  `(affineStep B f)^[k] x₀`. Consistency is Definition 4.1,
  `QuarteroniSaccoSaleri.Chapter04.definition_4_1`.
* Vector norms are the Euclidean norm of `EuclideanSpace ℝ (Fin n)`, written `‖toLp 2 v‖`. Matrix
  norms are the spectral norm $\|\cdot\|_2$ (Mathlib's scoped `Matrix.Norms.L2Operator`), which is
  the operator norm that the Euclidean norm induces.
* The convergence factor $\|B^k\|$ and the average convergence rate $R_k(B)$ are those of Definition
  4.2, `QuarteroniSaccoSaleri.Chapter04.definition_4_2_factor` and
  `QuarteroniSaccoSaleri.Chapter04.definition_4_2_rate`.
* The condition number $K(A) = \|A\|_2 \|A^{-1}\|_2$ is `NormedRing.condNumber A` in the spectral
  norm.

## Implementation notes

* The backbone states the same bounds on any normed space with the induced operator norm, so nothing
  depends on the choice of the Euclidean norm.

## Deviations from the source

* **Totalization.** The error bounds use the Euclidean operator norm and include zero starting
  error. See `QuarteroniSaccoSaleri.Chapter04.norm_error_le_convergenceFactor`.
* **Reading.** The rate-based stopping equivalence states the domain of the real logarithmic
  calculation. See `QuarteroniSaccoSaleri.Chapter04.equation_4_69`.
* **Scope.** The increment error bounds use the Euclidean operator norm and explicit strict
  contraction. See `QuarteroniSaccoSaleri.Chapter04.equation_4_71`,
  `QuarteroniSaccoSaleri.Chapter04.equation_4_72`,
  `QuarteroniSaccoSaleri.Chapter04.equation_4_72_apriori`.
* **Totalization.** The increment ratio gives a lower bound on the operator norm, with
  zero-denominator totalization. See `QuarteroniSaccoSaleri.Chapter04.increment_succ_le`.
* **Scope.** The residual tests use Euclidean norms and require nonzero data for relative
  normalization. See `QuarteroniSaccoSaleri.Chapter04.residual_stopping_abs`,
  `QuarteroniSaccoSaleri.Chapter04.residual_stopping_rel`.
* **Equation (4.69)** (reading). It is stated for $k \ge 1$ with $0 < \|B^k\| < 1$ and
  $\varepsilon > 0$, the conditions under which both sides make sense. The book's "amounts to
  requiring" is the equivalence $\|B^k\| \le \varepsilon \iff k \ge -\log \varepsilon / R_k(B)$. See
  `QuarteroniSaccoSaleri.Chapter04.equation_4_69`.

## Not formalized

* **Equation (4.70) and the indicator (4.73).** The estimate
  $k_{\min} \simeq -\log \varepsilon / R(B)$ and the indicator are heuristics, which "should not be
  regarded as an upper bound".
* **Examples 4.11 and 4.12.** They are numerical.
* **The preconditioned residual test** $\|P^{-1} r^{(k)}\| / \|P^{-1} r^{(0)}\| \le \varepsilon$. It
  is a criterion, not a result.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}

/-- The Euclidean norm satisfies $\|x - y\| = \|y - x\|$. -/
private theorem norm_toLp_sub_rev (x y : Fin n → ℝ) :
    ‖(toLp 2 (x - y) : EuclideanSpace ℝ (Fin n))‖ =
      ‖(toLp 2 (y - x) : EuclideanSpace ℝ (Fin n))‖ := by
  rw [← norm_neg, ← toLp_neg, neg_sub]

/-! ### The convergence factor and the number of iterations, (4.68)–(4.69) -/

/-- **Section 4.6** of [quarteroni2000numerical], the first display. Let
$A, B \in \mathbb{R}^{n \times n}$ and $b, f \in \mathbb{R}^n$, and let the method
$x^{(k+1)} = B x^{(k)} + f$ be consistent with $Ax = b$, where $x = A^{-1} b$. Then for every
$x^{(0)}$ and $k$, the error $e^{(k)} = x^{(k)} - x$ satisfies
$$\|e^{(k)}\| \le \|B^k\| \, \|e^{(0)}\|, \qquad \frac{\|e^{(k)}\|}{\|e^{(0)}\|} \le \|B^k\|.$$
The convergence factor after $k$ steps thus estimates the reduction of the error.

The quotient is $0$ when $e^{(0)} = 0$. The first bound follows from (4.4). The proof
specializes the backbone's `Stationary.norm_step_iterate_sub_le`.

**Reading.** Lean uses the Euclidean operator norm and also states the relative bound with totalized
division when the starting error is zero.
-/
theorem norm_error_le_convergenceFactor (hc : definition_4_1 A b B f) (x₀ : Fin n → ℝ) (k : ℕ) :
    ‖(toLp 2 ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
        definition_4_2_factor B k * ‖(toLp 2 (x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ∧
      ‖(toLp 2 ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ /
        ‖(toLp 2 (x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤ definition_4_2_factor B k := by
  have h := Stationary.norm_step_iterate_sub_le (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B)
    (toLp 2 f) (toLp_fixed_of_consistent hc) (toLp 2 x₀) k
  rw [← toLp_affineStep_iterate, ← toLp_sub, ← toLp_sub, ← map_pow, l2_opNorm_toEuclideanCLM] at h
  exact ⟨h, div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) h⟩

/-- **Equations (4.68)–(4.69)** of [quarteroni2000numerical]. Let the method
$x^{(k+1)} = B x^{(k)} + f$ be consistent with $Ax = b$, where $x = A^{-1} b$, let
$x^{(0)} \in \mathbb{R}^n$, $k \in \mathbb{N}$ and $\varepsilon \in \mathbb{R}$. Then:

1. if $\|B^k\| \le \varepsilon$, then the error is reduced by the factor $\varepsilon$,
   $\|e^{(k)}\| \le \varepsilon \|e^{(0)}\|$ (4.68);
2. if $k \ge 1$, $0 < \|B^k\| < 1$ and $\varepsilon > 0$, then
   $\|B^k\| \le \varepsilon \iff k \ge -\log \varepsilon / R_k(B)$ (4.69).

Here $R_k(B) = -\frac{1}{k} \log \|B^k\|$ is the average convergence rate of Definition 4.2.

**Reading.** The book says that the condition $\|B^k\| \le \varepsilon$ "amounts to requiring"
(4.69). This is stated as an equivalence, under the conditions $k \ge 1$, $0 < \|B^k\| < 1$ and
$\varepsilon > 0$, under which $R_k(B) > 0$ and $\log \varepsilon$ is finite.

**Reading.** The logarithmic equivalence explicitly restricts to a positive iteration count, strict
contraction with nonzero norm, and positive tolerance. The first error implication does not need
logarithms.
-/
theorem equation_4_69 (hc : definition_4_1 A b B f) (x₀ : Fin n → ℝ) {k : ℕ} {ε : ℝ} :
    (definition_4_2_factor B k ≤ ε →
        ‖(toLp 2 ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
          ε * ‖(toLp 2 (x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖) ∧
      (k ≠ 0 → 0 < definition_4_2_factor B k → definition_4_2_factor B k < 1 → 0 < ε →
        (definition_4_2_factor B k ≤ ε ↔ -Real.log ε / definition_4_2_rate B k ≤ k)) := by
  refine ⟨fun hε => (norm_error_le_convergenceFactor hc x₀ k).1.trans
    (mul_le_mul_of_nonneg_right hε (norm_nonneg _)), fun hk h0 h1 hε => ?_⟩
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hlog : Real.log (definition_4_2_factor B k) < 0 := Real.log_neg h0 h1
  have hR : 0 < definition_4_2_rate B k := by
    rw [definition_4_2_rate, neg_mul, neg_pos]
    exact mul_neg_of_pos_of_neg (one_div_pos.mpr hk') hlog
  rw [div_le_iff₀ hR, definition_4_2_rate, definition_4_2_factor, show
    (k : ℝ) * (-(1 / k : ℝ) * Real.log ‖B ^ k‖) = -Real.log ‖B ^ k‖ by field_simp,
    neg_le_neg_iff]
  exact (Real.log_le_log_iff h0 hε).symm

/-! ### Section 4.6.1: a stopping test based on the increment -/

/-- **Equation (4.71)** of [quarteroni2000numerical]. Let the method $x^{(k+1)} = B x^{(k)} + f$ be
consistent with $Ax = b$, where $x = A^{-1} b$. Then for every $x^{(0)}$ and $k$, the errors
satisfy the recursion $e^{(k+1)} = B e^{(k)}$ of (4.4), and
$$\|e^{(k+1)}\| \le \|B\| \, \|e^{(k)}\|.$$

**Reading.** The norm bounds are specialized to the Euclidean operator norm. The denominators in the
increment estimates are positive by the explicit contraction assumption.
-/
theorem equation_4_71 (hc : definition_4_1 A b B f) (x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep B f)^[k + 1] x₀ - A⁻¹ *ᵥ b = B *ᵥ ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) ∧
      ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
        ‖B‖ * ‖(toLp 2 ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ := by
  have h : (affineStep B f)^[k + 1] x₀ - A⁻¹ *ᵥ b = B *ᵥ ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) := by
    rw [equation_4_4 hc, equation_4_4 hc, pow_succ', ← mulVec_mulVec]
  refine ⟨h, ?_⟩
  rw [h, ← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM]
  exact ContinuousLinearMap.le_opNorm _ _

/-- **Equation (4.72)** of [quarteroni2000numerical], the a posteriori increment test. Let the
method $x^{(k+1)} = B x^{(k)} + f$ be consistent with $Ax = b$, where $x = A^{-1} b$, and let
$\|B\| < 1$. Then for every $x^{(0)}$ and $k$,
$$\|x - x^{(k+1)}\| \le \frac{\|B\|}{1 - \|B\|} \, \|x^{(k+1)} - x^{(k)}\|.$$

The bound follows from the triangle inequality in (4.71), $\|e^{(k+1)}\| \le \|B\|
(\|e^{(k+1)}\| + \|x^{(k+1)} - x^{(k)}\|)$. The proof specializes the backbone's
`Stationary.norm_iterate_sub_le'`.

**Reading.** The norm bounds are specialized to the Euclidean operator norm. The denominators in the
increment estimates are positive by the explicit contraction assumption.
-/
theorem equation_4_72 (hc : definition_4_1 A b B f) (hB : ‖B‖ < 1) (x₀ : Fin n → ℝ) (k : ℕ) :
    ‖(toLp 2 (A⁻¹ *ᵥ b - (affineStep B f)^[k + 1] x₀) : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖B‖ / (1 - ‖B‖) *
        ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) :
          EuclideanSpace ℝ (Fin n))‖ := by
  have hG : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B‖ < 1 := by rwa [l2_opNorm_toEuclideanCLM]
  have h := Stationary.norm_iterate_sub_le' (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f) hG
    (toLp_fixed_of_consistent hc) (toLp 2 x₀) k
  rw [← toLp_affineStep_iterate, ← toLp_affineStep_iterate, ← toLp_sub, ← toLp_sub,
    l2_opNorm_toEuclideanCLM] at h
  rw [norm_toLp_sub_rev (A⁻¹ *ᵥ b)]
  exact h

/-- **Section 4.6.1** of [quarteroni2000numerical], the a priori form of (4.72), from the display
after (4.72). Let the method $x^{(k+1)} = B x^{(k)} + f$ be consistent with $Ax = b$, where
$x = A^{-1} b$, and let $\|B\| < 1$. Then for every $x^{(0)}$ and $k$,
$$\|x - x^{(k+1)}\| \le \frac{\|B\|^{k+1}}{1 - \|B\|} \, \|x^{(1)} - x^{(0)}\|.$$
This bound estimates the number of iterations that are needed to reach a given tolerance.

The proof specializes the backbone's `Stationary.norm_iterate_sub_le`.

**Reading.** The norm bounds are specialized to the Euclidean operator norm. The denominators in the
increment estimates are positive by the explicit contraction assumption.
-/
theorem equation_4_72_apriori (hc : definition_4_1 A b B f) (hB : ‖B‖ < 1) (x₀ : Fin n → ℝ)
    (k : ℕ) :
    ‖(toLp 2 (A⁻¹ *ᵥ b - (affineStep B f)^[k + 1] x₀) : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖B‖ ^ (k + 1) / (1 - ‖B‖) *
        ‖(toLp 2 ((affineStep B f)^[1] x₀ - x₀) : EuclideanSpace ℝ (Fin n))‖ := by
  have hG : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B‖ < 1 := by rwa [l2_opNorm_toEuclideanCLM]
  have h := Stationary.norm_iterate_sub_le (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f) hG
    (toLp_fixed_of_consistent hc) (toLp 2 x₀) (k + 1)
  rw [← toLp_affineStep_iterate, ← toLp_affineStep, ← toLp_sub, ← toLp_sub,
    l2_opNorm_toEuclideanCLM] at h
  rw [norm_toLp_sub_rev (A⁻¹ *ᵥ b), Function.iterate_one]
  exact h

/-- **Section 4.6.1** of [quarteroni2000numerical], the estimate of $\|B\|$. Let
$B \in \mathbb{R}^{n \times n}$ and $f, x^{(0)} \in \mathbb{R}^n$, and let $x^{(k)}$ be the
iterates of $x^{(k+1)} = B x^{(k)} + f$. Write $\delta_{j+1} = \|x^{(j+1)} - x^{(j)}\|$. Then
for every $k$,
$$x^{(k+2)} - x^{(k+1)} = B (x^{(k+1)} - x^{(k)}), \qquad \delta_{k+2} \le \|B\| \,
  \delta_{k+1}, \qquad \frac{\delta_{k+2}}{\delta_{k+1}} \le \|B\|.$$
So the ratio $c$ of two consecutive increments is a lower bound for $\|B\|$.

No consistency hypothesis is needed. The quotient is $0$ when $\delta_{k+1} = 0$. The proof
specializes the backbone's `Stationary.step_iterate_succ_sub`. The indicator
$\varepsilon^{(k+1)} = \delta_{k+1}^2 / (\delta_k - \delta_{k+1})$ of (4.73), which replaces
$\|B\|$ with $c$ in (4.72), is a heuristic and is not formalized.

**Reading.** The inequality for increment ratios uses total division when the previous increment
vanishes, and its cross-multiplied version is available. It does not use the ratio as an upper bound
on the error.
-/
theorem increment_succ_le (B : Matrix (Fin n) (Fin n) ℝ) (f x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀ =
        B *ᵥ ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) ∧
      ‖(toLp 2 ((affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀) :
          EuclideanSpace ℝ (Fin n))‖ ≤
        ‖B‖ * ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) :
          EuclideanSpace ℝ (Fin n))‖ ∧
      ‖(toLp 2 ((affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀) :
          EuclideanSpace ℝ (Fin n))‖ /
        ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) :
          EuclideanSpace ℝ (Fin n))‖ ≤ ‖B‖ := by
  have hinc : ∀ j, (affineStep B f)^[j + 1] x₀ - (affineStep B f)^[j] x₀ =
      (B ^ j) *ᵥ (affineStep B f x₀ - x₀) := fun j => by
    have h := Stationary.step_iterate_succ_sub (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f)
      (toLp 2 x₀) j
    rw [← toLp_affineStep_iterate, ← toLp_affineStep_iterate, ← toLp_affineStep, ← toLp_sub,
      ← toLp_sub, ← map_pow, toEuclideanCLM_toLp] at h
    exact toLp_injective 2 h
  have h : (affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀ =
      B *ᵥ ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) := by
    rw [hinc (k + 1), hinc k, pow_succ', ← mulVec_mulVec]
  have hle : ‖(toLp 2 ((affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀) :
      EuclideanSpace ℝ (Fin n))‖ ≤
      ‖B‖ * ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) :
        EuclideanSpace ℝ (Fin n))‖ := by
    rw [h, ← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM]
    exact ContinuousLinearMap.le_opNorm _ _
  exact ⟨h, hle, div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) hle⟩

/-! ### Section 4.6.2: a stopping test based on the residual -/

/-- **Section 4.6.2** of [quarteroni2000numerical], the first display. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $b, y \in \mathbb{R}^n$ (for example, an
iterate), and let $\varepsilon \in \mathbb{R}$. If the residual satisfies
$\|b - A y\| \le \varepsilon$, then
$$\|A^{-1} b - y\| \le \|A^{-1}\| \, \varepsilon.$$

The proof uses $A^{-1} b - y = A^{-1} (b - A y)$.

**Reading.** The error estimates apply to an arbitrary candidate iterate, in Euclidean norm. The
normalized test uses the Euclidean condition number and explicitly requires a nonzero right-hand
side.
-/
theorem residual_stopping_abs (hA : IsUnit A) (b y : Fin n → ℝ) {ε : ℝ}
    (hr : ‖(toLp 2 (b - A *ᵥ y) : EuclideanSpace ℝ (Fin n))‖ ≤ ε) :
    ‖(toLp 2 (A⁻¹ *ᵥ b - y) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖A⁻¹‖ * ε := by
  have h : A⁻¹ *ᵥ b - y = A⁻¹ *ᵥ (b - A *ᵥ y) := by
    rw [mulVec_sub, nonsing_inv_mulVec_mulVec hA]
  rw [h, ← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hr (norm_nonneg _))

/-- **Section 4.6.2** of [quarteroni2000numerical], the normalized residual test. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $b \in \mathbb{R}^n$ with $b \neq 0$, let
$y \in \mathbb{R}^n$ and $\varepsilon \in \mathbb{R}$, and let $x = A^{-1} b$. If
$\|b - A y\| / \|b\| \le \varepsilon$, then
$$\frac{\|x - y\|}{\|x\|} \le K(A) \, \varepsilon, \qquad K(A) = \|A\|_2 \|A^{-1}\|_2.$$

The proof passes through $\|x - y\| / \|x\| \le K(A) \|b - A y\| / \|b\|$. It specializes the
backbone's `relative_error_le_condNumber_mul_relative_residual` to the operator $x \mapsto Ax$
on `EuclideanSpace ℝ (Fin n)`.

**Reading.** The error estimates apply to an arbitrary candidate iterate, in Euclidean norm. The
normalized test uses the Euclidean condition number and explicitly requires a nonzero right-hand
side.
-/
theorem residual_stopping_rel (hA : IsUnit A) {b : Fin n → ℝ} (hb : b ≠ 0) (y : Fin n → ℝ)
    {ε : ℝ} (hr : ‖(toLp 2 (b - A *ᵥ y) : EuclideanSpace ℝ (Fin n))‖ /
      ‖(toLp 2 b : EuclideanSpace ℝ (Fin n))‖ ≤ ε) :
    ‖(toLp 2 (A⁻¹ *ᵥ b - y) : EuclideanSpace ℝ (Fin n))‖ /
        ‖(toLp 2 (A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
      NormedRing.condNumber A * ε := by
  have hu : IsUnit (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) := hA.map _
  set e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofUnit hu.unit with he_def
  have he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A := by
    ext x; rfl
  have hκ : NormedRing.condNumber (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      NormedRing.condNumber A := by
    rw [he, NormedRing.condNumber, NormedRing.condNumber, ← toEuclideanCLM_ringInverse hA,
      l2_opNorm_toEuclideanCLM, l2_opNorm_toEuclideanCLM]
  have hx : e (toLp 2 (A⁻¹ *ᵥ b)) = toLp 2 b := by
    change toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (toLp 2 (A⁻¹ *ᵥ b)) = toLp 2 b
    rw [toEuclideanCLM_toLp, mulVec_nonsing_inv_mulVec hA]
  have hb' : (toLp 2 b : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    rwa [Ne, toLp_eq_zero]
  have h := relative_error_le_condNumber_mul_relative_residual e (y := toLp 2 y) hx hb'
  rw [hκ] at h
  have hAy : e (toLp 2 y) = toLp 2 (A *ᵥ y) := by
    change toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (toLp 2 y) = toLp 2 (A *ᵥ y)
    rw [toEuclideanCLM_toLp]
  rw [hAy, ← toLp_sub, ← toLp_sub] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr (NormedRing.condNumber_nonneg _))

end QuarteroniSaccoSaleri.Chapter04
