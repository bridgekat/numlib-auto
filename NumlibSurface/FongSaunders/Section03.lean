/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CG
import Numlib.Krylov.CR
import Numlib.Krylov.Iterate
import Numlib.Krylov.Monotonicity
import NumlibSurface.FongSaunders.Section02

/-!
# Fong and Saunders, Section 3: Normwise relative backward errors and stopping rules

This module formalizes Section 3 of [fong2012cg]. The section measures an approximate solution $x_k$
of $Ax = b$ by the smallest perturbation $(A + E_k) x_k = b + f_k$ that $x_k$ solves exactly, with
$\|E_k\| / \|A\| \le \alpha \xi$ and $\|f_k\| / \|b\| \le \beta \xi$ for tolerances
$\alpha, \beta \ge 0$; the matrix norm is the Frobenius norm. The least such $\xi$ is the normwise
relative backward error
$$\xi_k = \frac{\|r_k\|}{\alpha \|A\| \|x_k\| + \beta \|b\|}, \qquad r_k = b - A x_k.$$

The module gives the definition (3.1) of an acceptable solution, the closed form (3.2) of $\xi_k$
with the weight $\phi_k = \beta \|b\| / (\alpha \|A\| \|x_k\| + \beta \|b\|)$, the optimal
perturbations (3.3), the stopping rule (3.4), the norms (3.5)–(3.6) of the optimal perturbations,
the remark of Section 3.2 that $\phi_k$ decreases for CG and MINRES, and Theorem 3.1: for MINRES,
and hence for CR, the relative backward errors $\|E_k\| / \|A\|$ and $\|f_k\| / \|b\|$ decrease
monotonically. The monotonicity results specialize `Numlib.Krylov.Monotonicity`, through Theorem 2.3
in `NumlibSurface.FongSaunders.Section02`.

## Main definitions

* Equation (3.1), `FongSaunders.IsAcceptable`: $x$ is an acceptable solution if $(A + E) x = b + f$
  for some $E$ and $f$ with $\|E\| / \|A\| \le \alpha$ and $\|f\| / \|b\| \le \beta$.
* Equation (3.2), `FongSaunders.nrbe`: the normwise relative backward error $\xi_k$.
* Equation (3.2), `FongSaunders.nrbePhi`: the weight $\phi_k$.
* Equation (3.3), `FongSaunders.nrbePertA`: the optimal matrix perturbation
  $E_k = \frac{1 - \phi_k}{\|x_k\|^2} r_k x_k^T$.
* Equation (3.3), `FongSaunders.nrbePertb`: the optimal right-hand-side perturbation
  $f_k = -\phi_k r_k$.

## Main results

* Equations (3.2)–(3.3), `FongSaunders.nrbePert_attains`: the perturbations $E_k$ and $f_k$ are
  feasible and attain the value $\xi_k$.
* Equation (3.2), `FongSaunders.nrbe_isLeast`: $\xi_k$ is the least $\xi$ for which a feasible
  perturbation exists.
* Equation (3.4), `FongSaunders.nrbe_le_one_iff`: $\xi_k \le 1$ if and only if
  $\|r_k\| \le \alpha \|A\| \|x_k\| + \beta \|b\|$.
* Section 3, `FongSaunders.isAcceptable_iff_nrbe_le_one`: $x_k$ is acceptable if and only if
  $\xi_k \le 1$.
* Equation (3.5), `FongSaunders.norm_nrbePertA`: $\|E_k\| = (1 - \phi_k) \|r_k\| / \|x_k\|$.
* Equation (3.6), `FongSaunders.norm_nrbePertb`: $\|f_k\| = \phi_k \|r_k\|$.
* Section 3.2, `FongSaunders.nrbePhi_cg_antitone` and `FongSaunders.nrbePhi_minres_antitone`:
  $\phi_k$ decreases monotonically for CG and for MINRES.
* Theorem 3.1, `FongSaunders.nrbe_minres_antitone` and `FongSaunders.nrbe_minres_antitoneOn`:
  $\xi_k$ decreases monotonically for MINRES.
* Theorem 3.1, `FongSaunders.theorem_3_1_minres` and `FongSaunders.theorem_3_1_cr`:
  $\|E_k\| / \|A\|$ and $\|f_k\| / \|b\|$ decrease monotonically for MINRES and for CR.
* Section 3, `FongSaunders.minres_stops_first`: under the stopping rule $\|r_k\| \le \beta \|b\|$,
  MINRES stops no later than CG.

## Conventions

* In this section $\alpha$ and $\beta$ are the tolerances of the stopping rule, not the coefficients
  of Table 2.1.
* The matrix norm $\|A\|$ is the Frobenius norm, from `open scoped Matrix.Norms.Frobenius`.

## Implementation notes

* The ratios $\|E\| / \|A\|$ and $\|f\| / \|b\|$ are written as divisions, with Lean's convention
  $t / 0 = 0$. The definitions of $\xi_k$, $\phi_k$ and $E_k$ are also divisions: each is $0$ when
  its denominator is $0$, and in particular $E_k = 0$ for $x_k = 0$.
* The backbone proves the Rigal–Gaches theorem in `Numlib.Conditioning.LinearSystem` for the
  operator norm. The surface proves it again for the Frobenius norm.

## Deviations from the source

* **Nonzero data in the backward-error results** (reading). The ratios $\|E\| / \|A\|$ and
  $\|f\| / \|b\|$ presuppose $A \neq 0$ and $b \neq 0$, which the paper leaves implicit; the results
  state them. See `FongSaunders.nrbePert_attains`, `FongSaunders.nrbe_isLeast` and
  `FongSaunders.isAcceptable_iff_nrbe_le_one`.
* **Theorem 3.1, the rows that divide by $\|x_k\|$** (reading). The paper's $E_0$ is undefined
  because $x_0 = 0$; the decrease of $\|E_k\| / \|A\|$, and of $\xi_k$ when $\beta = 0$, is stated
  for $k \ge 1$. See `FongSaunders.theorem_3_1_minres`, `FongSaunders.theorem_3_1_cr` and
  `FongSaunders.nrbe_minres_antitoneOn`.
-/

namespace FongSaunders

open Krylov Matrix

open scoped Matrix.Norms.Frobenius

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Vec n} {α β : ℝ}

/-!
### Linearity of the product in the matrix, and two facts on the Frobenius norm

The backbone module `Numlib.Conditioning.LinearSystem` proves the Rigal–Gaches theorem with the
operator norm. The paper uses the Frobenius norm, so this module proves again the two norm facts
that the argument needs. The rest of the argument is the same computation.
-/

/-- The product is additive in the matrix: $(E + F) x = Ex + Fx$. The perturbed system $(A + E) x$
needs this. -/
theorem add_mulVecE (E F : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) :
    (E + F) ⬝ x = E ⬝ x + F ⬝ x := by
  change Matrix.toEuclideanLin (E + F) x
    = Matrix.toEuclideanLin E x + Matrix.toEuclideanLin F x
  rw [map_add, LinearMap.add_apply]

/-- The product is homogeneous in the matrix: $(cE) x = c\,(Ex)$ for $c \in \mathbb{R}$. -/
theorem smul_mulVecE (c : ℝ) (E : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) :
    (c • E) ⬝ x = c • (E ⬝ x) := by
  change Matrix.toEuclideanLin (c • E) x = c • Matrix.toEuclideanLin E x
  rw [map_smul, LinearMap.smul_apply]

/-- For finite index types and vectors $w$ and $v$, the Frobenius norm of the rank-one matrix
$w v^T$ is $\|w v^T\| = \|w\| \, \|v\|$, with the Euclidean norms of $w$ and $v$. -/
theorem frobenius_norm_vecMulVec {m k : Type*} [Fintype m] [Fintype k] (w : m → ℝ) (v : k → ℝ) :
    ‖Matrix.vecMulVec w v‖
      = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ m)‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ k)‖ := by
  rw [Matrix.frobenius_norm_def, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow]
  congr 1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.vecMulVec_apply, Real.rpow_two, norm_mul, mul_pow]

/-- The Frobenius norm dominates the operator norm: $\|Ex\| \le \|E\| \, \|x\|$ for every
$E \in \mathbb{R}^{n \times n}$ and $x \in \mathbb{R}^n$. -/
theorem norm_mulVecE_le_frobenius (E : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) :
    ‖E ⬝ x‖ ≤ ‖E‖ * ‖x‖ := by
  have hone : ‖(WithLp.toLp 2 (fun _ : Unit => (1 : ℝ)) : EuclideanSpace ℝ Unit)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp
  have hcol : ∀ u : Vec n, ‖Matrix.vecMulVec (WithLp.ofLp u) fun _ : Unit => (1 : ℝ)‖ = ‖u‖ := by
    intro u
    rw [frobenius_norm_vecMulVec, hone, mul_one]
  have hmul : E * Matrix.vecMulVec (WithLp.ofLp x) (fun _ : Unit => (1 : ℝ))
      = Matrix.vecMulVec (WithLp.ofLp (E ⬝ x)) fun _ : Unit => (1 : ℝ) :=
    Matrix.mul_vecMulVec _ _ _
  calc ‖E ⬝ x‖ = ‖E * Matrix.vecMulVec (WithLp.ofLp x) fun _ : Unit => (1 : ℝ)‖ := by
        rw [hmul, hcol]
    _ ≤ ‖E‖ * ‖Matrix.vecMulVec (WithLp.ofLp x) fun _ : Unit => (1 : ℝ)‖ :=
        Matrix.frobenius_norm_mul _ _
    _ = ‖E‖ * ‖x‖ := by rw [hcol]

/-- A rank-one matrix applied to a vector: $(u v^T) w = (v^T w)\,u$ for $u, v, w \in \mathbb{R}^n$.
-/
theorem mulVecE_vecMulVec (u v w : Vec n) :
    Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp v) ⬝ w = ⟪v, w⟫_ℝ • u := by
  ext i
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, mul_assoc]
  rw [← Finset.mul_sum, mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ### Acceptable solutions and the normwise relative backward error -/

/-- **Equation (3.1)** of [fong2012cg], acceptable solutions. Let $A \in \mathbb{R}^{n \times n}$,
$b \in \mathbb{R}^n$ and tolerances $\alpha, \beta \in \mathbb{R}$. A vector $x$ is an
**acceptable solution** if there are $E \in \mathbb{R}^{n \times n}$ and $f \in \mathbb{R}^n$
with $$(A + E)\,x = b + f, \qquad \frac{\|E\|}{\|A\|} \le \alpha, \qquad \frac{\|f\|}{\|b\|} \le
\beta.$$

The matrix norm is the Frobenius norm. The ratios are Lean divisions, so a ratio with
denominator $0$ is $0$; the results that use this definition therefore assume $A \neq 0$ and
$b \neq 0$. -/
def IsAcceptable (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) : Prop :=
  ∃ (E : Matrix (Fin n) (Fin n) ℝ) (f : Vec n),
    (A + E) ⬝ x = b + f ∧ ‖E‖ / ‖A‖ ≤ α ∧ ‖f‖ / ‖b‖ ≤ β

/-- For $A$, $b$, tolerances $\alpha, \beta$ and a vector $x$, the set of the numbers
$\xi \in \mathbb{R}$ for which there are $E$ and $f$ with $(A + E) x = b + f$,
$\|E\| / \|A\| \le \alpha \xi$ and $\|f\| / \|b\| \le \beta \xi$. The normwise relative backward
error is the least element of this set (`FongSaunders.nrbe_isLeast`). -/
def nrbeFeasible (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) : Set ℝ :=
  {ξ : ℝ | ∃ (E : Matrix (Fin n) (Fin n) ℝ) (f : Vec n),
    (A + E) ⬝ x = b + f ∧ ‖E‖ / ‖A‖ ≤ α * ξ ∧ ‖f‖ / ‖b‖ ≤ β * ξ}

/-- **Equation (3.2)** of [fong2012cg], the normwise relative backward error. For $A$, $b$,
tolerances $\alpha, \beta$ and $x_k \in \mathbb{R}^n$ with residual $r_k = b - A x_k$, $$\xi_k =
\frac{\|r_k\|}{\alpha \|A\| \|x_k\| + \beta \|b\|}.$$

The value is $0$ when the denominator is $0$. -/
noncomputable def nrbe (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) : ℝ :=
  ‖b - A ⬝ x‖ / (α * ‖A‖ * ‖x‖ + β * ‖b‖)

/-- **Equation (3.2)** of [fong2012cg], the weight. For $A$, $b$, tolerances $\alpha, \beta$ and
$x_k \in \mathbb{R}^n$, $$\phi_k = \frac{\beta \|b\|}{\alpha \|A\| \|x_k\| + \beta \|b\|}.$$

The value is $0$ when the denominator is $0$. -/
noncomputable def nrbePhi (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) : ℝ :=
  β * ‖b‖ / (α * ‖A‖ * ‖x‖ + β * ‖b‖)

/-- **Equation (3.3)** of [fong2012cg], the optimal matrix perturbation. For $A$, $b$, tolerances
$\alpha, \beta$ and $x_k \in \mathbb{R}^n$ with residual $r_k = b - A x_k$, $$E_k = \frac{1 -
\phi_k}{\|x_k\|^2}\, r_k x_k^T.$$

For $x_k = 0$ the coefficient is a division by $0$, so $E_k = 0$. -/
noncomputable def nrbePertA (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((1 - nrbePhi A b α β x) / ‖x‖ ^ 2) •
    Matrix.vecMulVec (WithLp.ofLp (b - A ⬝ x)) (WithLp.ofLp x)

/-- **Equation (3.3)** of [fong2012cg], the optimal right-hand-side perturbation. For $A$, $b$,
tolerances $\alpha, \beta$ and $x_k \in \mathbb{R}^n$ with residual $r_k = b - A x_k$, $$f_k =
-\phi_k\, r_k.$$
-/
noncomputable def nrbePertb (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) :
    Vec n :=
  -nrbePhi A b α β x • (b - A ⬝ x)

/-- If $\beta \ge 0$ and $\alpha \|A\| \|x_k\| + \beta \|b\| \ge 0$, then $\phi_k \ge 0$. -/
theorem nrbePhi_nonneg (x : Vec n) (hβ : 0 ≤ β) (hden : 0 ≤ α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    0 ≤ nrbePhi A b α β x :=
  div_nonneg (mul_nonneg hβ (norm_nonneg b)) hden

/-- If $\alpha \|A\| \|x_k\| + \beta \|b\| > 0$, then $$1 - \phi_k = \frac{\alpha \|A\|
\|x_k\|}{\alpha \|A\| \|x_k\| + \beta \|b\|}.$$
-/
theorem one_sub_nrbePhi {x : Vec n} (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    1 - nrbePhi A b α β x = α * ‖A‖ * ‖x‖ / (α * ‖A‖ * ‖x‖ + β * ‖b‖) := by
  rw [nrbePhi, eq_div_iff hden.ne', sub_mul, one_mul, div_mul_cancel₀ _ hden.ne']
  ring

/-- If $\alpha \ge 0$ and $\alpha \|A\| \|x_k\| + \beta \|b\| > 0$, then $1 - \phi_k \ge 0$; this is
the coefficient of the optimal matrix perturbation $E_k$. -/
theorem one_sub_nrbePhi_nonneg (hα : 0 ≤ α) {x : Vec n}
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) : 0 ≤ 1 - nrbePhi A b α β x := by
  rw [one_sub_nrbePhi hden]
  positivity

/-! ### Equations (3.5)–(3.6): the norms of the optimal perturbations -/

/-- **Equation (3.5)** of [fong2012cg]. Let $\alpha \ge 0$, let $x_k \neq 0$, and let
$\alpha \|A\| \|x_k\| + \beta \|b\| > 0$. Then the optimal matrix perturbation satisfies
$$\|E_k\| = \frac{(1 - \phi_k)\,\|r_k\|}{\|x_k\|}.$$

The norm is the Frobenius norm. -/
theorem norm_nrbePertA (hα : 0 ≤ α) {x : Vec n} (hx : x ≠ 0)
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    ‖nrbePertA A b α β x‖ = (1 - nrbePhi A b α β x) * ‖b - A ⬝ x‖ / ‖x‖ := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
  have hnn : (0 : ℝ) ≤ (1 - nrbePhi A b α β x) / ‖x‖ ^ 2 :=
    div_nonneg (one_sub_nrbePhi_nonneg hα hden) (sq_nonneg _)
  rw [nrbePertA, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn, frobenius_norm_vecMulVec]
  have h1 : (WithLp.toLp 2 (WithLp.ofLp (b - A ⬝ x)) : Vec n) = b - A ⬝ x := rfl
  have h2 : (WithLp.toLp 2 (WithLp.ofLp x) : Vec n) = x := rfl
  rw [h1, h2]
  field_simp

/-- **Equation (3.6)** of [fong2012cg]. Let $\beta \ge 0$ and
$\alpha \|A\| \|x_k\| + \beta \|b\| > 0$. Then the optimal right-hand-side perturbation
satisfies $$\|f_k\| = \phi_k \|r_k\|.$$
-/
theorem norm_nrbePertb (hβ : 0 ≤ β) {x : Vec n} (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    ‖nrbePertb A b α β x‖ = nrbePhi A b α β x * ‖b - A ⬝ x‖ := by
  rw [nrbePertb, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (nrbePhi_nonneg x hβ hden.le)]

/-- Equation (3.6) in relative form. If $b \neq 0$, $\beta \ge 0$ and
$\alpha \|A\| \|x_k\| + \beta \|b\| > 0$, then $\|f_k\| / \|b\| = \beta \xi_k$. This holds for
every $x_k$, also for $x_k = 0$. -/
theorem norm_nrbePertb_div (hb0 : b ≠ 0) (hβ : 0 ≤ β) {x : Vec n}
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    ‖nrbePertb A b α β x‖ / ‖b‖ = β * nrbe A b α β x := by
  have hbn : (0 : ℝ) < ‖b‖ := norm_pos_iff.2 hb0
  rw [norm_nrbePertb hβ hden, nrbePhi, nrbe]
  field_simp

/-- Equation (3.5) in relative form. If $A \neq 0$, $\alpha \ge 0$, $x_k \neq 0$ and
$\alpha \|A\| \|x_k\| + \beta \|b\| > 0$, then $\|E_k\| / \|A\| = \alpha \xi_k$. -/
theorem norm_nrbePertA_div (hA0 : A ≠ 0) (hα : 0 ≤ α) {x : Vec n} (hx : x ≠ 0)
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    ‖nrbePertA A b α β x‖ / ‖A‖ = α * nrbe A b α β x := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
  have hAn : (0 : ℝ) < ‖A‖ := norm_pos_iff.2 hA0
  rw [norm_nrbePertA hα hx hden, one_sub_nrbePhi hden, nrbe]
  field_simp

/-! ### Equations (3.2)–(3.3): the optimal perturbations attain the backward error -/

/-- **Equations (3.2)–(3.3)** of [fong2012cg], attainment. Let $A \neq 0$, $b \neq 0$,
$\alpha, \beta \ge 0$, $x_k \neq 0$ and $\alpha \|A\| \|x_k\| + \beta \|b\| > 0$. Then the
perturbations $E_k$ and $f_k$ of (3.3) are feasible and attain the value $\xi_k$: $$(A +
E_k)\,x_k = b + f_k, \qquad \frac{\|E_k\|}{\|A\|} = \alpha \xi_k, \qquad \frac{\|f_k\|}{\|b\|} =
\beta \xi_k.$$

**Reading.** The paper leaves the conditions $A \neq 0$ and $b \neq 0$ implicit in the ratios
$\|E\| / \|A\|$ and $\|f\| / \|b\|$. Lean's convention $t / 0 = 0$ would make both ratios vanish
otherwise, so the conditions are stated. For positive definite $A$, the condition $A \neq 0$
follows from $b \neq 0$ by `FongSaunders.ne_zero_of_posDef`. -/
theorem nrbePert_attains (hA0 : A ≠ 0) (hb0 : b ≠ 0) (hα : 0 ≤ α) (hβ : 0 ≤ β) {x : Vec n}
    (hx : x ≠ 0) (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    (A + nrbePertA A b α β x) ⬝ x = b + nrbePertb A b α β x ∧
      ‖nrbePertA A b α β x‖ / ‖A‖ = α * nrbe A b α β x ∧
        ‖nrbePertb A b α β x‖ / ‖b‖ = β * nrbe A b α β x := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
  refine ⟨?_, norm_nrbePertA_div hA0 hα hx hden, norm_nrbePertb_div hb0 hβ hden⟩
  have happ : nrbePertA A b α β x ⬝ x = (1 - nrbePhi A b α β x) • (b - A ⬝ x) := by
    rw [nrbePertA, smul_mulVecE, mulVecE_vecMulVec, real_inner_self_eq_norm_sq, smul_smul,
      div_mul_cancel₀ _ (by positivity : (‖x‖ : ℝ) ^ 2 ≠ 0)]
  have hAx : A ⬝ x = b - (b - A ⬝ x) := by abel
  rw [add_mulVecE, happ, nrbePertb, hAx]
  module

/-- **Equation (3.2)** of [fong2012cg], optimality of the backward error. Let $A \neq 0$,
$b \neq 0$, $\alpha, \beta \ge 0$, and let $\alpha \|A\| \|x_k\| + \beta \|b\| > 0$. Then
$\xi_k$ is the optimal value of the problem
$$\min \xi \quad \text{subject to} \quad (A + E)\,x_k = b + f, \quad \frac{\|E\|}{\|A\|} \le
  \alpha \xi, \quad \frac{\|f\|}{\|b\|} \le \beta \xi.$$
That is, $\xi_k$ is feasible, and $\xi_k \le \xi$ for every feasible $\xi$.

**Reading.** The paper leaves the conditions $A \neq 0$ and $b \neq 0$ implicit in the ratios.
Without them the statement is false, because Lean's convention $t / 0 = 0$ makes every
perturbation of a zero matrix feasible at every tolerance. For example, if $A = 0$, $b \neq 0$,
$\beta > 0$ and $x_k \neq 0$, then $\xi = 0$ is feasible with $f = 0$ and any $E$ with
$E x_k = b$, while $\xi_k = 1 / \beta > 0$.

The feasible set is `FongSaunders.nrbeFeasible`. The vector $x_k$ can be $0$. -/
theorem nrbe_isLeast (hA0 : A ≠ 0) (hb0 : b ≠ 0) (hα : 0 ≤ α) (hβ : 0 ≤ β) (x : Vec n)
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    IsLeast (nrbeFeasible A b α β x) (nrbe A b α β x) := by
  have hAn : (0 : ℝ) < ‖A‖ := norm_pos_iff.2 hA0
  have hbn : (0 : ℝ) < ‖b‖ := norm_pos_iff.2 hb0
  constructor
  · rcases eq_or_ne x 0 with rfl | hx
    · have hβ0 : 0 < β := by
        rcases eq_or_lt_of_le hβ with h | h
        · exfalso
          rw [← h] at hden
          simp at hden
        · exact h
      have hnr : nrbe A b α β 0 = 1 / β := by
        rw [nrbe]
        simp only [mulVecE_zero, sub_zero, norm_zero, mul_zero, zero_add]
        rw [mul_comm β ‖b‖, ← div_div, div_self hbn.ne']
      refine ⟨0, -b, by simp, ?_, ?_⟩
      · rw [norm_zero, zero_div, hnr]
        exact mul_nonneg hα (by positivity)
      · rw [norm_neg, div_self hbn.ne', hnr, mul_one_div, div_self hβ0.ne']
    · obtain ⟨h1, h2, h3⟩ := nrbePert_attains hA0 hb0 hα hβ hx hden
      exact ⟨_, _, h1, h2.le, h3.le⟩
  · rintro ξ ⟨E, f, hEf, hE, hf⟩
    rw [add_mulVecE] at hEf
    have hres : b - A ⬝ x = E ⬝ x - f := by
      have hb' : b = A ⬝ x + E ⬝ x - f := by rw [hEf]; abel
      rw [hb']
      abel
    have hEle : ‖E‖ ≤ α * ξ * ‖A‖ := (div_le_iff₀ hAn).1 hE
    have hfle : ‖f‖ ≤ β * ξ * ‖b‖ := (div_le_iff₀ hbn).1 hf
    rw [nrbe, div_le_iff₀ hden]
    calc ‖b - A ⬝ x‖ = ‖E ⬝ x - f‖ := by rw [hres]
      _ ≤ ‖E ⬝ x‖ + ‖f‖ := norm_sub_le _ _
      _ ≤ ‖E‖ * ‖x‖ + ‖f‖ := by gcongr; exact norm_mulVecE_le_frobenius E x
      _ ≤ α * ξ * ‖A‖ * ‖x‖ + β * ξ * ‖b‖ := by gcongr
      _ = ξ * (α * ‖A‖ * ‖x‖ + β * ‖b‖) := by ring

/-! ### Acceptability and the stopping rule (3.4) -/

/-- **Equation (3.4)** of [fong2012cg], the stopping rule. Let $\alpha, \beta \in \mathbb{R}$, and
let $\alpha \|A\| \|x_k\| + \beta \|b\| > 0$. Then $$\xi_k \le 1 \iff \|r_k\| \le \alpha \|A\|
\|x_k\| + \beta \|b\|.$$
-/
theorem nrbe_le_one_iff (α β : ℝ) (x : Vec n) (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    nrbe A b α β x ≤ 1 ↔ ‖b - A ⬝ x‖ ≤ α * ‖A‖ * ‖x‖ + β * ‖b‖ := by
  rw [nrbe, div_le_one hden]

/-- **Section 3** of [fong2012cg], acceptability. Let $A \neq 0$, $b \neq 0$, $\alpha, \beta \ge 0$,
and let $\alpha \|A\| \|x_k\| + \beta \|b\| > 0$. Then $x_k$ is an acceptable solution (3.1) if
and only if $\xi_k \le 1$.

**Reading.** The paper leaves the conditions $A \neq 0$ and $b \neq 0$ implicit in the ratios of
(3.1); without them the statement fails, because Lean's convention $t / 0 = 0$ makes every
perturbation of a zero matrix feasible. -/
theorem isAcceptable_iff_nrbe_le_one (hA0 : A ≠ 0) (hb0 : b ≠ 0) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    {x : Vec n} (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    IsAcceptable A b α β x ↔ nrbe A b α β x ≤ 1 := by
  constructor
  · rintro ⟨E, f, hEf, hE, hf⟩
    exact (nrbe_isLeast hA0 hb0 hα hβ x hden).2
      ⟨E, f, hEf, by rwa [mul_one], by rwa [mul_one]⟩
  · intro h
    obtain ⟨E, f, hEf, hE, hf⟩ := (nrbe_isLeast hA0 hb0 hα hβ x hden).1
    refine ⟨E, f, hEf, hE.trans ?_, hf.trans ?_⟩
    · calc α * nrbe A b α β x ≤ α * 1 := by gcongr
        _ = α := mul_one α
    · calc β * nrbe A b α β x ≤ β * 1 := by gcongr
        _ = β := mul_one β

/-! ### The weight $\phi_k$ decreases for CG and MINRES (Section 3.2) -/

/-- Let $\alpha, \beta \ge 0$, and let $(x_k)$ be a sequence with $\|x_k\|$ nondecreasing. Then
$\phi_k$ is nonincreasing along $(x_k)$. -/
theorem nrbePhi_antitone_of_monotone (hα : 0 ≤ α) (hβ : 0 ≤ β) {x : ℕ → Vec n}
    (hmono : Monotone fun k => ‖x k‖) : Antitone fun k => nrbePhi A b α β (x k) := by
  intro i j hij
  simp only [nrbePhi]
  have hnum : 0 ≤ β * ‖b‖ := mul_nonneg hβ (norm_nonneg b)
  have haA : 0 ≤ α * ‖A‖ := mul_nonneg hα (norm_nonneg A)
  have hle : ‖x i‖ ≤ ‖x j‖ := hmono hij
  have hd : α * ‖A‖ * ‖x i‖ + β * ‖b‖ ≤ α * ‖A‖ * ‖x j‖ + β * ‖b‖ := by nlinarith
  rcases eq_or_lt_of_le hnum with h0 | h0
  · simp [← h0]
  · have hden : ∀ k : ℕ, 0 < α * ‖A‖ * ‖x k‖ + β * ‖b‖ := fun k => by
      nlinarith [norm_nonneg (x k)]
    rw [div_le_div_iff₀ (hden j) (hden i)]
    exact mul_le_mul_of_nonneg_left hd hnum

/-- **Section 3.2** of [fong2012cg], the weight for CG. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, and let $\alpha, \beta \ge 0$. Then $\phi_k$ at the CG iterates $x_k^C$
decreases monotonically: $\phi_l \le \phi_k$ for $k \le l$.

The proof uses the increase of $\|x_k^C\|$, which is the theorem of [steihaug1983conjugate]. -/
theorem nrbePhi_cg_antitone (hA : A.PosDef) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Antitone fun k => nrbePhi A b α β (cg A b k).x := by
  refine nrbePhi_antitone_of_monotone hα hβ ?_
  simp only [cg_x]
  exact CG.norm_iterate_monotone b (isSymmetricCoercive_of_posDef hA)

/-- **Section 3.2** of [fong2012cg], the weight for MINRES. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, let $\alpha, \beta \ge 0$, and let $(x_k)$ be a sequence such that each $x_k$
is a MINRES iterate at step $k$. Then $\phi_k$ decreases monotonically: $\phi_l \le \phi_k$ for
$k \le l$.

The proof uses Theorem 2.3 (`FongSaunders.theorem_2_3_minres`). -/
theorem nrbePhi_minres_antitone (hA : A.PosDef) (hα : 0 ≤ α) (hβ : 0 ≤ β) {x : ℕ → Vec n}
    (hx : ∀ k, IsMINRESIterate A b k (x k)) : Antitone fun k => nrbePhi A b α β (x k) :=
  nrbePhi_antitone_of_monotone hα hβ (theorem_2_3_minres hA hx)

/-! ### Theorem 3.1 -/

/-- If $A$ is positive definite, $b \neq 0$, and $(x_k)$ is a sequence such that each $x_k$ is a
MINRES iterate at step $k$, then $x_k \neq 0$ for every $k \ge 1$. So the ratio
$\|r_k\| / \|x_k\|$ has a nonzero denominator for $k \ge 1$. -/
theorem minres_iterate_ne_zero (hA : A.PosDef) (hb : b ≠ 0) {x : ℕ → Vec n}
    (hx : ∀ k, IsMINRESIterate A b k (x k)) {k : ℕ} (hk : 1 ≤ k) : x k ≠ 0 := by
  have h1 : x 1 ≠ 0 := by
    rw [Krylov.IsMinResidualIterate.eq_CR_iterate (isSymmetricCoercive_of_posDef hA)
      (isMINRESIterate_iff.1 (hx 1))]
    exact CR.iterate_one_x_ne_zero b (isSymmetricCoercive_of_posDef hA) hb
  have hmono := theorem_2_3_minres hA hx hk
  simp only at hmono
  exact norm_pos_iff.1 (lt_of_lt_of_le (norm_pos_iff.2 h1) hmono)

/-- **Theorem 3.1** of [fong2012cg], the backward error for MINRES. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite, $b \neq 0$, $\alpha \ge 0$ and
$\beta > 0$, and let $(x_k)$ be a sequence such that each $x_k$ is a MINRES iterate at step $k$.
Then the normwise relative backward error decreases monotonically: $$\xi_l \le \xi_k \quad
\text{for } k \le l.$$

With $\beta > 0$ the denominator of $\xi_k$ is positive also at $k = 0$, so the statement holds
for all $k$. The case $\beta = 0$ is `FongSaunders.nrbe_minres_antitoneOn`. -/
theorem nrbe_minres_antitone (hA : A.PosDef) (hb : b ≠ 0) (hα : 0 ≤ α) (hβ : 0 < β)
    {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k)) :
    Antitone fun k => nrbe A b α β (x k) :=
  Krylov.IsMinResidualIterate.backwardError_antitone (isSymmetricCoercive_of_posDef hA)
    (fun k => isMINRESIterate_iff.1 (hx k)) hα hβ (norm_nonneg A) hb

/-- **Theorem 3.1** of [fong2012cg], the backward error for MINRES from step $1$. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite, $b \neq 0$, $\alpha > 0$ and
$\beta \ge 0$, and let $(x_k)$ be a sequence such that each $x_k$ is a MINRES iterate at step
$k$. Then $$\xi_l \le \xi_k \quad \text{for } 1 \le k \le l.$$

**Reading.** The restriction to $k \ge 1$ is necessary: for $\beta = 0$ the value
$\xi_0 = \|b\| / (\alpha \|A\| \cdot 0)$ is a division by $0$, which Lean evaluates to $0$,
below every later value. -/
theorem nrbe_minres_antitoneOn (hA : A.PosDef) (hb : b ≠ 0) (hα : 0 < α) (hβ : 0 ≤ β)
    {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k)) :
    AntitoneOn (fun k => nrbe A b α β (x k)) (Set.Ici 1) := by
  rcases eq_or_lt_of_le hβ with hβ0 | hβ0
  · have hkey := Krylov.IsMinResidualIterate.norm_residual_div_norm_antitoneOn
      (isSymmetricCoercive_of_posDef hA) (fun k => isMINRESIterate_iff.1 (hx k)) hb
    have hrw : ∀ y : Vec n, nrbe A b α β y = (α * ‖A‖)⁻¹ * (‖b - A ⬝ y‖ / ‖y‖) := by
      intro y
      rw [nrbe, ← hβ0, zero_mul, add_zero, div_eq_mul_inv, mul_inv, div_eq_mul_inv]
      ring
    intro i hi j hj hij
    have h := hkey hi hj hij
    simp only at h
    simp only [hrw]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · exact (nrbe_minres_antitone hA hb hα.le hβ0 hx).antitoneOn _

/-- **Theorem 3.1** of [fong2012cg], for MINRES. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, $b \neq 0$ and $\alpha, \beta > 0$, and let $(x_k)$ be a sequence such that each $x_k$
is a MINRES iterate at step $k$. Then the relative backward errors of the optimal perturbations
(3.3) decrease monotonically: $$\frac{\|E_l\|}{\|A\|} \le \frac{\|E_k\|}{\|A\|} \quad \text{for
} 1 \le k \le l, \qquad \frac{\|f_l\|}{\|b\|} \le \frac{\|f_k\|}{\|b\|} \quad \text{for } k \le
l.$$

**Reading.** The paper states the decrease of $\|E_k\| / \|A\|$ without a lower bound on $k$. At
$k = 0$ the iterate is $x_0 = 0$, so the paper's $E_0$ is undefined, while Lean's $E_0$ is $0$,
below every later value. The decrease of $\|E_k\| / \|A\|$ is therefore stated for $k \ge 1$. -/
theorem theorem_3_1_minres (hA : A.PosDef) (hb : b ≠ 0) (hα : 0 < α) (hβ : 0 < β)
    {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k)) :
    AntitoneOn (fun k => ‖nrbePertA A b α β (x k)‖ / ‖A‖) (Set.Ici 1) ∧
      Antitone fun k => ‖nrbePertb A b α β (x k)‖ / ‖b‖ := by
  have hA0 : A ≠ 0 := ne_zero_of_posDef hA hb
  have hbn : (0 : ℝ) < ‖b‖ := norm_pos_iff.2 hb
  have hden : ∀ y : Vec n, 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖ := fun y => by
    have h1 : 0 ≤ α * ‖A‖ * ‖y‖ := by positivity
    have h2 : 0 < β * ‖b‖ := by positivity
    linarith
  constructor
  · intro i hi j hj hij
    have ei := norm_nrbePertA_div hA0 hα.le
      (minres_iterate_ne_zero hA hb hx (Set.mem_Ici.1 hi)) (hden (x i))
    have ej := norm_nrbePertA_div hA0 hα.le
      (minres_iterate_ne_zero hA hb hx (Set.mem_Ici.1 hj)) (hden (x j))
    simp only [ei, ej]
    exact mul_le_mul_of_nonneg_left (nrbe_minres_antitone hA hb hα.le hβ hx hij) hα.le
  · intro i j hij
    simp only [norm_nrbePertb_div hb hβ.le (hden (x i)), norm_nrbePertb_div hb hβ.le (hden (x j))]
    exact mul_le_mul_of_nonneg_left (nrbe_minres_antitone hA hb hα.le hβ hx hij) hβ.le

/-- **Theorem 3.1** of [fong2012cg], for CR. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, $b \neq 0$ and $\alpha, \beta > 0$. Then at the CR iterates $x_k$,
$$\frac{\|E_l\|}{\|A\|} \le \frac{\|E_k\|}{\|A\|} \quad \text{for } 1 \le k \le l, \qquad
\frac{\|f_l\|}{\|b\|} \le \frac{\|f_k\|}{\|b\|} \quad \text{for } k \le l.$$

**Reading.** As in `FongSaunders.theorem_3_1_minres`, the decrease of $\|E_k\| / \|A\|$ is
stated for $k \ge 1$, because $E_0$ is undefined in the paper. -/
theorem theorem_3_1_cr (hA : A.PosDef) (hb : b ≠ 0) (hα : 0 < α) (hβ : 0 < β) :
    AntitoneOn (fun k => ‖nrbePertA A b α β (cr A b k).x‖ / ‖A‖) (Set.Ici 1) ∧
      Antitone fun k => ‖nrbePertb A b α β (cr A b k).x‖ / ‖b‖ :=
  theorem_3_1_minres hA hb hα hβ (cr_isMINRESIterate hA)

/-! ### MINRES stops no later than CG under the rule (3.4) with $\alpha = 0$ -/

/-- **Section 3** of [fong2012cg], the residuals of MINRES and CG. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite. If $x$ is a MINRES iterate at step $k$,
then $$\|b - Ax\| \le \|r_k^C\|.$$
-/
theorem minres_norm_residual_le_cg (hA : A.PosDef) (k : ℕ) {x : Vec n}
    (hx : IsMINRESIterate A b k x) : ‖b - A ⬝ x‖ ≤ ‖(cg A b k).r‖ := by
  rw [cg_residual_eq]
  exact hx.2 _ (cg_mem_krylov hA k)

/-- **Section 3** of [fong2012cg], MINRES stops first. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, let $\beta \in \mathbb{R}$, and let $(x_k)$ be a sequence such that each
$x_k$ is a MINRES iterate at step $k$. If CG satisfies the stopping rule
$\|r_k^C\| \le \beta \|b\|$ at step $k$, which is rule (3.4) with $\alpha = 0$, then MINRES
satisfies it too: $$\|b - A x_k\| \le \beta \|b\|.$$
-/
theorem minres_stops_first (hA : A.PosDef) (β : ℝ) {x : ℕ → Vec n}
    (hx : ∀ k, IsMINRESIterate A b k (x k)) (k : ℕ) (hcg : ‖(cg A b k).r‖ ≤ β * ‖b‖) :
    ‖b - A ⬝ x k‖ ≤ β * ‖b‖ :=
  (minres_norm_residual_le_cg hA k (hx k)).trans hcg

end FongSaunders
