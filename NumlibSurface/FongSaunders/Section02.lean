/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.CR
import Numlib.Krylov.Iterate
import Numlib.Krylov.Monotonicity
import Numlib.Krylov.Subspace
import Numlib.Projection.Basic
import Numlib.Projection.Optimality
import NumlibSurface.FongSaunders.Section01

/-!
# Fong and Saunders, Section 2: Algorithms CG and CR, their minimization properties and monotonicity

This module formalizes Section 2 of [fong2012cg]. For a symmetric positive definite system $Ax = b$,
started from $x_0 = 0$, it transcribes Algorithm CG and Algorithm CR of Table 2.1 as state
recurrences and identifies them with the backbone recurrences `CG.iterate` and `CR.iterate`. Every
other result of the section is then a specialization of the backbone modules `Numlib.Krylov.CG`,
`Numlib.Krylov.CR`, `Numlib.Krylov.Iterate` and `Numlib.Krylov.Monotonicity`. The CG quantities
carry the superscript $C$, as in $x_k^C$ and $r_k^C$; the CR quantities are $x_k$, $r_k$,
$s_k = A r_k$, $\rho_k = r_k^T A r_k$, $p_k$ and $q_k = A p_k$.

The section covers the quadratic $\phi(x) = \frac12 x^T A x - b^T x$ and the energy norm
$\|v\|_A = (v^T A v)^{1/2}$ (Section 2.1); CG as the minimizer of $\phi$, equivalently of
$\|x^* - x\|_A$, over $\mathcal{K}_k(A, b)$ (Section 2.1); MINRES as the minimizer (2.1) of
$\|b - Ax\|$ over $\mathcal{K}_k(A, b)$, and the fact that CR and MINRES coincide on symmetric
positive definite systems (Section 2.2); the termination of both algorithms at the Lanczos step
$\ell \le n$ (Section 2.3); the orthogonality relations of Theorem 2.1; the sign relations (2.2) and
Theorem 2.2; and the monotonicity Theorems 2.3, 2.4 and 2.5.

## Main definitions

* Section 2.1, `FongSaunders.phi`: the quadratic $\phi(x) = \frac12 x^T A x - b^T x$.
* Section 2.1, `FongSaunders.energyNorm`: the energy norm $\|v\|_A = (v^T A v)^{1/2}$.
* Table 2.1, `FongSaunders.cg`: the states of Algorithm CG, built from `FongSaunders.cgInit` and
  `FongSaunders.cgStep`.
* Table 2.1, `FongSaunders.cgAlpha` and `FongSaunders.cgBeta`: the coefficients $\alpha_k$ and
  $\beta_k$ of Algorithm CG.
* Table 2.1, `FongSaunders.cr`: the states of Algorithm CR, built from `FongSaunders.crInit` and
  `FongSaunders.crStep`.
* Table 2.1, `FongSaunders.crAlpha` and `FongSaunders.crBeta`: the coefficients $\alpha_k$ and
  $\beta_k$ of Algorithm CR.
* Equation (2.1), `FongSaunders.IsMINRESIterate`: $x$ is a MINRES iterate at step $k$ if it
  minimizes $\|b - Ax\|$ over $\mathcal{K}_k(A, b)$.
* Section 2.3, `FongSaunders.cgTerm` and `FongSaunders.crTerm`: the termination steps of the two
  algorithms.

## Main results

* Section 2.1, `FongSaunders.cg_isMinOn_phi`: $x_k^C$ minimizes $\phi$ over $\mathcal{K}_k(A, b)$.
* Section 2.1, `FongSaunders.cg_energyNorm_le`: $x_k^C$ minimizes $\|x^* - x\|_A$ over
  $\mathcal{K}_k(A, b)$.
* Section 2.1, `FongSaunders.cg_unique_min`: the minimizer of $\phi$ over $\mathcal{K}_k(A, b)$ is
  unique.
* Section 2.2, `FongSaunders.isMINRESIterate_iff_eq_cr`: the MINRES iterate at step $k$ is the CR
  iterate $x_k$.
* Section 2.3, `FongSaunders.cg_residual_eq_zero_iff` and `FongSaunders.cr_residual_eq_zero_iff`:
  $r_k = 0$ if and only if $k \ge \ell$, where $\ell$ is the Lanczos termination step.
* Section 2.3, `FongSaunders.crTerm_le`: the algorithms terminate after at most $n$ iterations.
* Theorem 2.1(a), `FongSaunders.theorem_2_1_a`: $q_i^T q_j = 0$ for $i \neq j$.
* Theorem 2.1(b), `FongSaunders.theorem_2_1_b`: $r_i^T q_j = 0$ for $i > j$.
* Equation (2.2), `FongSaunders.equation_2_2`: $\rho_i = r_i^T A r_i \ge 0$.
* Theorem 2.2(a)–(f), `FongSaunders.theorem_2_2_a` to `FongSaunders.theorem_2_2_f`:
  $\alpha_i \ge 0$, $\beta_i \ge 0$, $p_i^T q_j \ge 0$, $p_i^T p_j \ge 0$, $x_i^T p_j \ge 0$ and
  $r_i^T p_j \ge 0$ for CR.
* Theorem 2.3, `FongSaunders.theorem_2_3_cr` and `FongSaunders.theorem_2_3_minres`: $\|x_k\|$
  increases monotonically for CR and MINRES.
* Theorem 2.4, `FongSaunders.theorem_2_4_cr` and `FongSaunders.theorem_2_4_minres`: $\|x^* - x_k\|$
  decreases monotonically for CR and MINRES.
* Theorem 2.5, `FongSaunders.theorem_2_5_cr` and `FongSaunders.theorem_2_5_minres`:
  $\|x^* - x_k\|_A$ decreases strictly until termination for CR and MINRES.

## Conventions

* An algorithm state after $k$ iterations is indexed by $k$, so `FongSaunders.cg A b k` holds
  $x_k^C$, $r_k^C$, $\rho_k$ and $p_k^C$. The coefficients keep the indexing of the paper:
  $\alpha_k$ and $\beta_k$ belong to iteration $k$, and the values $\alpha_0 = \beta_0 = 0$ are
  conventions.
* A theorem "for MINRES" is stated for every sequence $(x_k)$ such that each $x_k$ satisfies
  `FongSaunders.IsMINRESIterate A b k`.

## Implementation notes

* The recurrences are total. Lean's convention $t / 0 = 0$ makes them stationary after termination,
  which matches the rule of the paper to stop when $r_k = 0$.
* The identifications `FongSaunders.cg_eq_backbone` and `FongSaunders.cr_eq_backbone` hold for every
  matrix $A$; positive definiteness is not needed for them.

## Deviations from the source

* **Energy norm** (reading). Section 2.1 writes $\|v\|_A$ for $v^T A v$; here
  $\|v\|_A = (v^T A v)^{1/2}$, and every statement about it is unchanged by squaring. See
  `FongSaunders.energyNorm`.
* **Table 2.1** (generalization). The stopped algorithms are extended by a constant state
  after termination, with $\alpha_0=\beta_0=0$. See `FongSaunders.cg` and `FongSaunders.cr`.
* **Theorem 2.3** (generalization). The source proves nondecrease. The strict form proves
  a strict increase at every CR step with nonzero current residual. See
  `FongSaunders.theorem_2_3_strict`.
* **Equation (2.1)** (generalization). Residual minimization is defined even for a singular
  or nonsymmetric matrix. The paper applies it to nonsingular symmetric systems. See
  `FongSaunders.IsMINRESIterate`.
* **Section 2.2, MINRES uniqueness** (reading). The declaration establishes uniqueness
  for positive definite matrices, as needed to identify CR with MINRES. See
  `FongSaunders.isMINRESIterate_unique`.
* **Section 2.3, termination indices** (reading). The first zero residual defines the
  termination index. The formal definition returns $0$ if there is no such residual.
  See `FongSaunders.cgTerm` and `FongSaunders.crTerm`.
* **Theorem 2.5** (reading). The strict decrease applies up to the first zero residual.
  The extended sequence has zero error thereafter. See `FongSaunders.theorem_2_5_cr` and
  `FongSaunders.theorem_2_5_minres`.
-/

namespace FongSaunders

open Krylov Matrix

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Vec n}

/-! ### The quadratic $\phi$ and the energy norm -/

/-- **Section 2.1** of [fong2012cg], the quadratic function. For $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$, the function $\phi : \mathbb{R}^n \to \mathbb{R}$ is $$\phi(x) = \tfrac12
x^T A x - b^T x.$$
-/
noncomputable def phi (A : Matrix (Fin n) (Fin n) ℝ) (b x : Vec n) : ℝ :=
  1 / 2 * ⟪x, A ⬝ x⟫_ℝ - ⟪b, x⟫_ℝ

/-- **Section 2.1** of [fong2012cg], the energy norm. For $A \in \mathbb{R}^{n \times n}$ and
$v \in \mathbb{R}^n$, the **energy norm** is $$\|v\|_A = \sqrt{v^T A v}.$$

**Reading.** Section 2.1 of the source writes $\|v\|_A$ for the quantity $v^T A v$, the square
of the value here. The definition takes the square root, so that $\|\cdot\|_A$ is a norm when
$A$ is positive definite. Every statement of the paper about $\|\cdot\|_A$ is a minimization or
a monotonicity statement, and squaring does not change it.

The square root is `Real.sqrt`, which is $0$ for a negative argument.
`FongSaunders.energyNorm_eq` identifies the definition with the backbone `energyNorm` of
`Matrix.toEuclideanLin A`. -/
noncomputable def energyNorm (A : Matrix (Fin n) (Fin n) ℝ) (v : Vec n) : ℝ :=
  Real.sqrt ⟪v, A ⬝ v⟫_ℝ

/-- The surface energy norm $\|v\|_A$ is the backbone `energyNorm` of the linear map
`Matrix.toEuclideanLin A`. -/
theorem energyNorm_eq (A : Matrix (Fin n) (Fin n) ℝ) (v : Vec n) :
    energyNorm A v = _root_.energyNorm (toEuclideanLin A) v := by
  rw [energyNorm, _root_.energyNorm, RCLike.re_to_real, real_inner_comm]

/-- The energy norm is nonnegative: $\|v\|_A \ge 0$. -/
theorem energyNorm_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (v : Vec n) : 0 ≤ energyNorm A v :=
  Real.sqrt_nonneg _

/-- If $A$ is positive definite, then $\|v\|_A^2 = v^T A v$. -/
theorem energyNorm_sq (hA : A.PosDef) (v : Vec n) : energyNorm A v ^ 2 = ⟪v, A ⬝ v⟫_ℝ :=
  Real.sq_sqrt (inner_mulVecE_self_nonneg hA v)

/-- The surface quadratic $\phi(x)$ equals $\frac12 (Ax)^T x - b^T x$, the backbone form of the
quadratic. -/
theorem phi_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x : Vec n) :
    phi A b x = RCLike.re (inner ℝ (toEuclideanLin A x) x) / 2 - RCLike.re (inner ℝ b x) := by
  rw [phi, RCLike.re_to_real, RCLike.re_to_real, real_inner_comm (A ⬝ x) x]
  ring

/-! ### Algorithm CG (Table 2.1, first column) -/

/-- **Table 2.1** of [fong2012cg], the state of Algorithm CG. A state consists of an iterate $x$, a
residual $r$, the scalar $\rho = r^T r$ and a search direction $p$. -/
structure CGState (n : ℕ) where
  /-- The iterate $x_k^C$. -/
  x : Vec n
  /-- The residual $r_k^C = b - A x_k^C$. -/
  r : Vec n
  /-- The scalar $\rho_k = (r_k^C)^T r_k^C$. -/
  ρ : ℝ
  /-- The search direction $p_k^C$. -/
  p : Vec n

/-- **Table 2.1** of [fong2012cg], one iteration of Algorithm CG. From the state $(x, r, \rho, p)$
the iteration computes $$q = Ap, \quad \alpha = \rho / p^T q, \quad x \leftarrow x + \alpha p,
\quad r \leftarrow r - \alpha q,$$ $$\bar\rho = \rho, \quad \rho \leftarrow r^T r, \quad \beta =
\rho / \bar\rho, \quad p \leftarrow r + \beta p.$$

The divisions follow Lean's convention $t / 0 = 0$. -/
noncomputable def cgStep (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) : CGState n :=
  let q := A ⬝ s.p
  let α := s.ρ / ⟪s.p, q⟫_ℝ
  let r := s.r - α • q
  let ρ := ⟪r, r⟫_ℝ
  { x := s.x + α • s.p, r := r, ρ := ρ, p := r + (ρ / s.ρ) • s.p }

/-- **Table 2.1** of [fong2012cg], the initialization of Algorithm CG: $x = 0$, $r = b$,
$\rho = \|b\|^2$ and $p = b$. -/
noncomputable def cgInit (b : Vec n) : CGState n := { x := 0, r := b, ρ := ‖b‖ ^ 2, p := b }

/-- **Table 2.1** of [fong2012cg], Algorithm CG. For $A \in \mathbb{R}^{n \times n}$,
$b \in \mathbb{R}^n$ and $k \in \mathbb{N}$, the state $(x_k^C, r_k^C, \rho_k, p_k^C)$ of
Algorithm CG after $k$ iterations from the initialization `FongSaunders.cgInit`.

**Generalization.** The source stops when $r=0$. Here a state is defined for every index.
At termination $r=\rho=p=0$, and Lean's convention $t/0=0$ keeps the state constant. -/
noncomputable def cg (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) : CGState n :=
  (cgStep A)^[k] (cgInit b)

/-- After $0$ iterations, Algorithm CG is at its initialization. -/
@[simp] theorem cg_zero : cg A b 0 = cgInit b := rfl

/-- The state after $k + 1$ iterations of Algorithm CG is one iteration applied to the state after
$k$ iterations. -/
theorem cg_succ (k : ℕ) : cg A b (k + 1) = cgStep A (cg A b k) :=
  Function.iterate_succ_apply' _ _ _

/-- **Table 2.1** of [fong2012cg], the CG step length. For $k \ge 1$, the step length of iteration
$k$ of Algorithm CG is $$\alpha_k = \rho_{k-1} / (p_{k-1}^C)^T A p_{k-1}^C.$$

The value $\alpha_0 = 0$ is a convention, and the paper does not use it.

**Reading.** Matches the printed CG quotient and additionally defines the zeroth coefficient.
-/
noncomputable def cgAlpha (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (cg A b k).ρ / ⟪(cg A b k).p, A ⬝ (cg A b k).p⟫_ℝ

/-- **Table 2.1** of [fong2012cg], the CG direction coefficient. For $k \ge 1$, the coefficient of
iteration $k$ of Algorithm CG is $\beta_k = \rho_k / \rho_{k-1}$.

The value $\beta_0 = 0$ is a convention.

**Reading.** Matches the printed CG quotient and additionally defines the zeroth coefficient.
-/
noncomputable def cgBeta (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (cg A b (k + 1)).ρ / (cg A b k).ρ

/-- **Section 2.3** of [fong2012cg], termination of Algorithm CG. The termination step $\ell$ of
Algorithm CG is the least $k$ with $r_k^C = 0$.

**Reading.** The printed algorithm stops at a zero residual. For general $A$ the set of
zero-residual indices can be empty, and the total definition then gives $0$. For positive
definite $A$, `FongSaunders.cg_residual_cgTerm` establishes termination. -/
noncomputable def cgTerm (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ :=
  sInf {k | (cg A b k).r = 0}

/-! ### Algorithm CR (Table 2.1, second and third columns) -/

/-- **Table 2.1** of [fong2012cg], the state of Algorithm CR. A state consists of an iterate $x$, a
residual $r$, the vector $s = Ar$, the scalar $\rho = r^T s$, a search direction $p$ and the
vector $q = Ap$. -/
structure CRState (n : ℕ) where
  /-- The iterate $x_k$. -/
  x : Vec n
  /-- The residual $r_k = b - A x_k$. -/
  r : Vec n
  /-- The auxiliary vector $s_k = A r_k$. -/
  s : Vec n
  /-- The scalar $\rho_k = r_k^T s_k = r_k^T A r_k$. -/
  ρ : ℝ
  /-- The search direction $p_k$. -/
  p : Vec n
  /-- The auxiliary vector $q_k = A p_k$. -/
  q : Vec n

/-- **Table 2.1** of [fong2012cg], one iteration of Algorithm CR. From the state
$(x, r, s, \rho, p, q)$ the iteration computes $$\alpha = \rho / \|q\|^2, \quad x \leftarrow x +
\alpha p, \quad r \leftarrow r - \alpha q, \quad s = Ar,$$ $$\bar\rho = \rho, \quad \rho
\leftarrow r^T s, \quad \beta = \rho / \bar\rho, \quad p \leftarrow r + \beta p, \quad q
\leftarrow s + \beta q.$$

The divisions follow Lean's convention $t / 0 = 0$. -/
noncomputable def crStep (A : Matrix (Fin n) (Fin n) ℝ) (st : CRState n) : CRState n :=
  let α := st.ρ / ‖st.q‖ ^ 2
  let r := st.r - α • st.q
  let s := A ⬝ r
  let ρ := ⟪r, s⟫_ℝ
  { x := st.x + α • st.p, r := r, s := s, ρ := ρ,
    p := r + (ρ / st.ρ) • st.p, q := s + (ρ / st.ρ) • st.q }

/-- **Table 2.1** of [fong2012cg], the initialization of Algorithm CR: $x = 0$, $r = b$, $s = Ar$,
$\rho = r^T s$, $p = r$ and $q = s$. -/
noncomputable def crInit (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : CRState n :=
  { x := 0, r := b, s := A ⬝ b, ρ := ⟪b, A ⬝ b⟫_ℝ, p := b, q := A ⬝ b }

/-- **Table 2.1** of [fong2012cg], Algorithm CR. For $A \in \mathbb{R}^{n \times n}$,
$b \in \mathbb{R}^n$ and $k \in \mathbb{N}$, the state $(x_k, r_k, s_k, \rho_k, p_k, q_k)$ of
Algorithm CR after $k$ iterations from the initialization `FongSaunders.crInit`.

**Generalization.** The source stops when $r=0$. Here a state is defined for every index.
Lean's convention $t/0=0$ keeps it constant from the first zero residual onward. -/
noncomputable def cr (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) : CRState n :=
  (crStep A)^[k] (crInit A b)

/-- After $0$ iterations, Algorithm CR is at its initialization. -/
@[simp] theorem cr_zero : cr A b 0 = crInit A b := rfl

/-- The state after $k + 1$ iterations of Algorithm CR is one iteration applied to the state after
$k$ iterations. -/
theorem cr_succ (k : ℕ) : cr A b (k + 1) = crStep A (cr A b k) :=
  Function.iterate_succ_apply' _ _ _

/-- **Table 2.1** of [fong2012cg], the CR step length. For $k \ge 1$, the step length of iteration
$k$ of Algorithm CR is $\alpha_k = \rho_{k-1} / \|q_{k-1}\|^2$.

The value $\alpha_0 = 0$ is a convention.

**Reading.** Matches the source quotient and adds the value at zero.
-/
noncomputable def crAlpha (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (cr A b k).ρ / ‖(cr A b k).q‖ ^ 2

/-- **Table 2.1** of [fong2012cg], the CR direction coefficient. For $k \ge 1$, the coefficient of
iteration $k$ of Algorithm CR is $\beta_k = \rho_k / \rho_{k-1}$.

The value $\beta_0 = 0$ is a convention.

**Reading.** Matches the source quotient and adds the value at zero.
-/
noncomputable def crBeta (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (cr A b (k + 1)).ρ / (cr A b k).ρ

/-- **Section 2.3** of [fong2012cg], termination of Algorithm CR. The termination step $\ell$ of
Algorithm CR is the least $k$ with $r_k = 0$.

**Reading.** The printed algorithm stops at a zero residual. For general $A$ the set of
zero-residual indices can be empty, and the total definition then gives $0$. For positive
definite $A$, `FongSaunders.cr_residual_crTerm` establishes termination. -/
noncomputable def crTerm (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) : ℕ :=
  sInf {k | (cr A b k).r = 0}

/-!
### The identification of Algorithms CG and CR with the backbone recurrences

Both identifications hold for every matrix $A$: positive definiteness is not needed.
-/

/-- For every $A \in \mathbb{R}^{n \times n}$, $b$ and $k$, the state of Algorithm CG after $k$
iterations is the state of the backbone recurrence `CG.iterate` of `Matrix.toEuclideanLin A`
from $x_0 = 0$, with $\rho_k = \|r_k^C\|^2$. -/
theorem cg_eq_backbone (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) :
    cg A b k =
      { x := (CG.iterate (toEuclideanLin A) b 0 k).x,
        r := (CG.iterate (toEuclideanLin A) b 0 k).r,
        ρ := ‖(CG.iterate (toEuclideanLin A) b 0 k).r‖ ^ 2,
        p := (CG.iterate (toEuclideanLin A) b 0 k).p } := by
  induction k with
  | zero => simp [cgInit, CG.init]
  | succ k ih =>
    rw [cg_succ, ih, CG.iterate_succ]
    have halpha : ‖(CG.iterate (toEuclideanLin A) b 0 k).r‖ ^ 2 /
        ⟪(CG.iterate (toEuclideanLin A) b 0 k).p,
          A ⬝ (CG.iterate (toEuclideanLin A) b 0 k).p⟫_ℝ
        = CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k) := by
      rw [CG.alpha, real_inner_self_eq_norm_sq, real_inner_comm]
    have hbeta : ‖(CG.step (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k)).r‖ ^ 2 /
        ‖(CG.iterate (toEuclideanLin A) b 0 k).r‖ ^ 2
        = CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k) := by
      rw [CG.beta, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    simp only [cgStep, mulVecE_eq, halpha, real_inner_self_eq_norm_sq, ← CG.step_r]
    refine CGState.mk.injEq .. ▸ ⟨rfl, rfl, rfl, ?_⟩
    rw [hbeta]
    exact (CG.step_p _ _).symm

/-- For every $A \in \mathbb{R}^{n \times n}$, $b$ and $k$, the state of Algorithm CR after $k$
iterations is the state of the backbone recurrence `CR.iterate` of `Matrix.toEuclideanLin A`
from $x_0 = 0$, with $s_k = A r_k$ and $\rho_k = r_k^T A r_k$. -/
theorem cr_eq_backbone (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) :
    cr A b k =
      { x := (CR.iterate (toEuclideanLin A) b 0 k).x,
        r := (CR.iterate (toEuclideanLin A) b 0 k).r,
        s := A ⬝ (CR.iterate (toEuclideanLin A) b 0 k).r,
        ρ := ⟪(CR.iterate (toEuclideanLin A) b 0 k).r,
          A ⬝ (CR.iterate (toEuclideanLin A) b 0 k).r⟫_ℝ,
        p := (CR.iterate (toEuclideanLin A) b 0 k).p,
        q := (CR.iterate (toEuclideanLin A) b 0 k).q } := by
  induction k with
  | zero => simp [crInit, CR.iterate, CR.init]
  | succ k ih =>
    rw [cr_succ, ih, CR.iterate_succ]
    have halpha : ⟪(CR.iterate (toEuclideanLin A) b 0 k).r,
        A ⬝ (CR.iterate (toEuclideanLin A) b 0 k).r⟫_ℝ /
          ‖(CR.iterate (toEuclideanLin A) b 0 k).q‖ ^ 2
        = CR.alpha (toEuclideanLin A) (CR.iterate (toEuclideanLin A) b 0 k) := by
      rw [CR.alpha, real_inner_self_eq_norm_sq]
    simp only [crStep, halpha]
    rfl

/-! ### The components of the two identifications -/

/-- The CG iterate $x_k^C$ is the iterate of the backbone recurrence `CG.iterate` from $x_0 = 0$. -/
@[simp] theorem cg_x (k : ℕ) : (cg A b k).x = (CG.iterate (toEuclideanLin A) b 0 k).x := by
  rw [cg_eq_backbone]

/-- The CG residual $r_k^C$ is the residual of the backbone recurrence `CG.iterate` from $x_0 = 0$.
-/
@[simp] theorem cg_r (k : ℕ) : (cg A b k).r = (CG.iterate (toEuclideanLin A) b 0 k).r := by
  rw [cg_eq_backbone]

/-- The CG direction $p_k^C$ is the direction of the backbone recurrence `CG.iterate` from
$x_0 = 0$. -/
@[simp] theorem cg_p (k : ℕ) : (cg A b k).p = (CG.iterate (toEuclideanLin A) b 0 k).p := by
  rw [cg_eq_backbone]

/-- In Algorithm CG, $\rho_k = \|r_k^C\|^2$ for every $k$. -/
theorem cg_rho (k : ℕ) : (cg A b k).ρ = ‖(cg A b k).r‖ ^ 2 := by
  rw [cg_eq_backbone]

/-- The CR iterate $x_k$ is the iterate of the backbone recurrence `CR.iterate` from $x_0 = 0$. -/
@[simp] theorem cr_x (k : ℕ) : (cr A b k).x = (CR.iterate (toEuclideanLin A) b 0 k).x := by
  rw [cr_eq_backbone]

/-- The CR residual $r_k$ is the residual of the backbone recurrence `CR.iterate` from $x_0 = 0$. -/
@[simp] theorem cr_r (k : ℕ) : (cr A b k).r = (CR.iterate (toEuclideanLin A) b 0 k).r := by
  rw [cr_eq_backbone]

/-- The CR direction $p_k$ is the direction of the backbone recurrence `CR.iterate` from $x_0 = 0$.
-/
@[simp] theorem cr_p (k : ℕ) : (cr A b k).p = (CR.iterate (toEuclideanLin A) b 0 k).p := by
  rw [cr_eq_backbone]

/-- The CR vector $q_k$ is the vector $q_k$ of the backbone recurrence `CR.iterate` from $x_0 = 0$.
-/
@[simp] theorem cr_q (k : ℕ) : (cr A b k).q = (CR.iterate (toEuclideanLin A) b 0 k).q := by
  rw [cr_eq_backbone]

/-- In Algorithm CR, $s_k = A r_k$ for every $k$. -/
theorem cr_s (k : ℕ) : (cr A b k).s = A ⬝ (cr A b k).r := by
  rw [cr_eq_backbone]

/-- In Algorithm CR, $\rho_k = r_k^T A r_k$ for every $k$, as in (2.2) of [fong2012cg]. -/
theorem cr_rho (k : ℕ) : (cr A b k).ρ = ⟪(cr A b k).r, A ⬝ (cr A b k).r⟫_ℝ := by
  rw [cr_eq_backbone]

/-- In Algorithm CR, $q_k = A p_k$ for every $k$. -/
theorem cr_q_eq (k : ℕ) : (cr A b k).q = A ⬝ (cr A b k).p := by
  rw [cr_q, cr_p]
  exact CR.q_eq _ _ _ k

/-- In Algorithm CG, the residual of the state is the true residual: $r_k^C = b - A x_k^C$. -/
theorem cg_residual_eq (k : ℕ) : (cg A b k).r = b - A ⬝ (cg A b k).x := by
  rw [cg_r, cg_x]
  exact CG.residual_eq _ _ _ k

/-- In Algorithm CR, the residual of the state is the true residual: $r_k = b - A x_k$. -/
theorem cr_residual_eq (k : ℕ) : (cr A b k).r = b - A ⬝ (cr A b k).x := by
  rw [cr_r, cr_x]
  exact CR.residual_eq _ _ _ k

/-- The CG step length $\alpha_{k+1}$ is the backbone step length `CG.alpha` at the state of
`CG.iterate` after $k$ iterations. -/
theorem cgAlpha_eq (k : ℕ) :
    cgAlpha A b (k + 1) = CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k) := by
  rw [cgAlpha, cg_rho, cg_r, cg_p, CG.alpha, real_inner_self_eq_norm_sq, real_inner_comm]

/-- The CG coefficient $\beta_{k+1}$ is the backbone coefficient `CG.beta` at the state of
`CG.iterate` after $k$ iterations. -/
theorem cgBeta_eq (k : ℕ) :
    cgBeta A b (k + 1) = CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b 0 k) := by
  rw [cgBeta, cg_rho, cg_rho, cg_r, cg_r, CG.beta, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, CG.iterate_succ]

/-- The CR step length $\alpha_{k+1}$ is the backbone step length `CR.alpha` at the state of
`CR.iterate` after $k$ iterations. -/
theorem crAlpha_eq (k : ℕ) :
    crAlpha A b (k + 1) = CR.alpha (toEuclideanLin A) (CR.iterate (toEuclideanLin A) b 0 k) := by
  rw [crAlpha, cr_rho, cr_r, cr_q, CR.alpha, real_inner_self_eq_norm_sq]

/-! ### MINRES iterates (2.1) -/

/-- **Equation (2.1)** of [fong2012cg], MINRES iterates. For $A \in \mathbb{R}^{n \times n}$,
$b \in \mathbb{R}^n$ and $k \in \mathbb{N}$, a vector $x$ is a **MINRES iterate** at step $k$ if
$x \in \mathcal{K}_k(A, b)$ and $$\|b - Ax\| \le \|b - Ay\| \quad \text{for all } y \in
\mathcal{K}_k(A, b).$$

**Generalization.** The source applies this minimization to nonsingular symmetric systems.
The predicate takes any real matrix, so it also expresses residual minimization for
singular and nonsymmetric systems.

The theorems "for MINRES" are stated for every
sequence $(x_k)$ of MINRES iterates. `FongSaunders.isMINRESIterate_iff` identifies the
definition with the backbone `Krylov.IsMinResidualIterate`. -/
def IsMINRESIterate (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (k : ℕ) (x : Vec n) : Prop :=
  x ∈ krylov A b k ∧ ∀ y ∈ krylov A b k, ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ y‖

/-- For every $A$, $x$ is a MINRES iterate at step $k$ if and only if it satisfies the backbone
specification `Krylov.IsMinResidualIterate` of `Matrix.toEuclideanLin A` with $x_0 = 0$. -/
theorem isMINRESIterate_iff {k : ℕ} {x : Vec n} :
    IsMINRESIterate A b k x ↔ Krylov.IsMinResidualIterate (toEuclideanLin A) b 0 k x := by
  have hK : Krylov.subspace (toEuclideanLin A) (b - toEuclideanLin A 0) k = krylov A b k := by
    rw [krylov_eq, map_zero, sub_zero]
  constructor
  · rintro ⟨hmem, hmin⟩
    exact ⟨by rw [sub_zero, hK]; exact hmem, fun y hy => hmin y (by rwa [sub_zero, hK] at hy)⟩
  · rintro ⟨hmem, hmin⟩
    rw [sub_zero, hK] at hmem
    exact ⟨hmem, fun y hy => hmin y (by rw [sub_zero, hK]; exact hy)⟩

/-- **Section 2.2** of [fong2012cg], the residual of MINRES. If $x$ is a MINRES iterate at step $k$
and $y \in \mathcal{K}_k(A, b)$, then $$\|b - Ax\| \le \|b - Ay\|.$$

This holds by the definition `FongSaunders.IsMINRESIterate`. -/
theorem minres_norm_residual_le {k : ℕ} {x y : Vec n} (hx : IsMINRESIterate A b k x)
    (hy : y ∈ krylov A b k) : ‖b - A ⬝ x‖ ≤ ‖b - A ⬝ y‖ := hx.2 y hy

/-! ### One-step unfoldings of the two recurrences -/

/-- In Algorithm CG, the conventional value is $\alpha_0 = 0$. -/
@[simp] theorem cgAlpha_zero : cgAlpha A b 0 = 0 := rfl

/-- In Algorithm CG, the conventional value is $\beta_0 = 0$. -/
@[simp] theorem cgBeta_zero : cgBeta A b 0 = 0 := rfl

/-- In Algorithm CR, the conventional value is $\alpha_0 = 0$. -/
@[simp] theorem crAlpha_zero : crAlpha A b 0 = 0 := rfl

/-- In Algorithm CR, the conventional value is $\beta_0 = 0$. -/
@[simp] theorem crBeta_zero : crBeta A b 0 = 0 := rfl

/-- In Algorithm CR, $\alpha_{k+1} = \rho_k / \|q_k\|^2$, the step length of Table 2.1. -/
theorem crAlpha_succ (k : ℕ) : crAlpha A b (k + 1) = (cr A b k).ρ / ‖(cr A b k).q‖ ^ 2 := rfl

/-- In Algorithm CR, $\beta_{k+1} = \rho_{k+1} / \rho_k$, the coefficient of Table 2.1.

The backbone recurrence `CR.step` uses this quotient without naming it, so the sign of $\beta_k$
(Theorem 2.2(b)) is proved here. -/
theorem crBeta_succ (k : ℕ) : crBeta A b (k + 1) = (cr A b (k + 1)).ρ / (cr A b k).ρ := rfl

/-- In Algorithm CR, $x_{k+1} = x_k + \alpha_{k+1} p_k$, as in Table 2.1. -/
theorem cr_succ_x (k : ℕ) :
    (cr A b (k + 1)).x = (cr A b k).x + crAlpha A b (k + 1) • (cr A b k).p := by
  rw [cr_succ, crAlpha]
  rfl

/-- In Algorithm CR, $r_{k+1} = r_k - \alpha_{k+1} q_k$, as in Table 2.1. -/
theorem cr_succ_r (k : ℕ) :
    (cr A b (k + 1)).r = (cr A b k).r - crAlpha A b (k + 1) • (cr A b k).q := by
  rw [cr_succ, crAlpha]
  rfl

/-- In Algorithm CR, $p_{k+1} = r_{k+1} + \beta_{k+1} p_k$, as in Table 2.1. -/
theorem cr_succ_p (k : ℕ) :
    (cr A b (k + 1)).p = (cr A b (k + 1)).r + crBeta A b (k + 1) • (cr A b k).p := by
  rw [crBeta, cr_succ]
  rfl

/-- In Algorithm CR, $q_{k+1} = s_{k+1} + \beta_{k+1} q_k$, as in Table 2.1. -/
theorem cr_succ_q (k : ℕ) :
    (cr A b (k + 1)).q = (cr A b (k + 1)).s + crBeta A b (k + 1) • (cr A b k).q := by
  rw [crBeta, cr_succ]
  rfl

/-! ### CG minimizes $\phi$, equivalently the energy norm of the error (Section 2.1) -/

/-- If $A$ is positive definite, then $x_k^C$ satisfies the backbone Galerkin specification
`Krylov.IsGalerkinIterate` on $\mathcal{K}_k(A, b)$ with $x_0 = 0$. -/
theorem cg_isGalerkinIterate (hA : A.PosDef) (k : ℕ) :
    Krylov.IsGalerkinIterate (toEuclideanLin A) b 0 k (cg A b k).x := by
  rw [cg_x]
  exact CG.isGalerkinIterate b 0 (isSymmetricCoercive_of_posDef hA) k

/-- **Section 2.1** of [fong2012cg], the CG subspace. If $A \in \mathbb{R}^{n \times n}$ is positive
definite, then for every $k$ the CG iterate lies in the Krylov subspace: $$x_k^C \in
\mathcal{K}_k(A, b).$$
-/
theorem cg_mem_krylov (hA : A.PosDef) (k : ℕ) : (cg A b k).x ∈ krylov A b k :=
  sub_zero_mem_subspace_iff.1 (cg_isGalerkinIterate hA k).mem

/-- **Section 2.1** of [fong2012cg], the quadratic in terms of $x^*$. Let
$A \in \mathbb{R}^{n \times n}$, $b \in \mathbb{R}^n$ and $x^* \in \mathbb{R}^n$ with
$Ax^* = b$. Then for every $x$, $$2\phi(x) = x^T A x - 2\,x^T A x^*.$$

No symmetry of $A$ is needed. -/
theorem two_phi_eq {xstar x : Vec n} (hstar : A ⬝ xstar = b) :
    2 * phi A b x = ⟪x, A ⬝ x⟫_ℝ - 2 * ⟪x, A ⬝ xstar⟫_ℝ := by
  rw [phi, ← hstar, real_inner_comm (A ⬝ xstar) x]
  ring

/-- **Section 2.1** of [fong2012cg], the quadratic and the energy norm of the error. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite, and let $Ax^* = b$. Then for every $x$,
$$\|x^* - x\|_A^2 = 2\phi(x) + (x^*)^T A x^*.$$

This identity is the reason why minimizing $\phi$ is the same as minimizing $\|x^* - x\|_A$. -/
theorem energyNorm_sq_eq_two_phi_add (hA : A.PosDef) {xstar x : Vec n} (hstar : A ⬝ xstar = b) :
    energyNorm A (xstar - x) ^ 2 = 2 * phi A b x + ⟪xstar, A ⬝ xstar⟫_ℝ := by
  have h1 : ⟪xstar, A ⬝ x⟫_ℝ = ⟪x, A ⬝ xstar⟫_ℝ :=
    (inner_mulVecE_comm (hA.isSymm) xstar x).trans (real_inner_comm x (A ⬝ xstar))
  rw [energyNorm_sq hA, two_phi_eq hstar, mulVecE_sub, inner_sub_left, inner_sub_right,
    inner_sub_right, h1]
  ring

/-- **Section 2.1** of [fong2012cg], the two minimization problems. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite, let $Ax^* = b$, and let $k \in \mathbb{N}$
and $x \in \mathbb{R}^n$. Then $\phi(x) \le \phi(y)$ for all $y \in \mathcal{K}_k(A, b)$ if and
only if $$\|x^* - x\|_A \le \|x^* - y\|_A \quad \text{for all } y \in \mathcal{K}_k(A, b).$$

Neither side requires $x \in \mathcal{K}_k(A, b)$: `IsMinOn` only compares values. -/
theorem isMinOn_phi_iff_energyNorm_min (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b)
    {k : ℕ} {x : Vec n} :
    IsMinOn (phi A b) (krylov A b k) x ↔
      ∀ y ∈ krylov A b k, energyNorm A (xstar - x) ≤ energyNorm A (xstar - y) := by
  have key : ∀ u v : Vec n,
      (phi A b u ≤ phi A b v ↔ energyNorm A (xstar - u) ≤ energyNorm A (xstar - v)) := by
    intro u v
    have hu := energyNorm_sq_eq_two_phi_add hA hstar (x := u)
    have hv := energyNorm_sq_eq_two_phi_add hA hstar (x := v)
    have hnu := energyNorm_nonneg A (xstar - u)
    have hnv := energyNorm_nonneg A (xstar - v)
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  rw [isMinOn_iff]
  exact forall_congr' fun y => imp_congr_right fun _ => key x y

/-- If $A$ is positive definite and $x$ satisfies the backbone Galerkin specification
`Krylov.IsGalerkinIterate` on $\mathcal{K}_k(A, b)$ with $x_0 = 0$, then $x$ minimizes $\phi$
over $\mathcal{K}_k(A, b)$. -/
theorem isMinOn_phi_of_isGalerkinIterate (hA : A.PosDef) {k : ℕ} {x : Vec n}
    (hx : Krylov.IsGalerkinIterate (toEuclideanLin A) b 0 k x) :
    IsMinOn (phi A b) (krylov A b k) x := by
  rw [isMinOn_iff]
  intro y hy
  rw [phi_eq, phi_eq]
  exact IsGalerkin.quadratic_le (isSymmetricCoercive_of_posDef hA) hx
    (sub_zero_mem_subspace_iff.2 hy)

/-- If $A$ is positive definite, then $x$ satisfies the backbone Galerkin specification
`Krylov.IsGalerkinIterate` on $\mathcal{K}_k(A, b)$ with $x_0 = 0$ if and only if
$x \in \mathcal{K}_k(A, b)$ and $x$ minimizes $\phi$ over $\mathcal{K}_k(A, b)$. -/
theorem isGalerkinIterate_iff_isMinOn_phi (hA : A.PosDef) {k : ℕ} {x : Vec n} :
    Krylov.IsGalerkinIterate (toEuclideanLin A) b 0 k x ↔
      x ∈ krylov A b k ∧ IsMinOn (phi A b) (krylov A b k) x := by
  have hstar : A ⬝ xstar A b = b := mulVecE_xstar hA
  refine ⟨fun hx => ⟨sub_zero_mem_subspace_iff.1 hx.mem,
    isMinOn_phi_of_isGalerkinIterate hA hx⟩, ?_⟩
  rintro ⟨hmem, hmin⟩
  refine (IsGalerkin.iff_energyNorm_min (isSymmetricCoercive_of_posDef hA) hstar).2
    ⟨sub_zero_mem_subspace_iff.2 hmem, fun y hy => ?_⟩
  have h := (isMinOn_phi_iff_energyNorm_min hA hstar).1 hmin y (sub_zero_mem_subspace_iff.1 hy)
  rwa [energyNorm_eq, energyNorm_eq] at h

/-- **Section 2.1** of [fong2012cg], CG minimizes $\phi$. If $A \in \mathbb{R}^{n \times n}$ is
positive definite, then for every $k$, $$\phi(x_k^C) \le \phi(y) \quad \text{for all } y \in
\mathcal{K}_k(A, b).$$
-/
theorem cg_isMinOn_phi (hA : A.PosDef) (k : ℕ) :
    IsMinOn (phi A b) (krylov A b k) (cg A b k).x :=
  isMinOn_phi_of_isGalerkinIterate hA (cg_isGalerkinIterate hA k)

/-- **Section 2.1** of [fong2012cg], CG minimizes the energy norm of the error. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite, and let $Ax^* = b$. Then for every $k$ and
every $y \in \mathcal{K}_k(A, b)$, $$\|x^* - x_k^C\|_A \le \|x^* - y\|_A.$$
-/
theorem cg_energyNorm_le (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) (k : ℕ)
    {y : Vec n} (hy : y ∈ krylov A b k) :
    energyNorm A (xstar - (cg A b k).x) ≤ energyNorm A (xstar - y) :=
  (isMinOn_phi_iff_energyNorm_min hA hstar).1 (cg_isMinOn_phi hA k) y hy

/-- **Section 2.1** of [fong2012cg], uniqueness of the CG iterate. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite. If $x \in \mathcal{K}_k(A, b)$ and
$\phi(x) \le \phi(y)$ for all $y \in \mathcal{K}_k(A, b)$, then $x = x_k^C$. -/
theorem cg_unique_min (hA : A.PosDef) {k : ℕ} {x : Vec n} (hx : x ∈ krylov A b k)
    (hmin : IsMinOn (phi A b) (krylov A b k) x) : x = (cg A b k).x := by
  rw [cg_x]
  exact Krylov.IsGalerkinIterate.eq_CG_iterate (isSymmetricCoercive_of_posDef hA)
    ((isGalerkinIterate_iff_isMinOn_phi hA).2 ⟨hx, hmin⟩)

/-! ### MINRES minimizes the residual, and CR and MINRES coincide (Section 2.2) -/

/-- **Section 2.2** of [fong2012cg], CR is MINRES. If $A \in \mathbb{R}^{n \times n}$ is positive
definite, then for every $k$ the CR iterate $x_k$ is a MINRES iterate at step $k$: it lies in
$\mathcal{K}_k(A, b)$ and minimizes $\|b - Ax\|$ there. -/
theorem cr_isMINRESIterate (hA : A.PosDef) (k : ℕ) : IsMINRESIterate A b k (cr A b k).x := by
  rw [isMINRESIterate_iff, cr_x]
  exact CR.isMinResidualIterate b 0 (isSymmetricCoercive_of_posDef hA) k

/-- **Section 2.2** of [fong2012cg], uniqueness of MINRES iterates. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite. If $x$ and $y$ are both MINRES iterates at
step $k$, then $x = y$.

**Reading.** The source describes MINRES on nonsingular symmetric systems. This uniqueness
result uses positive definiteness, the case used to identify MINRES with CR. -/
theorem isMINRESIterate_unique (hA : A.PosDef) {k : ℕ} {x y : Vec n}
    (hx : IsMINRESIterate A b k x) (hy : IsMINRESIterate A b k y) : x = y := by
  rw [Krylov.IsMinResidualIterate.eq_CR_iterate (isSymmetricCoercive_of_posDef hA)
      (isMINRESIterate_iff.1 hx),
    Krylov.IsMinResidualIterate.eq_CR_iterate (isSymmetricCoercive_of_posDef hA)
      (isMINRESIterate_iff.1 hy)]

/-- **Section 2.2** of [fong2012cg], CR and MINRES coincide. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite. For every $k$, a vector $x$ is a MINRES iterate at step $k$ if and only if
$x = x_k$, the CR iterate.

The paper says that CR and MINRES must generate the same iterates on symmetric positive definite
systems. -/
theorem isMINRESIterate_iff_eq_cr (hA : A.PosDef) (k : ℕ) (x : Vec n) :
    IsMINRESIterate A b k x ↔ x = (cr A b k).x :=
  ⟨fun hx => isMINRESIterate_unique hA hx (cr_isMINRESIterate hA k),
    fun hx => hx ▸ cr_isMINRESIterate hA k⟩

/-! ### Well-definedness and termination (Section 2.3) -/

/-- **Section 2.3** of [fong2012cg], CG is well defined. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite. If $r_k^C \neq 0$, then the denominator of the next step length is positive:
$$(p_k^C)^T A p_k^C > 0.$$
-/
theorem cg_inner_p_q_pos (hA : A.PosDef) {k : ℕ} (hk : (cg A b k).r ≠ 0) :
    0 < ⟪(cg A b k).p, A ⬝ (cg A b k).p⟫_ℝ := by
  rw [cg_p]
  have h := CG.re_inner_apply_direction_pos b 0 (isSymmetricCoercive_of_posDef hA)
    (k := k) (by rwa [cg_r] at hk)
  rw [RCLike.re_to_real] at h
  rwa [real_inner_comm]

/-- **Equation (2.2)** of [fong2012cg], strict form; CR is well defined. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite. If $r_k \neq 0$, then
$\rho_k = r_k^T A r_k > 0$. -/
theorem cr_rho_pos (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) : 0 < (cr A b k).ρ := by
  rw [cr_rho]
  exact inner_mulVecE_self_pos hA hk

/-- **Section 2.3** of [fong2012cg], termination of CG. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, and let $\ell$ be the termination step of the Lanczos process for $A$ and
$b$. Then for every $k$, $$r_k^C = 0 \iff k \ge \ell.$$
-/
theorem cg_residual_eq_zero_iff (hA : A.PosDef) (k : ℕ) :
    (cg A b k).r = 0 ↔ lanczosTerm A b ≤ k := by
  rw [cg_r]
  constructor
  · intro h
    by_contra hlt
    exact CG.residual_ne_zero_of_lt_grade b 0
      (by rw [sub_mulVecE_zero]; exact not_le.1 hlt) h
  · intro h
    exact CG.residual_eq_zero_of_grade_le b 0 (isSymmetricCoercive_of_posDef hA)
      (by rwa [sub_mulVecE_zero])

/-- **Section 2.3** of [fong2012cg], termination of CR. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, and let $\ell$ be the termination step of the Lanczos process for $A$ and
$b$. Then for every $k$, $$r_k = 0 \iff k \ge \ell.$$
-/
theorem cr_residual_eq_zero_iff (hA : A.PosDef) (k : ℕ) :
    (cr A b k).r = 0 ↔ lanczosTerm A b ≤ k := by
  constructor
  · intro h
    have h2 := cr_residual_eq (A := A) (b := b) k
    rw [h] at h2
    have hx : A ⬝ (cr A b k).x = b := (sub_eq_zero.1 h2.symm).symm
    have hle := Krylov.grade_le_of_apply_eq
      (sub_zero_mem_subspace_iff.2 (cr_isMINRESIterate hA k).1) hx
    rwa [sub_mulVecE_zero] at hle
  · intro h
    rw [cr_r]
    exact CR.residual_eq_zero_of_grade_le b 0 (isSymmetricCoercive_of_posDef hA)
      (by rwa [sub_mulVecE_zero])

/-- If $A$ is positive definite, then Algorithm CR reaches its termination step: $r_\ell = 0$ for
$\ell$ = `FongSaunders.crTerm A b`. -/
theorem cr_residual_crTerm (hA : A.PosDef) : (cr A b (crTerm A b)).r = 0 := by
  have hne : {k | (cr A b k).r = 0}.Nonempty :=
    ⟨lanczosTerm A b, (cr_residual_eq_zero_iff hA _).2 le_rfl⟩
  rw [crTerm]
  exact Nat.sInf_mem hne

/-- If $A$ is positive definite, then Algorithm CG reaches its termination step: $r_\ell^C = 0$ for
$\ell$ = `FongSaunders.cgTerm A b`. -/
theorem cg_residual_cgTerm (hA : A.PosDef) : (cg A b (cgTerm A b)).r = 0 := by
  have hne : {k | (cg A b k).r = 0}.Nonempty :=
    ⟨lanczosTerm A b, (cg_residual_eq_zero_iff hA _).2 le_rfl⟩
  rw [cgTerm]
  exact Nat.sInf_mem hne

/-- **Section 2.3** of [fong2012cg], the termination step of CR. If $A \in \mathbb{R}^{n \times n}$
is positive definite, then the termination step of Algorithm CR is the termination step $\ell$
of the Lanczos process.

The paper says: "This $\ell$ is the same as the $\ell$ at which the Lanczos process terminates." -/
theorem crTerm_eq_grade (hA : A.PosDef) : crTerm A b = lanczosTerm A b :=
  le_antisymm (Nat.sInf_le ((cr_residual_eq_zero_iff hA _).2 le_rfl))
    ((cr_residual_eq_zero_iff hA _).1 (cr_residual_crTerm (b := b) hA))

/-- If $A$ is positive definite, then the termination step of Algorithm CG is the termination step
$\ell$ of the Lanczos process (Section 2.3 of [fong2012cg]). -/
theorem cgTerm_eq_grade (hA : A.PosDef) : cgTerm A b = lanczosTerm A b :=
  le_antisymm (Nat.sInf_le ((cg_residual_eq_zero_iff hA _).2 le_rfl))
    ((cg_residual_eq_zero_iff hA _).1 (cg_residual_cgTerm (b := b) hA))

/-- If $A$ is positive definite, then Algorithms CG and CR terminate at the same step (Section 2.3
of [fong2012cg]). -/
theorem cgTerm_eq_crTerm (hA : A.PosDef) : cgTerm A b = crTerm A b :=
  (cgTerm_eq_grade hA).trans (crTerm_eq_grade hA).symm

/-- **Section 2.3** of [fong2012cg], termination in at most $n$ steps. If
$A \in \mathbb{R}^{n \times n}$ is positive definite, then Algorithm CR terminates at a step
$\ell \le n$. -/
theorem crTerm_le (hA : A.PosDef) : crTerm A b ≤ n :=
  (crTerm_eq_grade hA).le.trans (lanczosTerm_le A b)

/-- If $A$ is positive definite, then Algorithm CG terminates at a step $\ell \le n$. -/
theorem cgTerm_le (hA : A.PosDef) : cgTerm A b ≤ n :=
  (cgTerm_eq_grade hA).le.trans (lanczosTerm_le A b)

/-- In Algorithm CR, for every matrix $A$, if $r_k = 0$ then $s_k = 0$, $\rho_k = 0$, $p_k = 0$ and
$q_k = 0$ (Section 2.3 of [fong2012cg]). -/
theorem cr_of_residual_eq_zero {k : ℕ} (h : (cr A b k).r = 0) :
    (cr A b k).s = 0 ∧ (cr A b k).ρ = 0 ∧ (cr A b k).p = 0 ∧ (cr A b k).q = 0 := by
  have hs : (cr A b k).s = 0 := by rw [cr_s, h, mulVecE_zero]
  have hρ : (cr A b k).ρ = 0 := by rw [cr_rho, h, inner_zero_left]
  refine ⟨hs, hρ, ?_, ?_⟩ <;> rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hb : b = 0 := h
    simp [crInit, hb]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [cr_succ_p, h, crBeta, hρ, zero_div, zero_smul, add_zero]
  · have hb : b = 0 := h
    simp [crInit, hb]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [cr_succ_q, hs, crBeta, hρ, zero_div, zero_smul, add_zero]

/-- **Section 2.3** of [fong2012cg], the state at termination. If $A \in \mathbb{R}^{n \times n}$ is
positive definite and $\ell$ is the termination step of Algorithm CR, then $$r_\ell = 0, \quad
s_\ell = 0, \quad \rho_\ell = 0, \quad p_\ell = 0, \quad q_\ell = 0, \quad \beta_\ell = 0.$$
-/
theorem cr_term_state (hA : A.PosDef) :
    (cr A b (crTerm A b)).r = 0 ∧ (cr A b (crTerm A b)).s = 0 ∧ (cr A b (crTerm A b)).ρ = 0 ∧
      (cr A b (crTerm A b)).p = 0 ∧ (cr A b (crTerm A b)).q = 0 ∧
      crBeta A b (crTerm A b) = 0 := by
  have hr := cr_residual_crTerm (b := b) hA
  obtain ⟨hs, hρ, hp, hq⟩ := cr_of_residual_eq_zero hr
  refine ⟨hr, hs, hρ, hp, hq, ?_⟩
  rcases Nat.eq_zero_or_pos (crTerm A b) with h0 | hpos
  · rw [h0, crBeta]
  · obtain ⟨m, hm⟩ : ∃ m, crTerm A b = m + 1 := ⟨crTerm A b - 1, by omega⟩
    rw [hm, crBeta, ← hm, hρ, zero_div]

/-- A CR state whose vectors and whose $\rho$ are all zero is a fixed point of one iteration of
Algorithm CR. -/
private theorem crStep_eq_self {st : CRState n} (hr : st.r = 0) (hs : st.s = 0) (hρ : st.ρ = 0)
    (hp : st.p = 0) (hq : st.q = 0) : crStep A st = st := by
  obtain ⟨x, r, s, ρ, p, q⟩ := st
  simp_all [crStep]

/-- **Section 2.3** of [fong2012cg], stationarity after termination. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite, and let $\ell$ be the termination step of
Algorithm CR. For every $k \ge \ell$, the state of Algorithm CR after $k$ iterations is the
state after $\ell$ iterations.

**Generalization.** The printed procedure ends at $\ell$. The totalized recurrence
extends it by keeping the terminal state constant. -/
theorem cr_stationary (hA : A.PosDef) {k : ℕ} (h : crTerm A b ≤ k) :
    cr A b k = cr A b (crTerm A b) := by
  obtain ⟨hr, hs, hρ, hp, hq, -⟩ := cr_term_state (A := A) (b := b) hA
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k _ ih => rw [cr_succ, ih, crStep_eq_self hr hs hρ hp hq]

/-! ### Theorem 2.1 -/

/-- **Theorem 2.1(a)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite,
and let $q_i$ be the vectors of Algorithm CR. For all $i \neq j$, $$q_i^T q_j = 0.$$

The statement holds for all indices, also beyond termination, where $q_i = 0$. -/
theorem theorem_2_1_a (hA : A.PosDef) {i j : ℕ} (hij : i ≠ j) :
    ⟪(cr A b i).q, (cr A b j).q⟫_ℝ = 0 := by
  rw [cr_q_eq, cr_q_eq]
  simp only [cr_p, mulVecE_eq]
  exact CR.inner_apply_direction_eq_zero b 0 (isSymmetricCoercive_of_posDef hA) hij

/-- **Theorem 2.1(b)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite,
and let $r_i$ and $q_j$ be the vectors of Algorithm CR. For all $i \ge j + 1$, $$r_i^T q_j =
0.$$
-/
theorem theorem_2_1_b (hA : A.PosDef) {i j : ℕ} (hij : j + 1 ≤ i) :
    ⟪(cr A b i).r, (cr A b j).q⟫_ℝ = 0 := by
  rw [cr_q_eq]
  simp only [cr_p, cr_r, mulVecE_eq]
  exact CR.inner_residual_apply_direction_eq_zero b 0 (isSymmetricCoercive_of_posDef hA) hij

/-- If $A$ is positive definite, then in Algorithm CR $r_k^T q_k = \rho_k$ for every $k$. This is
the CR analogue of the CG identity $r_k^T p_k = \|r_k\|^2$. -/
theorem cr_inner_residual_q (hA : A.PosDef) (k : ℕ) :
    ⟪(cr A b k).r, (cr A b k).q⟫_ℝ = (cr A b k).ρ := by
  rw [cr_q_eq, cr_rho]
  simp only [cr_p, cr_r, mulVecE_eq]
  exact CR.inner_residual_apply_direction_eq b 0 (isSymmetricCoercive_of_posDef hA) le_rfl

/-! ### Equation (2.2) and Theorem 2.2 -/

/-- **Equation (2.2)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite.
For every $i$, the scalar of Algorithm CR satisfies $$\rho_i = r_i^T A r_i \ge 0.$$

The identity $\rho_i = r_i^T A r_i$ is `FongSaunders.cr_rho`. -/
theorem equation_2_2 (hA : A.PosDef) (i : ℕ) : 0 ≤ (cr A b i).ρ := by
  rw [cr_rho]
  exact inner_mulVecE_self_nonneg hA _

/-- **Theorem 2.2(a)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite.
For every $i$, the step length of Algorithm CR satisfies $\alpha_i \ge 0$.

The statement includes the conventional value $\alpha_0 = 0$. The strict form is
`FongSaunders.theorem_2_2_a_strict`. -/
theorem theorem_2_2_a (hA : A.PosDef) (i : ℕ) : 0 ≤ crAlpha A b i := by
  cases i with
  | zero => simp
  | succ k => rw [crAlpha_succ]; exact div_nonneg (equation_2_2 hA k) (sq_nonneg _)

/-- **Theorem 2.2(b)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite.
For every $i$, the coefficient of Algorithm CR satisfies $\beta_i \ge 0$.

The statement includes the conventional value $\beta_0 = 0$. -/
theorem theorem_2_2_b (hA : A.PosDef) (i : ℕ) : 0 ≤ crBeta A b i := by
  cases i with
  | zero => simp
  | succ k => rw [crBeta_succ]; exact div_nonneg (equation_2_2 hA (k + 1)) (equation_2_2 hA k)

/-- **Theorem 2.2(c)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite.
For all $i$ and $j$, the vectors of Algorithm CR satisfy $$p_i^T q_j \ge 0.$$
-/
theorem theorem_2_2_c (hA : A.PosDef) (i j : ℕ) : 0 ≤ ⟪(cr A b i).p, (cr A b j).q⟫_ℝ := by
  rw [cr_q_eq]
  simp only [cr_p, mulVecE_eq]
  have h := CR.re_inner_direction_apply_direction_nonneg b 0
    (isSymmetricCoercive_of_posDef hA) i j
  rwa [RCLike.re_to_real] at h

/-- **Theorem 2.2(d)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite.
For all $i$ and $j$, the directions of Algorithm CR satisfy $$p_i^T p_j \ge 0.$$
-/
theorem theorem_2_2_d (hA : A.PosDef) (i j : ℕ) : 0 ≤ ⟪(cr A b i).p, (cr A b j).p⟫_ℝ := by
  simp only [cr_p]
  have h := CR.re_inner_direction_nonneg b 0 (isSymmetricCoercive_of_posDef hA) i j
  rwa [RCLike.re_to_real] at h

/-- **Theorem 2.2(e)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite.
For all $i$ and $j$, the iterates and the directions of Algorithm CR from $x_0 = 0$ satisfy
$$x_i^T p_j \ge 0.$$
-/
theorem theorem_2_2_e (hA : A.PosDef) (i j : ℕ) : 0 ≤ ⟪(cr A b i).x, (cr A b j).p⟫_ℝ := by
  simp only [cr_x, cr_p]
  have h := CR.re_inner_iterate_direction_nonneg b (isSymmetricCoercive_of_posDef hA) i j
  rwa [RCLike.re_to_real] at h

/-- **Theorem 2.2(f)** of [fong2012cg]. Let $A \in \mathbb{R}^{n \times n}$ be positive definite.
For all $i$ and $j$, the residuals and the directions of Algorithm CR satisfy $$r_i^T p_j \ge
0.$$
-/
theorem theorem_2_2_f (hA : A.PosDef) (i j : ℕ) : 0 ≤ ⟪(cr A b i).r, (cr A b j).p⟫_ℝ := by
  simp only [cr_r, cr_p]
  have h := CR.re_inner_residual_direction_nonneg b 0 (isSymmetricCoercive_of_posDef hA) i j
  rwa [RCLike.re_to_real] at h

/-- If $A$ is positive definite and $r_k \neq 0$, then the CR vector $q_k$ is nonzero, so the step
length $\alpha_{k+1}$ has a nonzero denominator. -/
theorem cr_q_ne_zero (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) : (cr A b k).q ≠ 0 := by
  intro h
  have hρ := cr_inner_residual_q (b := b) hA k
  rw [h, inner_zero_right] at hρ
  exact (cr_rho_pos hA hk).ne' hρ.symm

/-- If $A$ is positive definite and $r_k \neq 0$, then the CR search direction $p_k$ is nonzero. -/
theorem cr_direction_ne_zero (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) :
    (cr A b k).p ≠ 0 := fun h => cr_q_ne_zero hA hk (by rw [cr_q_eq, h, mulVecE_zero])

/-- If $A$ is positive definite and $r_k \neq 0$, then the CR step length satisfies
$\alpha_{k+1} > 0$. This is the strict form of Theorem 2.2(a) of [fong2012cg]. -/
theorem crAlpha_pos (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) :
    0 < crAlpha A b (k + 1) := by
  rw [crAlpha_succ]
  exact div_pos (cr_rho_pos hA hk) (pow_pos (norm_pos_iff.2 (cr_q_ne_zero hA hk)) 2)

/-- **Theorem 2.2(a)** of [fong2012cg], strict form. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, and let $\ell$ be the termination step of Algorithm CR. For $1 \le i \le \ell$, the
step length of Algorithm CR satisfies $\alpha_i > 0$. -/
theorem theorem_2_2_a_strict (hA : A.PosDef) {i : ℕ} (hi : 1 ≤ i) (hℓ : i ≤ crTerm A b) :
    0 < crAlpha A b i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  refine crAlpha_pos hA fun h => ?_
  rw [cr_residual_eq_zero_iff hA, ← crTerm_eq_grade hA] at h
  omega

/-! ### Theorem 2.3 -/

/-- **Theorem 2.3** of [fong2012cg], for CR. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, and let $x_k$ be the iterates of Algorithm CR. Then $\|x_k\|$ increases monotonically:
$$\|x_k\| \le \|x_l\| \quad \text{for } k \le l.$$
-/
theorem theorem_2_3_cr (hA : A.PosDef) : Monotone fun k => ‖(cr A b k).x‖ := by
  simp only [cr_x]
  exact CR.norm_iterate_monotone b (isSymmetricCoercive_of_posDef hA)

/-- **Theorem 2.3** of [fong2012cg], for MINRES. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, and let $(x_k)$ be a sequence such that each $x_k$ is a MINRES iterate at step $k$.
Then $\|x_k\|$ increases monotonically: $$\|x_k\| \le \|x_l\| \quad \text{for } k \le l.$$
-/
theorem theorem_2_3_minres (hA : A.PosDef) {x : ℕ → Vec n}
    (hx : ∀ k, IsMINRESIterate A b k (x k)) : Monotone fun k => ‖x k‖ :=
  Krylov.IsMinResidualIterate.norm_monotone (isSymmetricCoercive_of_posDef hA)
    fun k => isMINRESIterate_iff.1 (hx k)

/-- **Theorem 2.3** of [fong2012cg], strict form for CR. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite. If the CR residual satisfies $r_k \neq 0$, then $$\|x_k\| < \|x_{k+1}\|.$$

**Generalization.** The source proves the nonstrict inequality. A nonzero residual
ensures a nonzero step length and search direction, so the squared-norm increment has
a strictly positive term $\alpha_{k+1}^2\|p_k\|^2$.
-/
theorem theorem_2_3_strict (hA : A.PosDef) {k : ℕ} (hk : (cr A b k).r ≠ 0) :
    ‖(cr A b k).x‖ < ‖(cr A b (k + 1)).x‖ := by
  have hα := crAlpha_pos hA hk
  have hpn : 0 < ‖(cr A b k).p‖ := norm_pos_iff.2 (cr_direction_ne_zero hA hk)
  have h1 : 0 ≤ crAlpha A b (k + 1) * ⟪(cr A b k).x, (cr A b k).p⟫_ℝ :=
    mul_nonneg hα.le (theorem_2_2_e hA k k)
  have h2 : 0 < crAlpha A b (k + 1) ^ 2 * ‖(cr A b k).p‖ ^ 2 :=
    mul_pos (pow_pos hα 2) (pow_pos hpn 2)
  have hsq : ‖(cr A b k).x‖ ^ 2 < ‖(cr A b (k + 1)).x‖ ^ 2 := by
    rw [cr_succ_x, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hα, mul_pow]
    linarith
  nlinarith [norm_nonneg (cr A b k).x, norm_nonneg (cr A b (k + 1)).x]

/-! ### Theorem 2.4 -/

/-- **Theorem 2.4** of [fong2012cg], for CR. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, and let $Ax^* = b$. Then the error of the CR iterates decreases monotonically:
$$\|x^* - x_l\| \le \|x^* - x_k\| \quad \text{for } k \le l.$$
-/
theorem theorem_2_4_cr (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) :
    Antitone fun k => ‖xstar - (cr A b k).x‖ := by
  simp only [cr_x]
  exact CR.norm_error_antitone b 0 (isSymmetricCoercive_of_posDef hA) hstar

/-- **Theorem 2.4** of [fong2012cg], for MINRES. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, let $Ax^* = b$, and let $(x_k)$ be a sequence such that each $x_k$ is a MINRES iterate
at step $k$. Then the error decreases monotonically: $$\|x^* - x_l\| \le \|x^* - x_k\| \quad
\text{for } k \le l.$$
-/
theorem theorem_2_4_minres (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) {x : ℕ → Vec n}
    (hx : ∀ k, IsMINRESIterate A b k (x k)) : Antitone fun k => ‖xstar - x k‖ :=
  Krylov.IsMinResidualIterate.norm_error_antitone (isSymmetricCoercive_of_posDef hA)
    (fun k => isMINRESIterate_iff.1 (hx k)) hstar

/-! ### Theorem 2.5 -/

/-- **Theorem 2.5** of [fong2012cg], nonstrict form for CR. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, and let $Ax^* = b$. Then the energy norm of the error of the CR iterates
decreases monotonically: $$\|x^* - x_l\|_A \le \|x^* - x_k\|_A \quad \text{for } k \le l.$$

**Reading.** The source gives strict decrease until termination. This statement gives the
nonstrict inequality for the full extended sequence, whose error is zero after termination.
-/
theorem theorem_2_5_cr_antitone (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) :
    Antitone fun k => energyNorm A (xstar - (cr A b k).x) := by
  simp only [energyNorm_eq, cr_x]
  exact CR.energyNorm_error_antitone b 0 (isSymmetricCoercive_of_posDef hA) hstar

/-- **Theorem 2.5** of [fong2012cg], nonstrict form for MINRES. Let $A \in \mathbb{R}^{n \times n}$
be positive definite, let $Ax^* = b$, and let $(x_k)$ be a sequence such that each $x_k$ is a
MINRES iterate at step $k$. Then $$\|x^* - x_l\|_A \le \|x^* - x_k\|_A \quad \text{for } k \le
l.$$

**Reading.** The source gives strict decrease until termination. This statement gives the
nonstrict inequality for the full extended sequence, whose error is zero after termination.
-/
theorem theorem_2_5_minres_antitone (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b)
    {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k)) :
    Antitone fun k => energyNorm A (xstar - x k) := by
  simp only [energyNorm_eq]
  exact Krylov.IsMinResidualIterate.energyNorm_error_antitone (isSymmetricCoercive_of_posDef hA)
    (fun k => isMINRESIterate_iff.1 (hx k)) hstar

/-- **Theorem 2.5** of [fong2012cg], for CR. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, and let $Ax^* = b$. If the CR residual satisfies $r_k \neq 0$, then $$\|x^* -
x_{k+1}\|_A < \|x^* - x_k\|_A.$$

**Reading.** The strict decrease in the source applies to the run that ends at the first zero
residual. The extended sequence has zero error thereafter. The nonstrict statement for all
steps is `FongSaunders.theorem_2_5_cr_antitone`.
-/
theorem theorem_2_5_cr (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) {k : ℕ}
    (hk : (cr A b k).r ≠ 0) :
    energyNorm A (xstar - (cr A b (k + 1)).x) < energyNorm A (xstar - (cr A b k).x) := by
  have hα := crAlpha_pos hA hk
  have hpp : 0 < ⟪(cr A b k).p, A ⬝ (cr A b k).p⟫_ℝ :=
    inner_mulVecE_self_pos hA (cr_direction_ne_zero hA hk)
  have h1 : 0 ≤ 2 * crAlpha A b (k + 1) * ⟪(cr A b (k + 1)).r, (cr A b k).p⟫_ℝ := by
    have := mul_nonneg hα.le (theorem_2_2_f (b := b) hA (k + 1) k)
    linarith
  have h2 : 0 < crAlpha A b (k + 1) ^ 2 * ⟪(cr A b k).p, A ⬝ (cr A b k).p⟫_ℝ :=
    mul_pos (pow_pos hα 2) hpp
  have hAe : A ⬝ (xstar - (cr A b (k + 1)).x) = (cr A b (k + 1)).r := by
    rw [mulVecE_sub, hstar, ← cr_residual_eq]
  have hsplit : xstar - (cr A b k).x
      = (xstar - (cr A b (k + 1)).x) + crAlpha A b (k + 1) • (cr A b k).p := by
    rw [cr_succ_x]; abel
  have hsq : energyNorm A (xstar - (cr A b (k + 1)).x) ^ 2
      < energyNorm A (xstar - (cr A b k).x) ^ 2 := by
    rw [energyNorm_sq hA, energyNorm_sq hA, hsplit,
      inner_mulVecE_add_smul (hA.isSymm), hAe]
    linarith
  nlinarith [energyNorm_nonneg A (xstar - (cr A b k).x),
    energyNorm_nonneg A (xstar - (cr A b (k + 1)).x)]

/-- **Theorem 2.5** of [fong2012cg], for MINRES. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, let $Ax^* = b$, and let $(x_k)$ be a sequence such that each $x_k$ is a MINRES iterate
at step $k$. If $b - A x_k \neq 0$, then $$\|x^* - x_{k+1}\|_A < \|x^* - x_k\|_A.$$

**Reading.** The strict decrease in the source applies to the run that ends at the first zero
residual. The extended sequence has zero error thereafter. The nonstrict statement for all
steps is `FongSaunders.theorem_2_5_minres_antitone`.
-/
theorem theorem_2_5_minres (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) {x : ℕ → Vec n}
    (hx : ∀ k, IsMINRESIterate A b k (x k)) {k : ℕ} (hk : b - A ⬝ x k ≠ 0) :
    energyNorm A (xstar - x (k + 1)) < energyNorm A (xstar - x k) := by
  have he : ∀ j, x j = (cr A b j).x := fun j => (isMINRESIterate_iff_eq_cr hA j (x j)).1 (hx j)
  rw [he, he]
  refine theorem_2_5_cr hA hstar (k := k) ?_
  rw [cr_residual_eq]
  rwa [he k] at hk

end FongSaunders
