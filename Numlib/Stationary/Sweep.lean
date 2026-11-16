/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Stationary.Splitting

/-!
# The classical stationary iterations as sweeps on vectors

Let $A = P - N$ be a splitting of a square matrix $A$ over a field (`Stationary.Splitting`, in
`Numlib.Stationary.Splitting`). The convergence theory is about the splitting, but a textbook writes
the method as a **sweep**: a map $x \mapsto x_{\mathrm{new}}$ on vectors, given by a componentwise
formula that a program executes. This module defines the sweeps of the classical methods and proves
that each sweep is the step $x \mapsto P^{-1}(N x + b)$ of its splitting ([quarteroni2000numerical],
(4.6); [saad2003iterative], (4.28)). A user needs this identification before a convergence theorem
about the splitting applies to a componentwise formula.

With $A = D + L + U$, where $D$ is the diagonal part, $L$ the strictly lower triangular part and $U$
the strictly upper triangular part of $A$, the SOR sweep with parameter $\omega$ is
$$x \mapsto (D + \omega L)^{-1} \bigl(((1 - \omega) D - \omega U) x + \omega b\bigr).$$
Read row by row, it is the recursion $y_i = \frac{\omega}{a_{ii}} \bigl(b_i - \sum_{j < i} a_{ij}
y_j - \sum_{j > i} a_{ij} x_j\bigr) + (1 - \omega) x_i$, and also the loop that relaxes the unknowns
one at a time. The case $\omega = 1$ is Gauss–Seidel. The JOR sweep (Jacobi at $\omega = 1$) and the
backward SOR sweep are treated in the same way, and a forward SOR sweep followed by a backward one
is the step of the SSOR splitting.

## Main definitions

* `Stationary.Splitting.mulVecStep`: the step $x \mapsto P^{-1}(N x + b)$ of a splitting.
* `Matrix.jorSweep`: the componentwise JOR formula, which is the Jacobi formula at $\omega = 1$.
* `Matrix.sorSweep`, `Matrix.backwardSorSweep`: the SOR and the backward SOR sweeps, which are the
  two Gauss–Seidel sweeps at $\omega = 1$.
* `Matrix.sorRelax`: the relaxation of one unknown in an SOR sweep.

## Main results

* `Stationary.Splitting.mulVecStep_eq_add_inv_mulVec`: the update form $x + P^{-1}(b - A x)$ of the
  step.
* `Stationary.Splitting.mulVecStep_eq_iterationOperator_mulVec_add`: the affine form
  $G x + P^{-1} b$ of the step.
* `Stationary.Splitting.mulVecStep_fixed_iff`: consistency, the fixed points of the step are the
  solutions of $A x = b$.
* `Stationary.Splitting.toLp_mulVecStep`: over `RCLike` scalars, the step is `Stationary.step` of
  the operator of $G$ on `EuclideanSpace`.
* `Matrix.sorSweep_apply`: the componentwise SOR recursion.
* `Matrix.jorSweep_eq_mulVecStep`, `Matrix.sorSweep_eq_mulVecStep`,
  `Matrix.backwardSorSweep_eq_mulVecStep`: each sweep is the step of `Matrix.jorSplitting`,
  `Matrix.sorSplitting` or `Matrix.backwardSorSplitting`.
* `Matrix.ssorSweep_eq_mulVecStep`: a forward SOR sweep followed by a backward one is the step of
  `Matrix.ssorSplitting`.
* `Matrix.foldl_sorRelax_eq_sorSweep`: the loop of relaxations over `Fin m`, in the natural order,
  is the SOR sweep.

## Implementation notes

* The SOR sweeps are defined by their matrix formula, and the componentwise recursion is a theorem
  about them. The recursion follows by reading the triangular system row by row along the linear
  order of the index type. This keeps the definitions total and independent of the index type. The
  components of the JOR sweep do not depend on each other, so the JOR sweep is defined
  componentwise.
* All statements are for `Matrix n n 𝕜` over a field, with vectors `n → 𝕜`. The linear order
  `[LinearOrder n]` is the order of the sweep. No analysis enters, except in the transport
  `Stationary.Splitting.toLp_mulVecStep` to `EuclideanSpace`, through which the theory of
  `Numlib.Stationary.Basic` applies.
-/

open Finset

namespace Stationary.Splitting

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [Field 𝕜] {A : Matrix n n 𝕜}

open Matrix

/-- One **step of a splitting iteration**. For a splitting $A = P - N$ of a square matrix over a
field and vectors $b$, $x$,
$$\mathrm{step}(x) = P^{-1}(N x + b),$$
so that $x_{k+1} = \mathrm{step}(x_k)$ solves $P x_{k+1} = N x_k + b$
([quarteroni2000numerical], (4.6); [saad2003iterative], (4.28)).

The matrix $P$ is the part `m` of the splitting, $N$ is `Stationary.Splitting.n`, and $P^{-1}$
is the matrix inverse. -/
noncomputable def mulVecStep (s : Splitting A) (b x : n → 𝕜) : n → 𝕜 :=
  s.m⁻¹ *ᵥ (s.n *ᵥ x + b)

variable (s : Splitting A) (b x : n → 𝕜)

/-- The update form of the step of a splitting $A = P - N$:
$$\mathrm{step}(x) = x + P^{-1}(b - A x),$$
so that $x_{k+1} = x_k + P^{-1} r_k$ with the residual $r_k = b - A x_k$
([quarteroni2000numerical], (4.7)–(4.8)). -/
theorem mulVecStep_eq_add_inv_mulVec : mulVecStep s b x = x + s.m⁻¹ *ᵥ (b - A *ᵥ x) := by
  have hn : s.n = s.m - A := rfl
  rw [mulVecStep, hn, sub_mulVec, show s.m *ᵥ x - A *ᵥ x + b = s.m *ᵥ x + (b - A *ᵥ x) by abel,
    mulVec_add, nonsing_inv_mulVec_mulVec s.isUnit]

/-- For the step of a splitting $A = P - N$, $P(\mathrm{step}(x) - x) = b - A x$. -/
theorem mulVec_mulVecStep_sub : s.m *ᵥ (mulVecStep s b x - x) = b - A *ᵥ x := by
  rw [mulVecStep_eq_add_inv_mulVec, add_sub_cancel_left, mulVec_nonsing_inv_mulVec s.isUnit]

/-- Let $A = P - N$ be a splitting, and let $x$, $y$, $b$ be vectors with $P(y - x) = b - A x$. Then
$y$ is the step of the splitting from $x$.

This is how a componentwise sweep is identified with the step of its splitting. -/
theorem mulVecStep_eq_of_mulVec_sub_eq {y : n → 𝕜} (h : s.m *ᵥ (y - x) = b - A *ᵥ x) :
    mulVecStep s b x = y := by
  rw [mulVecStep_eq_add_inv_mulVec, nonsing_inv_mulVec_eq s.isUnit h]
  abel

/-- The affine form of the step of a splitting $A = P - N$:
$$\mathrm{step}(x) = G x + P^{-1} b,$$
with the iteration matrix $G = P^{-1} N$ ([quarteroni2000numerical], the sentence after (4.6)). -/
theorem mulVecStep_eq_iterationOperator_mulVec_add :
    mulVecStep s b x = s.iterationOperator *ᵥ x + s.m⁻¹ *ᵥ b := by
  rw [mulVecStep, mulVec_add, Splitting.iterationOperator_eq, ← nonsing_inv_eq_ringInverse,
    ← mulVec_mulVec]

/-- **Consistency** of the splitting iteration. For a splitting $A = P - N$ and vectors $x$, $b$,
the vector $x$ is a fixed point of the step if and only if $A x = b$.

This is Definition 4.1 of [quarteroni2000numerical] for the method (4.6), and (4.29) of
[saad2003iterative]. -/
theorem mulVecStep_fixed_iff : mulVecStep s b x = x ↔ A *ᵥ x = b := by
  rw [mulVecStep_eq_add_inv_mulVec, add_eq_left]
  constructor
  · intro h
    have h' := congrArg (s.m *ᵥ ·) h
    simp only [mulVec_nonsing_inv_mulVec s.isUnit, mulVec_zero] at h'
    exact (sub_eq_zero.mp h').symm
  · intro h
    rw [h, sub_self, mulVec_zero]

/-- **Two steps compose into one.** Let $A = P_1 - N_1$, $A = P_2 - N_2$ and $A = P_t - N_t$ be
splittings of $A$ with
$$P_t^{-1} = P_2^{-1} (P_1 + P_2 - A) P_1^{-1}.$$
Then one step of the first splitting followed by one step of the second is one step of the
third: $\mathrm{step}_2(\mathrm{step}_1(x)) = \mathrm{step}_t(x)$.

The linear part is `Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq`, and the
constant term is `Stationary.Splitting.inverse_m_eq_iterationOperator_mul_inverse_add`. The
inverses in the hypothesis are `Ring.inverse`. -/
theorem mulVecStep_mulVecStep (s₁ s₂ t : Splitting A)
    (ht : Ring.inverse t.m = Ring.inverse s₂.m * (s₁.m + s₂.m - A) * Ring.inverse s₁.m) :
    mulVecStep s₂ b (mulVecStep s₁ b x) = mulVecStep t b x := by
  simp only [mulVecStep_eq_iterationOperator_mulVec_add, nonsing_inv_eq_ringInverse]
  rw [iterationOperator_eq_mul_of_inverse_m_eq s₁ s₂ t ht,
    inverse_m_eq_iterationOperator_mul_inverse_add s₁ s₂ t ht, mulVec_add, add_mulVec,
    ← mulVec_mulVec, ← mulVec_mulVec, add_assoc]

section EuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}

/-- Let $A = P - N$ be a splitting of a square matrix over an `RCLike` field, with iteration matrix
$G$. The step of the splitting from $x$, viewed in `EuclideanSpace`, is the affine step
$x \mapsto G x + f$ of `Stationary.step`, with $G$ acting as the operator
`Matrix.toEuclideanCLM` of $G$ and $f = P^{-1} b$.

Through this transport, the theory of `Numlib.Stationary.Basic` applies to a matrix iteration:
the propagation of the error, the convergence factors, and the a priori and a posteriori bounds.
The vectors are moved by `WithLp.toLp 2`. -/
theorem toLp_mulVecStep (s : Splitting A) (b x : n → 𝕜) :
    (WithLp.toLp 2 (mulVecStep s b x) : EuclideanSpace 𝕜 n) =
      Stationary.step (toEuclideanCLM (n := n) (𝕜 := 𝕜) s.iterationOperator)
        (WithLp.toLp 2 (s.m⁻¹ *ᵥ b)) (WithLp.toLp 2 x) := by
  rw [mulVecStep_eq_iterationOperator_mulVec_add, Stationary.step, toEuclideanCLM_toLp]
  rfl

end EuclideanSpace

end Stationary.Splitting

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {𝕜 : Type*} [Field 𝕜]

/-! ### The JOR and Jacobi sweeps -/

omit [LinearOrder n] in
/-- The **JOR sweep** with parameter $\omega$ for a square matrix $A$ and a right-hand side $b$: the
vector $x$ goes to the vector $y$ with
$$y_i = \frac{\omega}{a_{ii}} \Bigl(b_i - \sum_{j \neq i} a_{ij} x_j\Bigr) + (1 - \omega) x_i.$$

This is the display after (4.11) of [quarteroni2000numerical]. At $\omega = 1$ it is the Jacobi
formula (4.10). Each component depends only on the old vector, so the sweep is defined
componentwise. -/
noncomputable def jorSweep (A : Matrix n n 𝕜) (ω : 𝕜) (b x : n → 𝕜) : n → 𝕜 := fun i =>
  ω / A i i * (b i - ∑ j ∈ univ.erase i, A i j * x j) + (1 - ω) * x i

omit [LinearOrder n] in
/-- Let $A$ be a square matrix with invertible diagonal part $D$, and let $\omega \neq 0$. The JOR
sweep with parameter $\omega$ is the step of the JOR splitting $P = \omega^{-1} D$
(`Matrix.jorSplitting`).

Row $i$ of the equation $\omega^{-1} D (y - x) = b - A x$ is the formula of the sweep. -/
theorem jorSweep_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0)
    (b : n → 𝕜) : jorSweep A ω b = Splitting.mulVecStep (jorSplitting A h hω) b := by
  have hd := (isUnit_diagPart_iff A).mp h
  funext x
  refine (Splitting.mulVecStep_eq_of_mulVec_sub_eq _ b x ?_).symm
  funext i
  have hm : (jorSplitting A h hω).m = ω⁻¹ • diagPart A := rfl
  have hi := hd i
  rw [hm, smul_mulVec, Pi.smul_apply, diagPart_mulVec_apply, Pi.sub_apply, Pi.sub_apply,
    mulVec_apply_eq_add_sum_erase, jorSweep, smul_eq_mul]
  field_simp
  ring

omit [LinearOrder n] in
/-- Let $A$ be a square matrix with invertible diagonal part $D$. The Jacobi sweep, which is the JOR
sweep with $\omega = 1$, is the step of the Jacobi splitting $P = D$ ([quarteroni2000numerical],
(4.10) and (4.11)). -/
theorem jorSweep_one_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (b : n → 𝕜) :
    jorSweep A 1 b = Splitting.mulVecStep (jacobiSplitting A h) b := by
  rw [jorSweep_eq_mulVecStep A h one_ne_zero, jorSplitting_one]

/-! ### The SOR and Gauss–Seidel sweeps -/

/-- The **SOR sweep** with parameter $\omega$ for a square matrix $A = D + L + U$ and a right-hand
side $b$:
$$x \mapsto (D + \omega L)^{-1} \bigl(((1 - \omega) D - \omega U) x + \omega b\bigr),$$
where $D$, $L$ and $U$ are the diagonal, the strictly lower triangular and the strictly upper
triangular parts of $A$.

This is (4.16) of [quarteroni2000numerical] multiplied through by $D$. At $\omega = 1$ it is the
Gauss–Seidel sweep (4.13). The inverse is the matrix inverse. -/
noncomputable def sorSweep (A : Matrix n n 𝕜) (ω : 𝕜) (b x : n → 𝕜) : n → 𝕜 :=
  (diagPart A + ω • strictLower A)⁻¹ *ᵥ (((1 - ω) • diagPart A - ω • strictUpper A) *ᵥ x + ω • b)

/-- The **backward SOR sweep** with parameter $\omega$ for a square matrix $A = D + L + U$ and a
right-hand side $b$:
$$x \mapsto (D + \omega U)^{-1} \bigl(((1 - \omega) D - \omega L) x + \omega b\bigr).$$

This is the method $(D - \omega F) x_{k+1} = [\omega E + (1 - \omega) D] x_k + \omega b$ of
[quarteroni2000numerical], §4.2.6, with $E = -L$ and $F = -U$. At $\omega = 1$ it is the
backward Gauss–Seidel sweep. -/
noncomputable def backwardSorSweep (A : Matrix n n 𝕜) (ω : 𝕜) (b x : n → 𝕜) : n → 𝕜 :=
  (diagPart A + ω • strictUpper A)⁻¹ *ᵥ (((1 - ω) • diagPart A - ω • strictLower A) *ᵥ x + ω • b)

/-- Let $A$ be a square matrix with invertible diagonal part $D$. For every $\omega$, the SOR sweep
$y$ from $x$ solves the triangular system
$$(D + \omega L) y = ((1 - \omega) D - \omega U) x + \omega b.$$
-/
theorem diagPart_add_smul_strictLower_mulVec_sorSweep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (ω : 𝕜) (b x : n → 𝕜) :
    (diagPart A + ω • strictLower A) *ᵥ sorSweep A ω b x =
      ((1 - ω) • diagPart A - ω • strictUpper A) *ᵥ x + ω • b :=
  mulVec_nonsing_inv_mulVec (isUnit_diagPart_add_smul_strictLower h ω) _

/-- Let $A$ be a square matrix with invertible diagonal part $D$. For every $\omega$, the backward
SOR sweep $y$ from $x$ solves the triangular system
$$(D + \omega U) y = ((1 - \omega) D - \omega L) x + \omega b.$$
-/
theorem diagPart_add_smul_strictUpper_mulVec_backwardSorSweep (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) (ω : 𝕜) (b x : n → 𝕜) :
    (diagPart A + ω • strictUpper A) *ᵥ backwardSorSweep A ω b x =
      ((1 - ω) • diagPart A - ω • strictLower A) *ᵥ x + ω • b :=
  mulVec_nonsing_inv_mulVec (isUnit_diagPart_add_smul_strictUpper h ω) _

/-- **The componentwise SOR recursion.** Let $A$ be a square matrix with invertible diagonal, let
$\omega$ be a scalar, and let $y$ be the SOR sweep from $x$. Then for every index $i$,
$$y_i = \frac{\omega}{a_{ii}} \Bigl(b_i - \sum_{j < i} a_{ij} y_j - \sum_{j > i} a_{ij}
  x_j\Bigr) + (1 - \omega) x_i.$$
The updated components enter for $j < i$, and the old ones for $j > i$.

This is (4.15) of [quarteroni2000numerical], and at $\omega = 1$ it is the Gauss–Seidel
recursion (4.13). It is row $i$ of $(D + \omega L) y = ((1 - \omega) D - \omega U) x + \omega
b$, read as a recursion along the linear order of the index type. -/
theorem sorSweep_apply (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (ω : 𝕜) (b x : n → 𝕜)
    (i : n) :
    sorSweep A ω b x i =
      ω / A i i * (b i - ∑ j ∈ univ.filter (· < i), A i j * sorSweep A ω b x j
        - ∑ j ∈ univ.filter (i < ·), A i j * x j) + (1 - ω) * x i := by
  have hi : A i i ≠ 0 := (isUnit_diagPart_iff A).mp h i
  have hrow := congrFun (diagPart_add_smul_strictLower_mulVec_sorSweep A h ω b x) i
  rw [add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, Pi.add_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    diagPart_mulVec_apply, diagPart_mulVec_apply, strictLower_mulVec_apply,
    strictUpper_mulVec_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hrow
  field_simp
  linear_combination hrow

/-- **The componentwise backward SOR recursion.** Let $A$ be a square matrix with invertible
diagonal, let $\omega$ be a scalar, and let $y$ be the backward SOR sweep from $x$. Then for
every index $i$,
$$y_i = \frac{\omega}{a_{ii}} \Bigl(b_i - \sum_{j > i} a_{ij} y_j - \sum_{j < i} a_{ij}
  x_j\Bigr) + (1 - \omega) x_i.$$

This is the mirror image of `Matrix.sorSweep_apply`: the updated components enter for $j > i$. -/
theorem backwardSorSweep_apply (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (ω : 𝕜)
    (b x : n → 𝕜) (i : n) :
    backwardSorSweep A ω b x i =
      ω / A i i * (b i - ∑ j ∈ univ.filter (i < ·), A i j * backwardSorSweep A ω b x j
        - ∑ j ∈ univ.filter (· < i), A i j * x j) + (1 - ω) * x i := by
  have hi : A i i ≠ 0 := (isUnit_diagPart_iff A).mp h i
  have hrow := congrFun (diagPart_add_smul_strictUpper_mulVec_backwardSorSweep A h ω b x) i
  rw [add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, Pi.add_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    diagPart_mulVec_apply, diagPart_mulVec_apply, strictLower_mulVec_apply,
    strictUpper_mulVec_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hrow
  field_simp
  linear_combination hrow

/-- The residual form of the SOR sweep. Let $A$ be a square matrix with invertible diagonal part
$D$, and let $y$ be the SOR sweep from $x$ with parameter $\omega$. Then
$$(D + \omega L)(y - x) = \omega (b - A x).$$
-/
theorem diagPart_add_smul_strictLower_mulVec_sorSweep_sub (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) (ω : 𝕜) (b x : n → 𝕜) :
    (diagPart A + ω • strictLower A) *ᵥ (sorSweep A ω b x - x) = ω • (b - A *ᵥ x) := by
  have hA : A *ᵥ x = diagPart A *ᵥ x + strictLower A *ᵥ x + strictUpper A *ᵥ x := by
    conv_lhs => rw [← diagPart_add_strictLower_add_strictUpper A]
    simp only [add_mulVec]
  rw [mulVec_sub, diagPart_add_smul_strictLower_mulVec_sorSweep A h, hA]
  simp only [add_mulVec, sub_mulVec, smul_mulVec, sub_smul, one_smul, smul_sub, smul_add]
  abel

/-- The residual form of the backward SOR sweep. Let $A$ be a square matrix with invertible diagonal
part $D$, and let $y$ be the backward SOR sweep from $x$ with parameter $\omega$. Then
$$(D + \omega U)(y - x) = \omega (b - A x).$$
-/
theorem diagPart_add_smul_strictUpper_mulVec_backwardSorSweep_sub (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) (ω : 𝕜) (b x : n → 𝕜) :
    (diagPart A + ω • strictUpper A) *ᵥ (backwardSorSweep A ω b x - x) = ω • (b - A *ᵥ x) := by
  have hA : A *ᵥ x = diagPart A *ᵥ x + strictLower A *ᵥ x + strictUpper A *ᵥ x := by
    conv_lhs => rw [← diagPart_add_strictLower_add_strictUpper A]
    simp only [add_mulVec]
  rw [mulVec_sub, diagPart_add_smul_strictUpper_mulVec_backwardSorSweep A h, hA]
  simp only [add_mulVec, sub_mulVec, smul_mulVec, sub_smul, one_smul, smul_sub, smul_add]
  abel

/-- **The SOR sweep is the step of the SOR splitting.** Let $A$ be a square matrix with invertible
diagonal part $D$, and let $\omega \neq 0$. Then the SOR sweep with parameter $\omega$ is the
step of the SOR splitting $P = \omega^{-1} D + L$ (`Matrix.sorSplitting`). So the sweep is $x
\mapsto x + (\omega^{-1} D + L)^{-1}(b - A x)$, which is the display after (4.17) of
[quarteroni2000numerical], with $L = -E$.

The proof scales the residual form $(D + \omega L)(y - x) = \omega (b - A x)$ by $\omega^{-1}$. -/
theorem sorSweep_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0)
    (b : n → 𝕜) : sorSweep A ω b = Splitting.mulVecStep (sorSplitting A h hω) b := by
  funext x
  refine (Splitting.mulVecStep_eq_of_mulVec_sub_eq _ b x ?_).symm
  have hm : (sorSplitting A h hω).m = ω⁻¹ • (diagPart A + ω • strictLower A) := by
    change ω⁻¹ • diagPart A + strictLower A = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [hm, smul_mulVec, diagPart_add_smul_strictLower_mulVec_sorSweep_sub A h, smul_smul,
    inv_mul_cancel₀ hω, one_smul]

/-- **The Gauss–Seidel sweep is the step of the Gauss–Seidel splitting.** Let $A$ be a square matrix
with invertible diagonal part $D$. The SOR sweep with $\omega = 1$ is the step of the
Gauss–Seidel splitting $P = D + L$ ([quarteroni2000numerical], (4.13)–(4.14)). -/
theorem sorSweep_one_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (b : n → 𝕜) :
    sorSweep A 1 b = Splitting.mulVecStep (gaussSeidelSplitting A h) b := by
  rw [sorSweep_eq_mulVecStep A h one_ne_zero, sorSplitting_one]

/-- **The backward SOR sweep is the step of the backward SOR splitting.** Let $A$ be a square matrix
with invertible diagonal part $D$, and let $\omega \neq 0$. Then the backward SOR sweep with
parameter $\omega$ is the step of the backward SOR splitting $P = \omega^{-1} D + U$
(`Matrix.backwardSorSplitting`). -/
theorem backwardSorSweep_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) (b : n → 𝕜) :
    backwardSorSweep A ω b = Splitting.mulVecStep (backwardSorSplitting A h hω) b := by
  funext x
  refine (Splitting.mulVecStep_eq_of_mulVec_sub_eq _ b x ?_).symm
  have hm : (backwardSorSplitting A h hω).m = ω⁻¹ • (diagPart A + ω • strictUpper A) := by
    change ω⁻¹ • diagPart A + strictUpper A = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [hm, smul_mulVec, diagPart_add_smul_strictUpper_mulVec_backwardSorSweep_sub A h, smul_smul,
    inv_mul_cancel₀ hω, one_smul]

/-- **The backward Gauss–Seidel sweep is the step of the backward Gauss–Seidel splitting.** Let $A$
be a square matrix with invertible diagonal part $D$. The backward SOR sweep with $\omega = 1$
is the step of the backward Gauss–Seidel splitting $P = D + U$ ([quarteroni2000numerical],
§4.2.6). -/
theorem backwardSorSweep_one_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (b : n → 𝕜) :
    backwardSorSweep A 1 b = Splitting.mulVecStep (backwardGaussSeidelSplitting A h) b := by
  rw [backwardSorSweep_eq_mulVecStep A h one_ne_zero, backwardSorSplitting_one]

/-- **One SSOR step is a forward SOR sweep followed by a backward one.** Let $A$ be a square matrix
with invertible diagonal part $D$, and let $\omega \notin \{0, 2\}$. For every $b$ and $x$, the
backward SOR sweep applied to the SOR sweep from $x$ is the step from $x$ of the SSOR splitting
(`Matrix.ssorSplitting`).

This is the elimination of the half-step $x^{(k+1/2)}$ in §4.2.6 of [quarteroni2000numerical].
At $\omega = 1$ it is the symmetric Gauss–Seidel method with $B_{SGS}$ and $b_{SGS}$ of (4.21)
there; see also [saad2003iterative], (4.13)–(4.14). -/
theorem ssorSweep_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0)
    (hω2 : ω ≠ 2) (b x : n → 𝕜) :
    backwardSorSweep A ω b (sorSweep A ω b x) =
      Splitting.mulVecStep (ssorSplitting A h hω hω2) b x := by
  rw [sorSweep_eq_mulVecStep A h hω, backwardSorSweep_eq_mulVecStep A h hω]
  exact Splitting.mulVecStep_mulVecStep b x _ _ _ (ringInverse_ssorSplitting_m A h hω hω2)

/-!
### The SOR sweep as a loop of relaxations

A program executes a loop over the unknowns, and relaxes each unknown once from the current vector.
Over `Fin m`, in the natural order, this loop is the sweep `Matrix.sorSweep`.
-/

section Relaxation

variable {m : ℕ} {𝕜 : Type*} [Field 𝕜] (A : Matrix (Fin m) (Fin m) 𝕜) (ω : 𝕜) (b : Fin m → 𝕜)

/-- The **relaxation of the $i$-th unknown** in an SOR sweep, for a matrix $A$ indexed by `Fin m`, a
parameter $\omega$ and a right-hand side $b$: the vector $x$ goes to the vector that has the
$i$-th entry
$$x_i + \frac{\omega\, (b - A x)_i}{a_{ii}}$$
and the other entries of $x$.

This is one inner iteration of (4.15) of [quarteroni2000numerical] and of (4.12) of
[saad2003iterative]. -/
def sorRelax (i : Fin m) (x : Fin m → 𝕜) : Fin m → 𝕜 :=
  Function.update x i (x i + ω * (b - A *ᵥ x) i / A i i)

/-- The vector after the first $k$ relaxations of the loop, in the order $0, 1, \dots, k - 1$. -/
private def sorRelaxPartial (k : ℕ) (x : Fin m → 𝕜) : Fin m → 𝕜 :=
  ((List.finRange m).take k).foldl (fun y i => sorRelax A ω b i y) x

variable {A ω b}

private theorem sorRelaxPartial_succ {k : ℕ} (hk : k < m) (x : Fin m → 𝕜) :
    sorRelaxPartial A ω b (k + 1) x = sorRelax A ω b ⟨k, hk⟩ (sorRelaxPartial A ω b k x) := by
  rw [sorRelaxPartial, sorRelaxPartial, List.take_add_one,
    List.getElem?_eq_getElem (by simpa using hk), List.foldl_append]
  simp

/-- The first $k$ relaxations do not change the entries with index at least $k$. -/
private theorem sorRelaxPartial_of_le (x : Fin m → 𝕜) :
    ∀ k : ℕ, k ≤ m → ∀ j : Fin m, k ≤ (j : ℕ) → sorRelaxPartial A ω b k x j = x j := by
  intro k
  induction k with
  | zero => intro _ j _; rfl
  | succ k ih =>
    intro hk j hj
    have hkm : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hk
    have hne : j ≠ ⟨k, hkm⟩ := by
      simp only [ne_eq, Fin.ext_iff]
      omega
    rw [sorRelaxPartial_succ hkm, sorRelax, Function.update_of_ne hne, ih hkm.le j (by omega)]

/-- After the first $k$ relaxations, further relaxations do not change the entries with index less
than $k$. -/
private theorem sorRelaxPartial_stable (x : Fin m → 𝕜) :
    ∀ l : ℕ, l ≤ m → ∀ k : ℕ, k ≤ l → ∀ j : Fin m, (j : ℕ) < k →
      sorRelaxPartial A ω b l x j = sorRelaxPartial A ω b k x j := by
  intro l
  induction l with
  | zero => intro _ k hk j hj; omega
  | succ l ih =>
    intro hl k hk j hj
    rcases eq_or_lt_of_le hk with rfl | hkl
    · rfl
    have hlm : l < m := lt_of_lt_of_le (Nat.lt_succ_self l) hl
    have hne : j ≠ ⟨l, hlm⟩ := by
      simp only [ne_eq, Fin.ext_iff]
      omega
    rw [sorRelaxPartial_succ hlm, sorRelax, Function.update_of_ne hne,
      ih hlm.le k (by omega) j hj]

/-- **The SOR sweep is its loop of relaxations.** Let $A$ be a square matrix indexed by `Fin m` with
invertible diagonal, and let $\omega$ be any scalar. Relaxing the unknowns one at a time in the
order $0, 1, \dots, m - 1$, each from the current vector, gives the SOR sweep from $x$, that is,
the solution $y$ of
$$(D + \omega L) y = ((1 - \omega) D - \omega U) x + \omega b.$$

This is (4.15)–(4.16) of [quarteroni2000numerical]. No condition on $\omega$ is needed, only
nonzero diagonal entries. -/
theorem foldl_sorRelax_eq_sorSweep (h : IsUnit (diagPart A)) (x : Fin m → 𝕜) :
    (List.finRange m).foldl (fun y i => sorRelax A ω b i y) x = sorSweep A ω b x := by
  set y := (List.finRange m).foldl (fun y i => sorRelax A ω b i y) x with hy
  have hdiag : ∀ i : Fin m, A i i ≠ 0 := (isUnit_diagPart_iff A).1 h
  have hcard : sorRelaxPartial A ω b m x = y := by
    rw [hy, sorRelaxPartial, List.take_of_length_le (by simp)]
  have hres : (diagPart A + ω • strictLower A) *ᵥ (y - x) = ω • (b - A *ᵥ x) := by
    funext i
    -- the vector before relaxation `i` agrees with `y` below `i` and with `x` from `i` on
    set z := sorRelaxPartial A ω b (i : ℕ) x with hz
    have hzlt : ∀ j : Fin m, j < i → z j = y j := fun j hj => by
      rw [← hcard]
      exact (sorRelaxPartial_stable x m le_rfl (i : ℕ) i.2.le j hj).symm
    have hzge : ∀ j : Fin m, ¬ j < i → z j = x j := fun j hj =>
      sorRelaxPartial_of_le x (i : ℕ) i.2.le j (by omega)
    have hyi : y i = x i + ω * (b - A *ᵥ z) i / A i i := by
      have h1 : y i = sorRelaxPartial A ω b ((i : ℕ) + 1) x i := by
        rw [← hcard]
        exact sorRelaxPartial_stable x m le_rfl ((i : ℕ) + 1) i.2 i (Nat.lt_succ_self _)
      rw [h1, sorRelaxPartial_succ i.2, sorRelax, Function.update_self,
        sorRelaxPartial_of_le x (i : ℕ) i.2.le i le_rfl]
    have hkey : A i i * (y i - x i) = ω * (b i - (A *ᵥ z) i) := by
      rw [hyi, add_sub_cancel_left, Pi.sub_apply, mul_div_cancel₀ _ (hdiag i)]
    have hsplit : ∀ w : Fin m → 𝕜, (A *ᵥ w) i
        = ∑ j ∈ univ.filter (· < i), A i j * w j
          + ∑ j ∈ univ.filter (fun j => ¬ j < i), A i j * w j := fun w => by
      change ∑ j, A i j * w j = _
      exact (sum_filter_add_sum_filter_not _ _ _).symm
    have hlow : ∑ j ∈ univ.filter (· < i), A i j * (y j - x j)
        = (A *ᵥ z) i - (A *ᵥ x) i := by
      have h1 : ∑ j ∈ univ.filter (· < i), A i j * z j
          = ∑ j ∈ univ.filter (· < i), A i j * y j :=
        sum_congr rfl fun j hj => by rw [hzlt j (mem_filter.1 hj).2]
      have h2 : ∑ j ∈ univ.filter (fun j => ¬ j < i), A i j * z j
          = ∑ j ∈ univ.filter (fun j => ¬ j < i), A i j * x j :=
        sum_congr rfl fun j hj => by rw [hzge j (mem_filter.1 hj).2]
      rw [hsplit, hsplit, h1, h2]
      simp only [mul_sub, sum_sub_distrib]
      ring
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, add_mulVec, Pi.add_apply,
      diagPart_mulVec_apply, smul_mulVec, strictLower_mulVec_apply]
    rw [hlow, hkey]
    ring
  have hstep : (diagPart A + ω • strictLower A) *ᵥ (y - x)
      = (diagPart A + ω • strictLower A) *ᵥ (sorSweep A ω b x - x) := by
    rw [hres, diagPart_add_smul_strictLower_mulVec_sorSweep_sub A h]
  exact sub_left_inj.mp
    (mulVec_injective_of_isUnit (isUnit_diagPart_add_smul_strictLower h ω) hstep)

end Relaxation

end Matrix
