/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Taylor
import Numlib.FiniteDifference.Derivative
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Finite differences for the two-point boundary value problem

This file studies the centred finite difference discretization of the two-point boundary value
problem $-u'' = f$ on $(a, b)$, $u(a) = u(b) = 0$, and of its variable-coefficient form
$-(\alpha u')' + \gamma u = f$. It follows [quarteroni2000numerical] §12.2, but on a general
interval $[a, b]$ in place of the book's $[0, 1]$. The uniform grid has $n$ interior nodes
$x_j = a + jh$, $j = 0, \dots, n + 1$, with step $h = (b - a)/(n + 1)$. A grid function is a vector
$v = (v_0, \dots, v_{n+1})$, and $V_h^0$ is the space of grid functions with $v_0 = v_{n+1} = 0$.
The discrete operator is $(L_h w)_j = -(w_{j+1} - 2 w_j + w_{j-1})/h^2$ at the interior nodes
$j = 1, \dots, n$. On $V_h^0$ it is the matrix $h^{-2} \operatorname{tridiag}(-1, 2, -1)$ applied to
the interior values.

The trapezoidal inner product $(w, v)_h = h \sum_k c_k w_k v_k$ with $c_0 = c_{n+1} = 1/2$ and
$c_k = 1$ otherwise defines the discrete norm $\|v\|_h = (v, v)_h^{1/2}$, and the discrete $H^1$
seminorm is $|\!|\!|v|\!|\!|_h = (h \sum_{j=0}^{n} ((v_{j+1} - v_j)/h)^2)^{1/2}$. The file proves
summation by parts, the energy identity $(L_h v, v)_h = |\!|\!|v|\!|\!|_h^2$ on $V_h^0$, the
discrete Poincaré inequality, the bound on the truncation error by Taylor expansion, stability in
the discrete norm and in the maximum norm, and the convergence theorem $\|u - u_h\|_\infty \le ((b -
a)^2/96)\, h^2 \|f''\|_\infty$. For variable coefficients it shows that the matrix of the scheme is
symmetric positive definite, an M-matrix, and strictly diagonally dominant, and it defines the
discrete Neumann and Robin boundary rows.

## Main definitions

* `FiniteDifference.uniformGrid`: the nodes $x_j = a + jh$ of the uniform grid.
* `FiniteDifference.gridZero`: the space $V_h^0$ of grid functions that vanish at both endpoints.
* `FiniteDifference.discreteLaplacian`: the discrete operator $L_h$.
* `FiniteDifference.discreteInner`, `FiniteDifference.discreteL2Norm`,
  `FiniteDifference.discreteH1Seminorm`: the trapezoidal inner product $(w, v)_h$, the norm
  $\|v\|_h$ and the seminorm $|\!|\!|v|\!|\!|_h$.
* `FiniteDifference.truncationError`: the local truncation error $\tau_j = (L_h u)(x_j) - f(x_j)$.
* `FiniteDifference.variableCoeffOperator`: the flux-form operator for $-(\alpha u')' + \gamma u$.
* `FiniteDifference.IsNeumannSolution`, `FiniteDifference.IsRobinSolution`: the discrete problems
  with a Neumann condition at $b$ and with Robin conditions at both ends.

## Main results

* `FiniteDifference.discreteLaplacian_eq_mulVec`: on $V_h^0$, $L_h w = h^{-2}
  \operatorname{tridiag}(-1, 2, -1)$ applied to the interior values of $w$.
* `FiniteDifference.sum_sub_mul_eq_sub_sum`: summation by parts.
* `FiniteDifference.discreteInner_discreteLaplacian_eq`: the energy identity $h \sum_j (L_h w)_j
  v_j = h^{-1} \sum_j (w_{j+1} - w_j)(v_{j+1} - v_j)$ for $v \in V_h^0$.
* `FiniteDifference.discreteL2Norm_le_discreteH1Seminorm`: the discrete Poincaré inequality $\|v\|_h
  \le ((n + 1) h/\sqrt 2)\, |\!|\!|v|\!|\!|_h$ on $V_h^0$.
* `FiniteDifference.discreteL2Norm_le_of_discreteLaplacian_eq`: stability by the energy method.
* `FiniteDifference.abs_truncationError_le_of_lipschitzOnWith`,
  `FiniteDifference.abs_truncationError_le_of_contDiffOn`: the truncation error is $O(h^2)$.
* `FiniteDifference.discreteLaplacian_parabola`: the discrete parabola $w_j = (x_j - a)(b - x_j)/2$
  satisfies $L_h w = 1$.
* `FiniteDifference.norm_le_of_discreteLaplacian_eq`: stability in the maximum norm, $\|u\|_\infty
  \le ((b - a)^2/8) \|L_h u\|_\infty$ on $V_h^0$.
* `FiniteDifference.norm_sub_le_of_discreteLaplacian_eq`: the convergence theorem.
* `FiniteDifference.variableCoeffMatrix_posDef`: the matrix of the variable-coefficient scheme is
  positive definite for $\alpha > 0$ and $\gamma \ge 0$.

## Proof outline

There are two stability estimates. The energy method combines the energy identity
$(L_h v, v)_h = |\!|\!|v|\!|\!|_h^2$ with the discrete Poincaré inequality and gives
$\|u_h\|_h \le (((n + 1) h)^2/2) \|f_h\|_h$; this is the estimate that extends to variable
coefficients. The maximum-norm estimate $\|u_h\|_\infty \le ((b - a)^2/8) \|L_h u_h\|_\infty$ does
not use the explicit discrete Green's function of the book. The matrix
$\operatorname{tridiag}(-1, 2, -1)$ is an M-matrix, and the discrete parabola satisfies $L_h w = 1$
exactly, so the comparison principle `Matrix.IsMMatrix.norm_inv_mulVec_le` gives the bound with the
same constant. Together with the truncation error bound $\|\tau_h\|_\infty \le (h^2/12)
\|u''''\|_\infty$ this gives the convergence theorem. For variable coefficients, one energy identity
(`FiniteDifference.sum_variableCoeffOperator_mul_interior`) gives positive definiteness, the
M-matrix property and diagonal dominance; the identity for $L_h$ is its case $\alpha = 1$,
$\gamma = 0$.

## Implementation notes

* The natural number `n` is the number of interior nodes. The nodes are indexed by `Fin (n + 2)` and
  the panels $[x_j, x_{j+1}]$ by `Fin (n + 1)`. The book divides $[0, 1]$ into $n$ subintervals with
  $n - 1$ interior nodes; that is the case $n - 1$ here.
* The maximum norm $\|v\|_\infty$ of a grid function is the norm of the `Pi` type
  `Fin (n + 2) → ℝ`. An interior grid function is `Fin n → ℝ`; the index `i : Fin n` stands for the
  node $i + 1$.
  `FiniteDifference.interior` and `FiniteDifference.ofInterior` pass between grid functions and
  their interior values.
* The operator $L_h$ maps grid functions to interior grid functions. Every spectral and
  inverse-positivity fact about it comes from its matrix form
  `FiniteDifference.discreteLaplacian_eq_mulVec` and the facts about
  `Matrix.symmTridiagonalToeplitz` in `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`.
* The operator, the inner product and the norms take the step $h$ as a free argument. Lean's
  convention $x / 0 = 0$ makes $L_h$ and the difference quotients zero at $h = 0$; the theorems
  assume $h \neq 0$ or $h > 0$ where they need it.
* The Neumann and Robin boundary rows are definitions only; the book proves nothing about them.
* Some statements differ from the printed text of [quarteroni2000numerical]. The truncation error
  formula (12.19) and the off-diagonal entries of the matrix (12.34) are stated with corrected
  signs, the missing prime on $u'$ in Exercise 12.10 is restored, and the consistency bound under a
  Lipschitz third derivative is $M h^2/12$ in place of the book's weaker $M h^2$.
-/

open Set Finset Matrix

namespace FiniteDifference

variable {n : ℕ} {a b : ℝ}

/-! ### The uniform grid -/

/-- The grid step $h = (b - a)/(n + 1)$ of the uniform grid on $[a, b]$ with $n$ interior nodes. -/
noncomputable def gridStep (a b : ℝ) (n : ℕ) : ℝ := (b - a) / (n + 1)

/-- The **uniform grid** on $[a, b]$ with $n$ interior nodes: the nodes $x_j = a + jh$,
$j = 0, \dots, n + 1$, with $h = (b - a)/(n + 1)$.

The node index is `j : Fin (n + 2)`, and $h$ is `FiniteDifference.gridStep a b n`. -/
noncomputable def uniformGrid (a b : ℝ) (n : ℕ) (j : Fin (n + 2)) : ℝ := a + j * gridStep a b n

/-- If $a < b$, the grid step is positive. -/
theorem gridStep_pos (hab : a < b) : 0 < gridStep a b n := by
  unfold gridStep; positivity

/-- If $a \le b$, the grid step is nonnegative. -/
theorem gridStep_nonneg (hab : a ≤ b) : 0 ≤ gridStep a b n := by
  unfold gridStep; positivity

/-- The $n + 1$ panels fill the interval: $(n + 1) h = b - a$. -/
theorem gridStep_mul_succ : ((n : ℝ) + 1) * gridStep a b n = b - a := by
  unfold gridStep; field_simp

/-- The node $x_j$ is $a + jh$. -/
theorem uniformGrid_apply (j : Fin (n + 2)) : uniformGrid a b n j = a + j * gridStep a b n := rfl

/-- The first node is $x_0 = a$. -/
@[simp]
theorem uniformGrid_zero : uniformGrid a b n 0 = a := by simp [uniformGrid]

/-- The last node is $x_{n+1} = b$. -/
@[simp]
theorem uniformGrid_last : uniformGrid a b n (Fin.last (n + 1)) = b := by
  simp only [uniformGrid, Fin.val_last]
  push_cast
  rw [gridStep_mul_succ]
  ring

/-- Consecutive nodes are $h$ apart: $x_{j+1} - x_j = h$ for $j = 0, \dots, n$. -/
theorem uniformGrid_succ_sub (j : Fin (n + 1)) :
    uniformGrid a b n j.succ - uniformGrid a b n j.castSucc = gridStep a b n := by
  simp only [uniformGrid, Fin.val_succ, Fin.val_castSucc]
  push_cast
  ring

/-- The next node is $x_{j+1} = x_j + h$ for $j = 0, \dots, n$. -/
theorem uniformGrid_succ (j : Fin (n + 1)) :
    uniformGrid a b n j.succ = uniformGrid a b n j.castSucc + gridStep a b n := by
  rw [← uniformGrid_succ_sub j]; ring

/-- If $a < b$, the nodes are strictly increasing in $j$. -/
theorem uniformGrid_strictMono (hab : a < b) : StrictMono (uniformGrid a b n) := by
  intro i j hij
  simp only [uniformGrid]
  have := gridStep_pos (n := n) hab
  have : (i : ℝ) < j := by exact_mod_cast hij
  nlinarith

/-- If $a \le b$, every node lies in $[a, b]$. -/
theorem uniformGrid_mem_Icc (hab : a ≤ b) (j : Fin (n + 2)) : uniformGrid a b n j ∈ Icc a b := by
  have h0 := gridStep_nonneg (n := n) hab
  have hj : (j : ℝ) ≤ n + 1 := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  constructor
  · simp only [uniformGrid]; exact le_add_of_nonneg_right (by positivity)
  · simp only [uniformGrid]
    nlinarith [gridStep_mul_succ (a := a) (b := b) (n := n)]

/-- If $a < b$, the interior nodes $x_1, \dots, x_n$ lie in the open interval $(a, b)$. -/
theorem uniformGrid_interior_mem_Ioo (hab : a < b) (i : Fin n) :
    uniformGrid a b n i.succ.castSucc ∈ Ioo a b := by
  have hmono := uniformGrid_strictMono (n := n) hab
  constructor
  · simpa using hmono (show (0 : Fin (n + 2)) < i.succ.castSucc from by
      rw [Fin.lt_def]; simp)
  · simpa using hmono (show i.succ.castSucc < Fin.last (n + 1) from by
      rw [Fin.lt_def]; simp)

/-! ### Grid functions -/

/-- The space $V_h^0$ of **grid functions vanishing at both endpoints**: the grid functions
$v = (v_0, \dots, v_{n+1})$ with $v_0 = v_{n+1} = 0$, as a subspace of $\mathbb{R}^{n+2}$. -/
def gridZero (n : ℕ) : Submodule ℝ (Fin (n + 2) → ℝ) where
  carrier := {v | v 0 = 0 ∧ v (Fin.last (n + 1)) = 0}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨hv0, hv1⟩ ⟨hw0, hw1⟩; simp [hv0, hv1, hw0, hw1]
  smul_mem' := by rintro c v ⟨hv0, hv1⟩; simp [hv0, hv1]

/-- A grid function lies in $V_h^0$ if and only if $v_0 = 0$ and $v_{n+1} = 0$. -/
theorem mem_gridZero_iff {v : Fin (n + 2) → ℝ} :
    v ∈ gridZero n ↔ v 0 = 0 ∧ v (Fin.last (n + 1)) = 0 := Iff.rfl

/-- The linear map that takes a grid function $v$ to its interior values $(v_1, \dots, v_n)$. -/
def interior (n : ℕ) : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v i := v i.succ.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The $i$-th entry of the interior values of $v$ is $v_{i+1}$, for `i : Fin n`. -/
@[simp]
theorem interior_apply (v : Fin (n + 2) → ℝ) (i : Fin n) : interior n v i = v i.succ.castSucc := rfl

/-- Every node index $j \in \{0, \dots, n + 1\}$ is $0$, or $n + 1$, or an interior index $i + 1$
with $i < n$. This is the case analysis behind the statements about grid functions in $V_h^0$. -/
theorem node_eq_zero_or_eq_last_or (j : Fin (n + 2)) :
    j = 0 ∨ j = Fin.last (n + 1) ∨ ∃ i : Fin n, j = i.succ.castSucc := by
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
  · exact Or.inl (Fin.ext (by simpa using hj))
  by_cases hj2 : (j : ℕ) < n + 1
  · refine Or.inr (Or.inr ⟨⟨(j : ℕ) - 1, by omega⟩, Fin.ext ?_⟩)
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  · refine Or.inr (Or.inl (Fin.ext ?_))
    simp only [Fin.val_last]
    omega

/-- The linear map that extends interior values $(u_1, \dots, u_n)$ by zero at both endpoints to a
grid function. -/
def ofInterior (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun u j := if h : (j : ℕ) ≠ 0 ∧ (j : ℕ) < n + 1 then u ⟨(j : ℕ) - 1, by omega⟩ else 0
  map_add' u v := by
    ext j
    by_cases h : (j : ℕ) ≠ 0 ∧ (j : ℕ) < n + 1
    · simp only [Pi.add_apply, dite_eq_left h]
    · simp only [Pi.add_apply, dite_eq_right h, add_zero]
  map_smul' c u := by
    ext j
    by_cases h : (j : ℕ) ≠ 0 ∧ (j : ℕ) < n + 1
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dite_eq_left h]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dite_eq_right h, mul_zero]

/-- The extension by zero has the value $u_j$ at an interior node $j$ and $0$ at the nodes $0$ and
$n + 1$. -/
theorem ofInterior_apply (u : Fin n → ℝ) (j : Fin (n + 2)) :
    ofInterior n u j
      = if h : (j : ℕ) ≠ 0 ∧ (j : ℕ) < n + 1 then u ⟨(j : ℕ) - 1, by omega⟩ else 0 := rfl

/-- The extension by zero vanishes at the first node. -/
@[simp]
theorem ofInterior_zero (u : Fin n → ℝ) : ofInterior n u 0 = 0 := by
  rw [ofInterior_apply, dite_eq_right (by simp)]

/-- The extension by zero vanishes at the last node. -/
@[simp]
theorem ofInterior_last (u : Fin n → ℝ) : ofInterior n u (Fin.last (n + 1)) = 0 := by
  rw [ofInterior_apply, dite_eq_right (by simp)]

/-- The extension by zero has the value $u_{i+1}$ at the interior node `i.succ.castSucc`. -/
@[simp]
theorem ofInterior_succ_castSucc (u : Fin n → ℝ) (i : Fin n) :
    ofInterior n u i.succ.castSucc = u i := by
  rw [ofInterior_apply, dite_eq_left (by
    have := i.isLt
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega)]
  exact congrArg u (Fin.ext (by simp))

/-- The extension by zero has the value $u_{i+1}$ at the interior node `i.castSucc.succ`.

This is `FiniteDifference.ofInterior_succ_castSucc` in the form that `simp` produces, because
`Fin.castSucc_succ` is a `simp` lemma. -/
@[simp]
theorem ofInterior_castSucc_succ (u : Fin n → ℝ) (i : Fin n) :
    ofInterior n u i.castSucc.succ = u i := ofInterior_succ_castSucc u i

/-- The interior values of the extension by zero of $u$ are $u$. -/
theorem interior_ofInterior (u : Fin n → ℝ) : interior n (ofInterior n u) = u := by
  ext i; simp

/-- The extension by zero of interior values lies in $V_h^0$. -/
theorem ofInterior_mem_gridZero (u : Fin n → ℝ) : ofInterior n u ∈ gridZero n :=
  ⟨by simp, by simp⟩

/-- A grid function in $V_h^0$ is the extension by zero of its interior values. -/
theorem ofInterior_interior_of_mem {v : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n) :
    ofInterior n (interior n v) = v := by
  ext j
  rcases node_eq_zero_or_eq_last_or j with rfl | rfl | ⟨i, rfl⟩
  · simpa using hv.1.symm
  · simpa using hv.2.symm
  · simp

/-- Two grid functions in $V_h^0$ with the same interior values are equal. -/
theorem interior_injective_on_gridZero {v w : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n)
    (hw : w ∈ gridZero n) (h : interior n v = interior n w) : v = w := by
  rw [← ofInterior_interior_of_mem hv, ← ofInterior_interior_of_mem hw, h]

/-- For a grid function $v \in V_h^0$, the maximum norm of $v$ is at most the maximum norm of its
interior values. -/
theorem norm_le_norm_interior_of_mem {v : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n) :
    ‖v‖ ≤ ‖interior n v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  rcases node_eq_zero_or_eq_last_or j with rfl | rfl | ⟨i, rfl⟩
  · rw [hv.1, norm_zero]; exact norm_nonneg _
  · rw [hv.2, norm_zero]; exact norm_nonneg _
  · exact norm_le_pi_norm (interior n v) i

/-- A grid function in $V_h^0$ whose interior values vanish is zero. -/
theorem eq_zero_of_interior_eq_zero {v : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n)
    (h : interior n v = 0) : v = 0 :=
  interior_injective_on_gridZero hv (Submodule.zero_mem _) (by rw [h, map_zero])

/-- A grid function $v$ with $v_0 = 0$ and $v_{j+1} = v_j$ for $j = 0, \dots, n$ is zero. -/
theorem eq_zero_of_forall_succ_eq {v : Fin (n + 2) → ℝ} (h0 : v 0 = 0)
    (h : ∀ j : Fin (n + 1), v j.succ = v j.castSucc) : v = 0 := by
  ext j
  induction j using Fin.induction with
  | zero => exact h0
  | succ j ih => rw [h j, ih]; rfl

/-! ### The discrete Laplacian -/

/-- The **discrete operator** $L_h$ of [quarteroni2000numerical] (12.9). For a step $h$ and a grid
function $w = (w_0, \dots, w_{n+1})$, it is the interior grid function
$$(L_h w)_j = -\frac{w_{j+1} - 2 w_j + w_{j-1}}{h^2}, \qquad j = 1, \dots, n.$$

The map is linear from `Fin (n + 2) → ℝ` to `Fin n → ℝ`; the index `i : Fin n` stands for the
node $i + 1$. The step $h$ is a free argument, and $L_h = 0$ at $h = 0$. -/
noncomputable def discreteLaplacian (n : ℕ) (h : ℝ) : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun w i := -(w i.succ.succ - 2 * w i.succ.castSucc + w i.castSucc.castSucc) / h ^ 2
  map_add' _ _ := by ext; simp only [Pi.add_apply]; ring
  map_smul' _ _ := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The value of $L_h w$ at the interior node $i + 1$ is $-(w_{i+2} - 2 w_{i+1} + w_i)/h^2$. -/
theorem discreteLaplacian_apply (h : ℝ) (w : Fin (n + 2) → ℝ) (i : Fin n) :
    discreteLaplacian n h w i
      = -(w i.succ.succ - 2 * w i.succ.castSucc + w i.castSucc.castSucc) / h ^ 2 := rfl

/-- Let $u : \mathbb{R} \to \mathbb{R}$ and let $h$ be the grid step. At each interior node $x_j$,
the discrete operator applied to the grid values $u(x_k)$ is minus the second centred difference
of $u$:
$$(L_h u)_j = -\frac{u(x_j + h) - 2 u(x_j) + u(x_j - h)}{h^2}.$$
-/
theorem discreteLaplacian_comp_uniformGrid (u : ℝ → ℝ) (i : Fin n) :
    discreteLaplacian n (gridStep a b n) (u ∘ uniformGrid a b n) i
      = -secondCentredDiff u (gridStep a b n) (uniformGrid a b n i.succ.castSucc) := by
  have h1 := uniformGrid_succ (a := a) (b := b) i.succ
  have h2 := uniformGrid_succ (a := a) (b := b) i.castSucc
  rw [Fin.succ_castSucc] at h2
  rw [discreteLaplacian_apply, secondCentredDiff_apply, Function.comp_apply, Function.comp_apply,
    Function.comp_apply, h1, show uniformGrid a b n i.castSucc.castSucc
      = uniformGrid a b n i.succ.castSucc - gridStep a b n by linarith]
  ring

/-! ### The neighbour sums of a tridiagonal row -/

/-- If $w_{n+1} = 0$, then the sum over $j < n$ of $c$ times the interior value $w_{j+1}$,
restricted to $j = i + 1$, is $c\, w_{i+2}$. -/
private theorem sum_ite_succ_eq {w : Fin (n + 2) → ℝ} (hw : w (Fin.last (n + 1)) = 0) (i : Fin n)
    (c : ℝ) : ∑ j : Fin n, (if (i : ℕ) + 1 = j then c * interior n w j else 0)
      = c * w i.succ.succ := by
  by_cases hi : (i : ℕ) + 1 < n
  · have hfin : (⟨(i : ℕ) + 1, hi⟩ : Fin n).succ.castSucc = i.succ.succ := Fin.ext (by simp)
    rw [Finset.sum_eq_single ⟨(i : ℕ) + 1, hi⟩]
    · rw [ite_eq_left rfl, interior_apply, hfin]
    · intro j _ hj
      rw [ite_eq_right]
      intro h
      exact hj (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hlast : i.succ.succ = Fin.last (n + 1) := by ext; simp; omega
    rw [hlast, hw, mul_zero]
    exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; intro h; omega

/-- If $w_0 = 0$, then the sum over $j < n$ of $c$ times the interior value $w_{j+1}$, restricted to
$j + 1 = i$, is $c\, w_i$. -/
private theorem sum_ite_pred_eq {w : Fin (n + 2) → ℝ} (hw : w 0 = 0) (i : Fin n) (c : ℝ) :
    ∑ j : Fin n, (if (j : ℕ) + 1 = i then c * interior n w j else 0)
      = c * w i.castSucc.castSucc := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    simp only [Fin.castSucc_mk, Fin.zero_eta]
    rw [Fin.castSucc_zero, hw, mul_zero]
    exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; omega
  | succ i =>
    have hfin : (⟨i, by omega⟩ : Fin n).succ.castSucc
        = (⟨i + 1, hi⟩ : Fin n).castSucc.castSucc := Fin.ext (by simp)
    rw [Finset.sum_eq_single ⟨i, by omega⟩]
    · rw [ite_eq_left rfl, interior_apply, hfin]
    · intro j _ hj
      rw [ite_eq_right]
      intro h
      exact hj (Fin.ext (by simpa using h))
    · intro h; exact absurd (Finset.mem_univ _) h

/-- For $w \in V_h^0$ and an interior node $j$, the $j$-th entry of
$\operatorname{tridiag}(-1, 2, -1)$ applied to the interior values of $w$ is
$2 w_j - w_{j+1} - w_{j-1}$. -/
theorem symmTridiagonalToeplitz_mulVec_interior {w : Fin (n + 2) → ℝ} (hw : w ∈ gridZero n)
    (i : Fin n) : (symmTridiagonalToeplitz n (-1) 2 *ᵥ interior n w) i
      = 2 * w i.succ.castSucc - w i.succ.succ - w i.castSucc.castSucc := by
  have hsplit : ∀ j : Fin n, symmTridiagonalToeplitz n (-1) 2 i j * interior n w j
      = (if j = i then 2 * interior n w j else 0)
        - (if (i : ℕ) + 1 = j then 1 * interior n w j else 0)
        - (if (j : ℕ) + 1 = i then 1 * interior n w j else 0) := by
    intro j
    rw [symmTridiagonalToeplitz_apply']
    by_cases h1 : (i : ℕ) = j
    · have : j = i := Fin.ext h1.symm
      subst this
      simp
    · have hne : j ≠ i := fun h => h1 (by rw [h])
      rw [ite_eq_right h1, ite_eq_right hne]
      split_ifs <;> first | (exfalso; omega) | ring
  rw [mulVec, dotProduct]
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i,
    sum_ite_succ_eq hw.2, sum_ite_pred_eq hw.1]
  simp only [Finset.mem_univ, ite_true, interior_apply, one_mul]

/-- For every $h$ and every $w \in V_h^0$, the discrete operator is the **finite difference matrix**
of [quarteroni2000numerical] (12.8) applied to the interior values:
$$L_h w = h^{-2} \operatorname{tridiag}(-1, 2, -1) \begin{bmatrix} w_1 \\ \vdots \\ w_n
  \end{bmatrix}.$$

The matrix is `Matrix.symmTridiagonalToeplitz n (-1) 2`. Its symmetry, positive definiteness and
M-matrix property are `Matrix.symmTridiagonalToeplitz_isSymm`,
`Matrix.posDef_symmTridiagonalToeplitz_neg_one_two` and
`Matrix.isMMatrix_symmTridiagonalToeplitz_neg_one_two`. -/
theorem discreteLaplacian_eq_mulVec (h : ℝ) {w : Fin (n + 2) → ℝ} (hw : w ∈ gridZero n) :
    discreteLaplacian n h w = (h ^ 2)⁻¹ • (symmTridiagonalToeplitz n (-1) 2 *ᵥ interior n w) := by
  ext i
  rw [Pi.smul_apply, smul_eq_mul, symmTridiagonalToeplitz_mulVec_interior hw,
    discreteLaplacian_apply]
  ring

/-- For $h \neq 0$, the discrete operator is injective on $V_h^0$: if $w \in V_h^0$ and $L_h w = 0$,
then $w = 0$. Hence the finite difference problem has at most one solution. -/
theorem discreteLaplacian_injective_on_gridZero {h : ℝ} (hh : h ≠ 0) {w : Fin (n + 2) → ℝ}
    (hw : w ∈ gridZero n) (hL : discreteLaplacian n h w = 0) : w = 0 := by
  rw [discreteLaplacian_eq_mulVec h hw, smul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff two_ne_zero] at hL
  refine eq_zero_of_interior_eq_zero hw (eq_zero_of_mulVec_eq_zero ?_ (hL.resolve_left hh))
  exact (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1
    (isMMatrix_symmTridiagonalToeplitz_neg_one_two n).isUnit))

/-! ### The discrete inner product and norms -/

/-- The trapezoidal weights $c_0 = c_{n+1} = 1/2$ and $c_k = 1$ for $k = 1, \dots, n$. -/
noncomputable def gridWeight (n : ℕ) (k : Fin (n + 2)) : ℝ :=
  if k = 0 ∨ k = Fin.last (n + 1) then 1 / 2 else 1

/-- The trapezoidal weights are nonnegative. -/
theorem gridWeight_nonneg (k : Fin (n + 2)) : 0 ≤ gridWeight n k := by
  unfold gridWeight; split_ifs <;> norm_num

/-- The trapezoidal weights are at most $1$. -/
theorem gridWeight_le_one (k : Fin (n + 2)) : gridWeight n k ≤ 1 := by
  unfold gridWeight; split_ifs <;> norm_num

/-- The trapezoidal weight of an interior node is $1$. -/
@[simp]
theorem gridWeight_succ_castSucc (i : Fin n) : gridWeight n i.succ.castSucc = 1 := by
  unfold gridWeight
  rw [ite_eq_right]
  rintro (h | h)
  · exact absurd (congrArg Fin.val h) (by simp)
  · exact absurd (congrArg Fin.val h) (by simp; omega)

/-- The **trapezoidal discrete inner product** of [quarteroni2000numerical] §12.2.1. For a step $h$
and grid functions $w$, $v$,
$$(w, v)_h = h \sum_{k=0}^{n+1} c_k w_k v_k,$$
with the weights $c_0 = c_{n+1} = 1/2$ and $c_k = 1$ otherwise. This is the composite
trapezoidal rule applied to the product $wv$.

The weights are `FiniteDifference.gridWeight`. -/
noncomputable def discreteInner (n : ℕ) (h : ℝ) (w v : Fin (n + 2) → ℝ) : ℝ :=
  h * ∑ k, gridWeight n k * w k * v k

/-- The **discrete norm** $\|v\|_h = (v, v)_h^{1/2}$ of a grid function $v$, for the trapezoidal
inner product of `FiniteDifference.discreteInner`.

Lean's square root is $0$ at negative arguments, so the value is $0$ when $(v, v)_h < 0$, which
happens only for $h < 0$. -/
noncomputable def discreteL2Norm (n : ℕ) (h : ℝ) (v : Fin (n + 2) → ℝ) : ℝ :=
  √(discreteInner n h v v)

/-- The discrete derivative $(v_{j+1} - v_j)/h$ of a grid function $v$ on the panel
$j = 0, \dots, n$ ([quarteroni2000numerical] Remark 12.1). It is $0$ at $h = 0$. -/
noncomputable def discreteDeriv (n : ℕ) (h : ℝ) (v : Fin (n + 2) → ℝ) (j : Fin (n + 1)) : ℝ :=
  (v j.succ - v j.castSucc) / h

/-- The **discrete $H^1$ seminorm** of [quarteroni2000numerical] (12.12). For a step $h$ and a grid
function $v$,
$$|\!|\!|v|\!|\!|_h = \Big(h \sum_{j=0}^{n} \Big(\frac{v_{j+1} - v_j}{h}\Big)^2\Big)^{1/2}.$$

The difference quotients are `FiniteDifference.discreteDeriv`. Lean's square root is $0$ at
negative arguments, so the value is $0$ for $h < 0$. -/
noncomputable def discreteH1Seminorm (n : ℕ) (h : ℝ) (v : Fin (n + 2) → ℝ) : ℝ :=
  √(h * ∑ j, discreteDeriv n h v j ^ 2)

/-- The discrete inner product is symmetric: $(w, v)_h = (v, w)_h$. -/
theorem discreteInner_comm (h : ℝ) (w v : Fin (n + 2) → ℝ) :
    discreteInner n h w v = discreteInner n h v w := by
  unfold discreteInner
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The discrete inner product is additive in its first argument:
$(w + v, z)_h = (w, z)_h + (v, z)_h$. -/
theorem discreteInner_add_left (h : ℝ) (w v z : Fin (n + 2) → ℝ) :
    discreteInner n h (w + v) z = discreteInner n h w z + discreteInner n h v z := by
  unfold discreteInner
  rw [← mul_add, ← Finset.sum_add_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => by simp only [Pi.add_apply]; ring)

/-- The discrete inner product is homogeneous in its first argument: $(c w, v)_h = c\, (w, v)_h$. -/
theorem discreteInner_smul_left (h c : ℝ) (w v : Fin (n + 2) → ℝ) :
    discreteInner n h (c • w) v = c * discreteInner n h w v := by
  unfold discreteInner
  have hk : ∀ k, gridWeight n k * (c • w) k * v k = c * (gridWeight n k * w k * v k) :=
    fun k => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [hk, ← Finset.mul_sum]
  ring

/-- For $h \ge 0$, $(v, v)_h \ge 0$. -/
theorem discreteInner_self_nonneg {h : ℝ} (hh : 0 ≤ h) (v : Fin (n + 2) → ℝ) :
    0 ≤ discreteInner n h v v := by
  unfold discreteInner
  refine mul_nonneg hh (Finset.sum_nonneg fun k _ => ?_)
  rw [mul_assoc, ← sq]
  exact mul_nonneg (gridWeight_nonneg k) (sq_nonneg _)

/-- For $h > 0$, $(v, v)_h = 0$ if and only if $v = 0$. -/
theorem discreteInner_self_eq_zero_iff {h : ℝ} (hh : 0 < h) (v : Fin (n + 2) → ℝ) :
    discreteInner n h v v = 0 ↔ v = 0 := by
  unfold discreteInner
  rw [mul_eq_zero, or_iff_right hh.ne']
  have hterm : ∀ k, gridWeight n k * v k * v k = gridWeight n k * v k ^ 2 := fun k => by ring
  simp only [hterm]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (gridWeight_nonneg k) (sq_nonneg _)]
  constructor
  · intro H
    ext k
    have hk := H k (Finset.mem_univ k)
    have hpos : 0 < gridWeight n k := by unfold gridWeight; split_ifs <;> norm_num
    exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 hk).resolve_left hpos.ne')
  · rintro rfl k _
    simp

/-- The discrete norm is nonnegative. -/
theorem discreteL2Norm_nonneg (h : ℝ) (v : Fin (n + 2) → ℝ) : 0 ≤ discreteL2Norm n h v :=
  Real.sqrt_nonneg _

/-- For $h \ge 0$, $\|v\|_h^2 = (v, v)_h$. -/
theorem discreteL2Norm_sq {h : ℝ} (hh : 0 ≤ h) (v : Fin (n + 2) → ℝ) :
    discreteL2Norm n h v ^ 2 = discreteInner n h v v :=
  Real.sq_sqrt (discreteInner_self_nonneg hh v)

/-- The discrete $H^1$ seminorm is nonnegative. -/
theorem discreteH1Seminorm_nonneg (h : ℝ) (v : Fin (n + 2) → ℝ) :
    0 ≤ discreteH1Seminorm n h v := Real.sqrt_nonneg _

/-- For $h \ge 0$, $|\!|\!|v|\!|\!|_h^2 = h \sum_{j=0}^{n} ((v_{j+1} - v_j)/h)^2$. -/
theorem discreteH1Seminorm_sq {h : ℝ} (hh : 0 ≤ h) (v : Fin (n + 2) → ℝ) :
    discreteH1Seminorm n h v ^ 2 = h * ∑ j, discreteDeriv n h v j ^ 2 :=
  Real.sq_sqrt (mul_nonneg hh (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- The discrete $H^1$ seminorm is the discrete $L^2$ norm of the difference quotient $v_h^{(1)}$ on
the $n + 1$ panels ([quarteroni2000numerical] Remark 12.1): $|\!|\!|v|\!|\!|_h = (h
\sum_{j=0}^{n} ((v_{j+1} - v_j)/h)^2)^{1/2}$.

The panel sum has all weights $1$, while `FiniteDifference.discreteInner` has the trapezoidal
weights on the nodes. -/
theorem discreteH1Seminorm_eq_norm_discreteDeriv (h : ℝ) (v : Fin (n + 2) → ℝ) :
    discreteH1Seminorm n h v = √(h * ∑ j, discreteDeriv n h v j ^ 2) := rfl

/-- For a grid function $w$ and $v \in V_h^0$, the endpoint terms of the discrete inner product
vanish: $(w, v)_h = h \sum_{j=1}^{n} w_j v_j$. -/
theorem discreteInner_eq_sum_interior (h : ℝ) (w : Fin (n + 2) → ℝ) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    discreteInner n h w v = h * ∑ i, w i.succ.castSucc * interior n v i := by
  unfold discreteInner
  congr 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, hv.1, Fin.succ_last, hv.2]
  simp only [mul_zero, zero_add, add_zero]
  exact Finset.sum_congr rfl fun i _ => by rw [Fin.succ_castSucc, gridWeight_succ_castSucc, one_mul,
    interior_apply]

/-- For interior values $g = (g_1, \dots, g_n)$ and $v \in V_h^0$, the discrete inner product of the
extension of $g$ by zero with $v$ is $h \sum_{j=1}^{n} g_j v_j$. -/
theorem discreteInner_ofInterior (h : ℝ) (g : Fin n → ℝ) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    discreteInner n h (ofInterior n g) v = h * ∑ i, g i * interior n v i := by
  rw [discreteInner_eq_sum_interior h _ hv]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [ofInterior_succ_castSucc]

/-- The **Cauchy–Schwarz inequality** for the discrete inner product: for $h \ge 0$ and grid
functions $w$, $v$, $(w, v)_h \le \|w\|_h \|v\|_h$. -/
theorem discreteInner_le_discreteL2Norm_mul {h : ℝ} (hh : 0 ≤ h) (w v : Fin (n + 2) → ℝ) :
    discreteInner n h w v ≤ discreteL2Norm n h w * discreteL2Norm n h v := by
  have hc : ∀ k, 0 ≤ h * gridWeight n k := fun k => mul_nonneg hh (gridWeight_nonneg k)
  have e1 : discreteInner n h w v
      = ∑ k, (√(h * gridWeight n k) * w k) * (√(h * gridWeight n k) * v k) := by
    unfold discreteInner
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := Real.mul_self_sqrt (hc k)
    linear_combination (-(w k * v k)) * this
  have e2 : ∀ u : Fin (n + 2) → ℝ, discreteL2Norm n h u
      = √(∑ k, (√(h * gridWeight n k) * u k) ^ 2) := fun u => by
    unfold discreteL2Norm discreteInner
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, Real.sq_sqrt (hc k)]
    ring
  rw [e1, e2, e2]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-! ### Summation by parts and the energy identities -/

/-- **Summation by parts** ([quarteroni2000numerical] §12.2.1). For grid functions $w$, $v$,
$$\sum_{j=0}^{n} (w_{j+1} - w_j) v_j
  = w_{n+1} v_{n+1} - w_0 v_0 - \sum_{j=0}^{n} (v_{j+1} - v_j) w_{j+1}.$$ -/
theorem sum_sub_mul_eq_sub_sum (w v : Fin (n + 2) → ℝ) :
    ∑ j : Fin (n + 1), (w j.succ - w j.castSucc) * v j.castSucc
      = w (Fin.last (n + 1)) * v (Fin.last (n + 1)) - w 0 * v 0
        - ∑ j : Fin (n + 1), (v j.succ - v j.castSucc) * w j.succ := by
  have htel : ∑ j : Fin (n + 1), (w j.succ * v j.succ - w j.castSucc * v j.castSucc)
      = w (Fin.last (n + 1)) * v (Fin.last (n + 1)) - w 0 * v 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 := Fin.sum_univ_succ (fun k : Fin (n + 2) => w k * v k)
    have h2 := Fin.sum_univ_castSucc (fun k : Fin (n + 2) => w k * v k)
    linarith
  rw [← htel, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A shifted summation by parts. For a panel function $e = (e_0, \dots, e_n)$ and $v \in V_h^0$,
$$\sum_{j=1}^{n} (e_j - e_{j-1}) v_j = -\sum_{j=0}^{n} e_j (v_{j+1} - v_j).$$

The energy identities follow from it. -/
theorem sum_succ_sub_castSucc_mul_eq_neg_sum (e : Fin (n + 1) → ℝ) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    ∑ i : Fin n, (e i.succ - e i.castSucc) * v i.succ.castSucc
      = -∑ j : Fin (n + 1), e j * (v j.succ - v j.castSucc) := by
  have h1 : ∑ i : Fin n, e i.succ * v i.succ.castSucc = ∑ j : Fin (n + 1), e j * v j.castSucc := by
    rw [Fin.sum_univ_succ (f := fun j => e j * v j.castSucc), Fin.castSucc_zero, hv.1, mul_zero,
      zero_add]
  have h2 : ∑ i : Fin n, e i.castSucc * v i.succ.castSucc = ∑ j : Fin (n + 1), e j * v j.succ := by
    rw [Fin.sum_univ_castSucc (f := fun j => e j * v j.succ), Fin.succ_last, hv.2, mul_zero,
      add_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [Fin.succ_castSucc]
  calc ∑ i : Fin n, (e i.succ - e i.castSucc) * v i.succ.castSucc
      = ∑ i : Fin n, e i.succ * v i.succ.castSucc
          - ∑ i : Fin n, e i.castSucc * v i.succ.castSucc := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ j : Fin (n + 1), e j * v j.castSucc - ∑ j : Fin (n + 1), e j * v j.succ := by rw [h1, h2]
    _ = -∑ j : Fin (n + 1), e j * (v j.succ - v j.castSucc) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- The **energy identity** behind [quarteroni2000numerical] Lemma 12.1. Let $h \neq 0$, let $w$ be
a grid function and let $v \in V_h^0$. Then
$$h \sum_{j=1}^{n} (L_h w)_j v_j = h^{-1} \sum_{j=0}^{n} (w_{j+1} - w_j)(v_{j+1} - v_j).$$

Only $v$ needs to vanish at the endpoints. Since $v \in V_h^0$, the left side is $(L_h w, v)_h$. -/
theorem discreteInner_discreteLaplacian_eq {h : ℝ} (hh : h ≠ 0) {w v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    h * ∑ i, discreteLaplacian n h w i * interior n v i
      = h⁻¹ * ∑ j : Fin (n + 1), (w j.succ - w j.castSucc) * (v j.succ - v j.castSucc) := by
  have key := sum_succ_sub_castSucc_mul_eq_neg_sum (fun j => w j.succ - w j.castSucc) hv
  have e : ∀ i : Fin n, discreteLaplacian n h w i * interior n v i
      = -(h ^ 2)⁻¹ * (((w i.succ.succ - w i.succ.castSucc)
          - (w i.castSucc.succ - w i.castSucc.castSucc))
        * v i.succ.castSucc) := fun i => by
    rw [discreteLaplacian_apply, interior_apply, Fin.succ_castSucc]
    field_simp
    ring
  simp only [e]
  rw [← Finset.mul_sum, key]
  field_simp

/-- The discrete operator is **symmetric** on $V_h^0$ ([quarteroni2000numerical] Lemma 12.1). For
$h \neq 0$ and $w, v \in V_h^0$,
$$(L_h w, v)_h = (w, L_h v)_h,$$
where the interior grid functions $L_h w$ and $L_h v$ are extended by zero to the endpoints. -/
theorem discreteInner_discreteLaplacian_comm {h : ℝ} (hh : h ≠ 0) {w v : Fin (n + 2) → ℝ}
    (hw : w ∈ gridZero n) (hv : v ∈ gridZero n) :
    discreteInner n h (ofInterior n (discreteLaplacian n h w)) v
      = discreteInner n h w (ofInterior n (discreteLaplacian n h v)) := by
  rw [discreteInner_ofInterior h _ hv, discreteInner_comm, discreteInner_ofInterior h _ hw,
    discreteInner_discreteLaplacian_eq hh hv, discreteInner_discreteLaplacian_eq hh hw]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The **energy identity** $(L_h v, v)_h = |\!|\!|v|\!|\!|_h^2$ of [quarteroni2000numerical]
(12.13). For $h > 0$ and $v \in V_h^0$,
$$h \sum_{j=1}^{n} (L_h v)_j v_j = |\!|\!|v|\!|\!|_h^2.$$
-/
theorem discreteInner_discreteLaplacian_self {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    h * ∑ i, discreteLaplacian n h v i * interior n v i = discreteH1Seminorm n h v ^ 2 := by
  rw [discreteInner_discreteLaplacian_eq hh.ne' hv, discreteH1Seminorm_sq hh.le, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [discreteDeriv]
  field_simp

/-- The discrete operator is **positive definite** on $V_h^0$ ([quarteroni2000numerical] Lemma
12.1). For $h > 0$ and $v \in V_h^0$ with $v \neq 0$,
$$h \sum_{j=1}^{n} (L_h v)_j v_j > 0.$$
-/
theorem discreteInner_discreteLaplacian_self_pos {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) (hv0 : v ≠ 0) :
    0 < h * ∑ i, discreteLaplacian n h v i * interior n v i := by
  rw [discreteInner_discreteLaplacian_self hh hv, discreteH1Seminorm_sq hh.le]
  refine mul_pos hh (Finset.sum_pos' (fun j _ => sq_nonneg _) ?_)
  by_contra hcon
  push Not at hcon
  refine hv0 (eq_zero_of_forall_succ_eq hv.1 fun j => ?_)
  have := hcon j (Finset.mem_univ j)
  have h0 : discreteDeriv n h v j = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _))
  rw [discreteDeriv, div_eq_zero_iff, or_iff_left hh.ne', sub_eq_zero] at h0
  exact h0

/-- The seminorm $|\!|\!|\cdot|\!|\!|_h$ **is a norm on $V_h^0$**, the positive definiteness clause
of [quarteroni2000numerical] Lemma 12.1. For $h > 0$ and $v \in V_h^0$, $|\!|\!|v|\!|\!|_h = 0$
if and only if $v = 0$. -/
theorem discreteH1Seminorm_eq_zero_iff {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) : discreteH1Seminorm n h v = 0 ↔ v = 0 := by
  constructor
  · intro h0
    by_contra hv0
    have := discreteInner_discreteLaplacian_self_pos hh hv hv0
    rw [discreteInner_discreteLaplacian_self hh hv, h0] at this
    simp at this
  · rintro rfl
    simp [discreteH1Seminorm, discreteDeriv]

/-! ### The discrete Poincaré inequality and the energy stability estimate -/

/-- The **discrete Poincaré inequality** in squared form. For $h > 0$ and $v \in V_h^0$,
$$\|v\|_h^2 \le \frac{((n + 1) h)^2}{2}\, h \sum_{j=0}^{n} \Big(\frac{v_{j+1} - v_j}{h}\Big)^2 =
  \frac{((n + 1) h)^2}{2}\, |\!|\!|v|\!|\!|_h^2.$$
This is [quarteroni2000numerical] Lemma 12.2 on an interval of length $(n + 1) h$. -/
theorem discreteInner_self_le_sq_mul {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    discreteInner n h v v ≤ ((n + 1) * h) ^ 2 / 2 * (h * ∑ j, discreteDeriv n h v j ^ 2) := by
  -- the padded grid function and its increments, indexed by `ℕ`
  set V : ℕ → ℝ := fun m => if hm : m < n + 2 then v ⟨m, hm⟩ else 0 with hV
  set D : ℕ → ℝ := fun k => if hk : k < n + 1 then v ⟨k + 1, by omega⟩ - v ⟨k, by omega⟩ else 0
    with hD
  have hV0 : V 0 = 0 := by simp [hV, hv.1]
  have hVD : ∀ k, k < n + 1 → V (k + 1) - V k = D k := fun k hk => by
    simp only [hV, hD, dite_eq_left hk, dite_eq_left (show k + 1 < n + 2 by omega),
      dite_eq_left (show k < n + 2 by omega)]
  have hVsum : ∀ m, m ≤ n + 1 → V m = ∑ k ∈ Finset.range m, D k := fun m hm => by
    have htel := Finset.sum_range_sub V m
    rw [hV0, sub_zero] at htel
    rw [← htel]
    exact Finset.sum_congr rfl fun k hk => hVD k (by have := Finset.mem_range.1 hk; omega)
  set S := ∑ k ∈ Finset.range (n + 1), D k ^ 2 with hS
  -- `V m² ≤ m S` for `m ≤ n + 1`
  have hVsq : ∀ m, m ≤ n + 1 → V m ^ 2 ≤ m * S := fun m hm => by
    rw [hVsum m hm]
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.range m) (f := D)).trans ?_
    rw [Finset.card_range]
    have hsub : Finset.range m ⊆ Finset.range (n + 1) := Finset.range_subset_range.2 hm
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      hsub fun k _ _ => sq_nonneg _) (by positivity)
  -- the two norms in terms of `V` and `D`
  have hinner : discreteInner n h v v = h * ∑ m ∈ Finset.range n, V (m + 1) ^ 2 := by
    rw [discreteInner_eq_sum_interior h v hv, ← Fin.sum_univ_eq_sum_range]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfin : (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 2)) = i.succ.castSucc := Fin.ext (by simp)
    rw [interior_apply, hV]
    simp only [dite_eq_left (show (i : ℕ) + 1 < n + 2 by omega), hfin]
    ring
  have hseminorm : ∑ j, discreteDeriv n h v j ^ 2 = S / h ^ 2 := by
    rw [hS, ← Fin.sum_univ_eq_sum_range, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [discreteDeriv, div_pow, hD]
    simp only [dite_eq_left j.isLt]
    rfl
  -- the Gauss sum `∑_{m<n} (m + 1) ≤ (n + 1)²/2`
  have hgauss : ∑ m ∈ Finset.range n, ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 / 2 := by
    have h1 : ∑ m ∈ Finset.range n, ((m : ℝ) + 1) = ((∑ m ∈ Finset.range (n + 1), m : ℕ) : ℝ) := by
      rw [Finset.sum_range_succ', Nat.cast_add, Nat.cast_sum, Nat.cast_zero, add_zero]
      push_cast
      rfl
    have h2 := Finset.sum_range_id_mul_two (n + 1)
    rw [Nat.add_sub_cancel] at h2
    have h3 : ((∑ m ∈ Finset.range (n + 1), m : ℕ) : ℝ) * 2 = ((n : ℝ) + 1) * n := by
      exact_mod_cast h2
    nlinarith
  rw [hinner, hseminorm]
  calc h * ∑ m ∈ Finset.range n, V (m + 1) ^ 2
      ≤ h * ∑ m ∈ Finset.range n, ((m : ℝ) + 1) * S := by
        gcongr with m hm
        have := hVsq (m + 1) (by have := Finset.mem_range.1 hm; omega)
        push_cast at this
        exact this
    _ = h * (∑ m ∈ Finset.range n, ((m : ℝ) + 1)) * S := by rw [← Finset.sum_mul]; ring
    _ ≤ h * (((n : ℝ) + 1) ^ 2 / 2) * S := by gcongr
    _ = ((n + 1) * h) ^ 2 / 2 * (h * (S / h ^ 2)) := by field_simp

/-- The **discrete Poincaré inequality**. For $h > 0$ and $v \in V_h^0$,
$$\|v\|_h \le \frac{(n + 1) h}{\sqrt 2}\, |\!|\!|v|\!|\!|_h.$$
This is [quarteroni2000numerical] Lemma 12.2 on an interval of length $(n + 1) h$.

On the uniform grid $(n + 1) h = b - a$, so the constant is $(b - a)/\sqrt 2$; on $[0, 1]$ it is
the book's $1/\sqrt 2$. -/
theorem discreteL2Norm_le_discreteH1Seminorm {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    discreteL2Norm n h v ≤ ((n + 1) * h / √2) * discreteH1Seminorm n h v := by
  have hpos : 0 ≤ ((n : ℝ) + 1) * h / √2 := by positivity
  rw [← abs_of_nonneg (discreteL2Norm_nonneg h v),
    ← abs_of_nonneg (mul_nonneg hpos (discreteH1Seminorm_nonneg h v)), ← sq_le_sq, mul_pow,
    discreteL2Norm_sq hh.le, discreteH1Seminorm_sq hh.le, div_pow, Real.sq_sqrt zero_le_two]
  exact discreteInner_self_le_sq_mul hh hv

/-- **Stability by the energy method** ([quarteroni2000numerical] (12.17) on a general interval).
Let $h > 0$, let $u \in V_h^0$, and let $f$ be a grid function with $(L_h u)_j = f_j$ at the
interior nodes $j = 1, \dots, n$. Then
$$|\!|\!|u|\!|\!|_h \le \frac{(n + 1) h}{\sqrt 2} \|f\|_h \quad\text{and}\quad \|u\|_h \le
  \frac{((n + 1) h)^2}{2} \|f\|_h.$$

On $[0, 1]$, where $(n + 1) h = 1$, the second bound is the book's $\|u_h\|_h \le \|f_h\|_h/2$.
The endpoint values of $f$ do not enter the equation, but they enter $\|f\|_h$ with weight
$1/2$. -/
theorem discreteL2Norm_le_of_discreteLaplacian_eq {h : ℝ} (hh : 0 < h) {u f : Fin (n + 2) → ℝ}
    (hu : u ∈ gridZero n) (hL : discreteLaplacian n h u = interior n f) :
    discreteH1Seminorm n h u ≤ ((n + 1) * h / √2) * discreteL2Norm n h f ∧
      discreteL2Norm n h u ≤ ((n + 1) * h) ^ 2 / 2 * discreteL2Norm n h f := by
  have hC : 0 ≤ ((n : ℝ) + 1) * h / √2 := by positivity
  have hP := discreteL2Norm_le_discreteH1Seminorm hh hu
  -- `‖|u|‖_h² = (f, u)_h ≤ ‖f‖_h ‖u‖_h`
  have h1 : discreteH1Seminorm n h u ^ 2 ≤ discreteL2Norm n h f * discreteL2Norm n h u := by
    have hfu := discreteInner_eq_sum_interior h f hu
    simp only [interior_apply] at hfu ⊢
    rw [← discreteInner_discreteLaplacian_self hh hu, hL]
    simp only [interior_apply]
    rw [← hfu]
    exact discreteInner_le_discreteL2Norm_mul hh.le f u
  have hA : discreteH1Seminorm n h u ≤ ((n + 1) * h / √2) * discreteL2Norm n h f := by
    rcases (discreteH1Seminorm_nonneg h u).eq_or_lt with h0 | h0
    · rw [← h0]; exact mul_nonneg hC (discreteL2Norm_nonneg h f)
    · have := h1.trans (mul_le_mul_of_nonneg_left hP (discreteL2Norm_nonneg h f))
      rw [sq] at this
      nlinarith
  refine ⟨hA, hP.trans ?_⟩
  calc ((n + 1) * h / √2) * discreteH1Seminorm n h u
      ≤ ((n + 1) * h / √2) * (((n + 1) * h / √2) * discreteL2Norm n h f) :=
        mul_le_mul_of_nonneg_left hA hC
    _ = ((n + 1) * h / √2 * ((n + 1) * h / √2)) * discreteL2Norm n h f := by ring
    _ = ((n + 1) * h) ^ 2 / 2 * discreteL2Norm n h f := by
        rw [div_mul_div_comm, Real.mul_self_sqrt zero_le_two]
        ring

/-! ### The truncation error -/

/-- The **local truncation error** of [quarteroni2000numerical] (12.18). For functions
$u, f : \mathbb{R} \to \mathbb{R}$ and the uniform grid on $[a, b]$ with $n$ interior nodes, it
is the interior grid function
$$\tau_j = (L_h u)_j - f(x_j), \qquad j = 1, \dots, n,$$
where $L_h$ acts on the grid values $u(x_k)$ with the grid step $h$. -/
noncomputable def truncationError (a b : ℝ) (n : ℕ) (u f : ℝ → ℝ) : Fin n → ℝ :=
  discreteLaplacian n (gridStep a b n) (u ∘ uniformGrid a b n)
    - fun i => f (uniformGrid a b n i.succ.castSucc)

/-- The value of the truncation error at the interior node $i + 1$ is $(L_h u)_{i+1} - f(x_{i+1})$.
-/
theorem truncationError_apply (u f : ℝ → ℝ) (i : Fin n) :
    truncationError a b n u f i
      = discreteLaplacian n (gridStep a b n) (u ∘ uniformGrid a b n) i
        - f (uniformGrid a b n i.succ.castSucc) := rfl

/-- The **error equation** ([quarteroni2000numerical] Remark 12.3, (12.22)). Let
$u, f : \mathbb{R} \to \mathbb{R}$, and let the grid function $u_h$ satisfy
$(L_h u_h)_j = f(x_j)$ at the interior nodes. Then the error $e_j = u(x_j) - (u_h)_j$ satisfies
$L_h e = \tau_h$. -/
theorem error_eq_of_discreteLaplacian_eq (u f : ℝ → ℝ) {uh : Fin (n + 2) → ℝ}
    (hL : discreteLaplacian n (gridStep a b n) uh
      = fun i => f (uniformGrid a b n i.succ.castSucc)) :
    discreteLaplacian n (gridStep a b n) (u ∘ uniformGrid a b n - uh)
      = truncationError a b n u f := by
  rw [map_sub, hL]
  rfl

/-! ### Consistency under a Lipschitz third derivative -/

/-- **Consistency under a Lipschitz third derivative** ([quarteroni2000numerical] Remark 12.2). Let
$a < b$, let $u$ be of class $C^3$ on $[a, b]$, let $u'''$ be Lipschitz continuous on $(a, b)$
with constant $M \ge 0$, and let $u'' = -f$ on $(a, b)$. Then at every interior node,
$$|\tau_j| \le \frac{M h^2}{12}.$$

The book states the weaker bound $M h^2$. The proof uses the integral form of the Taylor
remainder, as in (12.21) of the book. -/
theorem abs_truncationError_le_of_lipschitzOnWith (hab : a < b) {u f : ℝ → ℝ} {M : NNReal}
    (hu : ContDiffOn ℝ 3 u (Icc a b)) (hM : LipschitzOnWith M (iteratedDeriv 3 u) (Ioo a b))
    (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x) (i : Fin n) :
    |truncationError a b n u f i| ≤ (M : ℝ) * gridStep a b n ^ 2 / 12 := by
  set h := gridStep a b n with hh
  set x := uniformGrid a b n i.succ.castSucc with hxdef
  have hpos : 0 < h := gridStep_pos hab
  have hne0 : h ≠ 0 := hpos.ne'
  have hx : x ∈ Ioo a b := uniformGrid_interior_mem_Ioo hab i
  have hxm : uniformGrid a b n i.castSucc.castSucc = x - h := by
    rw [hxdef, ← Fin.succ_castSucc, uniformGrid_succ]; ring
  have hxp : uniformGrid a b n i.succ.succ = x + h := by rw [hxdef, uniformGrid_succ]
  have hsub : Icc (x - h) (x + h) ⊆ Icc a b := by
    rw [← hxm, ← hxp]
    exact Icc_subset_Icc (uniformGrid_mem_Icc hab.le _).1 (uniformGrid_mem_Icc hab.le _).2
  have hcx : ContDiffAt ℝ 3 u x := hu.contDiffAt (Icc_mem_nhds hx.1 hx.2)
  -- the two Taylor expansions
  have key : ∀ y : ℝ, y ∈ Icc (x - h) (x + h) → x ≠ y →
      |u y - (u x + (y - x) * iteratedDeriv 1 u x + (y - x) ^ 2 / 2 * iteratedDeriv 2 u x
        + (y - x) ^ 3 / 6 * iteratedDeriv 3 u x)| ≤ (M : ℝ) * (y - x) ^ 4 / 24 := by
    intro y hy hne
    have hxmem : x ∈ Icc (x - h) (x + h) := ⟨by linarith, by linarith⟩
    have hIcc : Set.uIcc x y ⊆ Icc a b :=
      (Set.Icc_subset_Icc (le_inf hxmem.1 hy.1) (sup_le hxmem.2 hy.2)).trans hsub
    have hIoo : Set.uIoo x y ⊆ Ioo a b :=
      Set.Ioo_subset_Ioo (le_inf hx.1.le (hsub hy).1) (sup_le hx.2.le (hsub hy).2)
    refine abs_sub_taylor_three_le_of_lipschitz hne M.coe_nonneg (hu.mono hIcc) hcx ?_
    intro t ht
    have hEq : iteratedDerivWithin 3 u (uIcc x y) t = iteratedDeriv 3 u t :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
        (hu.contDiffAt (Icc_mem_nhds (hIoo ht).1 (hIoo ht).2))
        (Set.uIoo_subset_uIcc_self ht)
    rw [hEq]
    simpa [Real.dist_eq] using hM.dist_le_mul t (hIoo ht) x hx
  have hplus := key (x + h) ⟨by linarith, le_rfl⟩ (by linarith)
  have hminus := key (x - h) ⟨le_rfl, by linarith⟩ (by linarith)
  have hxa : x + h - x = h := by ring
  have hxb : x - h - x = -h := by ring
  rw [hxa] at hplus
  rw [hxb] at hminus
  -- the truncation error is the sum of the two remainders, divided by `h²`
  have hfx : f x = -iteratedDeriv 2 u x := by
    rw [hu'' x hx, neg_neg]
  have hτ : truncationError a b n u f i
      = -((u (x + h) - (u x + h * iteratedDeriv 1 u x + h ^ 2 / 2 * iteratedDeriv 2 u x
            + h ^ 3 / 6 * iteratedDeriv 3 u x))
          + (u (x - h) - (u x + -h * iteratedDeriv 1 u x + (-h) ^ 2 / 2 * iteratedDeriv 2 u x
            + (-h) ^ 3 / 6 * iteratedDeriv 3 u x))) / h ^ 2 := by
    rw [truncationError_apply, discreteLaplacian_apply]
    simp only [Function.comp_apply]
    rw [← hh, hxm, hxp, ← hxdef, hfx]
    field_simp
    ring
  rw [hτ, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 2), abs_neg]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < h ^ 2)]
  calc |u (x + h) - (u x + h * iteratedDeriv 1 u x + h ^ 2 / 2 * iteratedDeriv 2 u x
          + h ^ 3 / 6 * iteratedDeriv 3 u x)
        + (u (x - h) - (u x + -h * iteratedDeriv 1 u x + (-h) ^ 2 / 2 * iteratedDeriv 2 u x
          + (-h) ^ 3 / 6 * iteratedDeriv 3 u x))|
      ≤ (M : ℝ) * h ^ 4 / 24 + (M : ℝ) * (-h) ^ 4 / 24 := (abs_add_le _ _).trans
        (add_le_add hplus hminus)
    _ = (M : ℝ) * h ^ 2 / 12 * h ^ 2 := by ring

/-- The **truncation error in Lagrange form** ([quarteroni2000numerical] (12.19), with the sign of
the printed formula corrected). Let $a < b$, let $u$ be of class $C^4$ on $[a, b]$, and let
$u'' = -f$ on $(a, b)$. Then at each interior node $x_j$ there are $\xi \in (x_{j-1}, x_j)$ and
$\eta \in (x_j, x_{j+1})$ with
$$\tau_j = -\frac{h^2}{24} \big(u''''(\xi) + u''''(\eta)\big).$$
-/
theorem truncationError_eq_of_contDiffOn (hab : a < b) {u f : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (i : Fin n) :
    ∃ ξ ∈ Ioo (uniformGrid a b n i.castSucc.castSucc) (uniformGrid a b n i.succ.castSucc),
      ∃ η ∈ Ioo (uniformGrid a b n i.succ.castSucc) (uniformGrid a b n i.succ.succ),
        truncationError a b n u f i
          = -(gridStep a b n ^ 2 / 24) * (iteratedDeriv 4 u ξ + iteratedDeriv 4 u η) := by
  set h := gridStep a b n with hh
  set x := uniformGrid a b n i.succ.castSucc with hx
  have hpos : 0 < h := gridStep_pos hab
  have hxm : uniformGrid a b n i.castSucc.castSucc = x - h := by
    rw [hx, ← Fin.succ_castSucc, uniformGrid_succ]; ring
  have hxp : uniformGrid a b n i.succ.succ = x + h := by
    rw [hx, uniformGrid_succ]
  have hsub : Icc (x - h) (x + h) ⊆ Icc a b := by
    rw [← hxm, ← hxp]
    exact Icc_subset_Icc (uniformGrid_mem_Icc hab.le _).1 (uniformGrid_mem_Icc hab.le _).2
  obtain ⟨ξ, hξ, η, hη, hT⟩ :=
    iteratedDeriv_two_sub_secondCentredDiff_eq_two_points hpos (hu.mono hsub)
  refine ⟨ξ, by rw [hxm]; exact hξ, η, by rw [hxp]; exact hη, ?_⟩
  have hfx : f x = -iteratedDeriv 2 u x := by
    rw [hu'' x (uniformGrid_interior_mem_Ioo hab i), neg_neg]
  rw [truncationError_apply, discreteLaplacian_comp_uniformGrid, ← hh, ← hx, hfx, ← hT]
  ring

/-- **Consistency for $C^4$ solutions** ([quarteroni2000numerical] (12.20)). Let $a < b$, let $u$ be
of class $C^4$ on $[a, b]$, let $u'' = -f$ on $(a, b)$, and let $|u''''| \le M$ on $(a, b)$.
Then at every interior node,
$$|\tau_j| \le \frac{h^2}{12} M.$$

The bound in the maximum norm is `FiniteDifference.norm_truncationError_le_of_contDiffOn`. -/
theorem abs_truncationError_le_of_contDiffOn (hab : a < b) {u f : ℝ → ℝ} {M : ℝ}
    (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (hM : ∀ x ∈ Ioo a b, |iteratedDeriv 4 u x| ≤ M) (i : Fin n) :
    |truncationError a b n u f i| ≤ gridStep a b n ^ 2 / 12 * M := by
  obtain ⟨ξ, hξ, η, hη, hT⟩ := truncationError_eq_of_contDiffOn hab hu hu'' i
  have hξ' : ξ ∈ Ioo a b := ⟨(uniformGrid_mem_Icc hab.le _).1.trans_lt hξ.1,
    hξ.2.trans_le (uniformGrid_mem_Icc hab.le _).2⟩
  have hη' : η ∈ Ioo a b := ⟨(uniformGrid_mem_Icc hab.le _).1.trans_lt hη.1,
    hη.2.trans_le (uniformGrid_mem_Icc hab.le _).2⟩
  have h1 := hM ξ hξ'
  have h2 := hM η hη'
  rw [hT, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ gridStep a b n ^ 2 / 24)]
  calc gridStep a b n ^ 2 / 24 * |iteratedDeriv 4 u ξ + iteratedDeriv 4 u η|
      ≤ gridStep a b n ^ 2 / 24 * (M + M) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2)) (by positivity)
    _ = gridStep a b n ^ 2 / 12 * M := by ring

/-- Under the hypotheses of `FiniteDifference.abs_truncationError_le_of_contDiffOn`, the truncation
error satisfies $\|\tau_h\|_\infty \le (h^2/12) M$. -/
theorem norm_truncationError_le_of_contDiffOn (hab : a < b) {u f : ℝ → ℝ} {M : ℝ}
    (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (hM : ∀ x ∈ Ioo a b, |iteratedDeriv 4 u x| ≤ M) :
    ‖truncationError a b n u f‖ ≤ gridStep a b n ^ 2 / 12 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ (Set.nonempty_Ioo.2 hab).some_mem)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim (truncationError a b 0 u f) 0, norm_zero]
    exact mul_nonneg (by positivity) hM0
  refine (pi_norm_le_iff_of_nonneg ?_).2 fun i => ?_
  · have i0 : Fin n := ⟨0, hn⟩
    exact (abs_nonneg _).trans (abs_truncationError_le_of_contDiffOn hab hu hu'' hM i0)
  · rw [Real.norm_eq_abs]
    exact abs_truncationError_le_of_contDiffOn hab hu hu'' hM i

/-- If $u'' = -f$ on the open interval $(a, b)$, then $u'''' = -f''$ at every point of $(a, b)$. -/
theorem iteratedDeriv_four_eq_neg_iteratedDeriv_two {u f : ℝ → ℝ}
    (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x) {x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDeriv 4 u x = -iteratedDeriv 2 f x := by
  have hev : iteratedDeriv 2 u =ᶠ[nhds x] -f :=
    Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun y hy => by
      rw [Pi.neg_apply]; exact hu'' y hy
  have h4 : iteratedDeriv 4 u = iteratedDeriv 2 (iteratedDeriv 2 u) := by
    simp only [iteratedDeriv_eq_iterate]
    exact Function.iterate_add_apply deriv 2 2 u
  rw [h4, hev.iteratedDeriv_eq 2, iteratedDeriv_neg]

/-! ### Stability in the maximum norm and the convergence theorem -/

/-- The **comparison function**. Let $a < b$. The discrete parabola $w_j = (x_j - a)(b - x_j)/2$
satisfies
$$(L_h w)_j = 1, \qquad j = 1, \dots, n.$$

This grid function is the one that [quarteroni2000numerical] Exercise 12.7 obtains as $T_h 1$. -/
theorem discreteLaplacian_parabola (hab : a < b) :
    discreteLaplacian n (gridStep a b n)
      (fun j => (uniformGrid a b n j - a) * (b - uniformGrid a b n j) / 2) = 1 := by
  ext i
  have hpos := gridStep_pos (n := n) hab
  have h1 : uniformGrid a b n i.succ.succ
      = uniformGrid a b n i.succ.castSucc + gridStep a b n := uniformGrid_succ i.succ
  have h2 : uniformGrid a b n i.castSucc.castSucc
      = uniformGrid a b n i.succ.castSucc - gridStep a b n := by
    have h := uniformGrid_succ (a := a) (b := b) i.castSucc
    rw [Fin.succ_castSucc] at h
    linarith
  rw [discreteLaplacian_apply, Pi.one_apply]
  simp only [h1, h2]
  field_simp
  ring

/-- The discrete parabola $w_j = (x_j - a)(b - x_j)/2$ lies in $V_h^0$. -/
theorem parabola_mem_gridZero :
    (fun j => (uniformGrid a b n j - a) * (b - uniformGrid a b n j) / 2) ∈ gridZero n := by
  constructor <;> simp

/-- If $a \le b$, the discrete parabola $w_j = (x_j - a)(b - x_j)/2$ has maximum norm at most
$(b - a)^2/8$. -/
theorem norm_parabola_le (hab : a ≤ b) :
    ‖fun j => (uniformGrid a b n j - a) * (b - uniformGrid a b n j) / 2‖ ≤ (b - a) ^ 2 / 8 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hj := uniformGrid_mem_Icc (n := n) hab j
  rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith [hj.1, hj.2])]
  nlinarith [hj.1, hj.2, sq_nonneg (b + a - 2 * uniformGrid a b n j)]

/-- **Stability in the maximum norm** ([quarteroni2000numerical] (12.28) on $[a, b]$). Let $a < b$,
let $u \in V_h^0$ on the uniform grid, and let $g = L_h u$. Then
$$\|u\|_\infty \le \frac{(b - a)^2}{8} \|g\|_\infty.$$

The proof is the M-matrix comparison principle `Matrix.IsMMatrix.norm_inv_mulVec_le` with the
discrete parabola of `FiniteDifference.discreteLaplacian_parabola` as the comparison function. -/
theorem norm_le_of_discreteLaplacian_eq (hab : a < b) {u : Fin (n + 2) → ℝ} (hu : u ∈ gridZero n)
    {g : Fin n → ℝ} (hL : discreteLaplacian n (gridStep a b n) u = g) :
    ‖u‖ ≤ (b - a) ^ 2 / 8 * ‖g‖ := by
  set h := gridStep a b n with hh
  have hpos : 0 < h := gridStep_pos hab
  set T := symmTridiagonalToeplitz n (-1) 2 with hT
  have hM := isMMatrix_symmTridiagonalToeplitz_neg_one_two n
  have hdet : IsUnit T.det := (isUnit_iff_isUnit_det _).1 hM.isUnit
  set w : Fin (n + 2) → ℝ := fun j => (uniformGrid a b n j - a) * (b - uniformGrid a b n j) / 2
    with hw
  -- the comparison vector `interior w / h²`
  have hcomp : T *ᵥ ((h ^ 2)⁻¹ • interior n w) = 1 := by
    rw [mulVec_smul, ← discreteLaplacian_eq_mulVec h parabola_mem_gridZero, hh,
      discreteLaplacian_parabola hab]
  -- `interior u = T⁻¹ (h² g)`
  have hint : interior n u = T⁻¹ *ᵥ (h ^ 2 • g) := by
    rw [← hL, discreteLaplacian_eq_mulVec h hu, smul_smul,
      mul_inv_cancel₀ (by positivity), one_smul,
      mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  calc ‖u‖ ≤ ‖interior n u‖ := norm_le_norm_interior_of_mem hu
    _ ≤ ‖(h ^ 2)⁻¹ • interior n w‖ * ‖h ^ 2 • g‖ := by
        rw [hint]; exact hM.norm_inv_mulVec_le hcomp _
    _ = ‖interior n w‖ * ‖g‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
          abs_of_pos (by positivity)]
        field_simp
    _ ≤ (b - a) ^ 2 / 8 * ‖g‖ := by
        gcongr
        exact ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm w _).trans
          (norm_parabola_le hab.le)

/-- The **discrete maximum principle** ([quarteroni2000numerical] §12.2). Let $h > 0$ and
$u \in V_h^0$. If $(L_h u)_j \ge 0$ at every interior node, then $u_j \ge 0$ at every node. -/
theorem nonneg_of_discreteLaplacian_nonneg {h : ℝ} (hh : 0 < h) {u : Fin (n + 2) → ℝ}
    (hu : u ∈ gridZero n) (hL : 0 ≤ discreteLaplacian n h u) : 0 ≤ u := by
  have hM := isMMatrix_symmTridiagonalToeplitz_neg_one_two n
  have hint : 0 ≤ interior n u := by
    refine hM.nonneg_of_mulVec_nonneg fun i => ?_
    have := hL i
    rw [discreteLaplacian_eq_mulVec h hu, Pi.smul_apply, smul_eq_mul] at this
    exact nonneg_of_mul_nonneg_right this (by positivity)
  intro j
  rcases node_eq_zero_or_eq_last_or j with rfl | rfl | ⟨i, rfl⟩
  · simp [hu.1]
  · simp [hu.2]
  · simpa using hint i

/-- **Convergence of the centred scheme** in terms of a bound on $u''''$ ([quarteroni2000numerical]
Theorem 12.1 on $[a, b]$). Let $a < b$, let $u$ be of class $C^4$ on $[a, b]$ with $u'' = -f$
and $|u''''| \le M$ on $(a, b)$ and $u(a) = u(b) = 0$, and let $u_h \in V_h^0$ satisfy
$(L_h u_h)_j = f(x_j)$ at the interior nodes. Then
$$\max_{0 \le j \le n+1} |u(x_j) - (u_h)_j| \le \frac{(b - a)^2}{96} h^2 M.$$
-/
theorem norm_sub_le_of_discreteLaplacian_eq_of_iteratedDeriv_four_le (hab : a < b) {u f : ℝ → ℝ}
    {M : ℝ} (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (hM : ∀ x ∈ Ioo a b, |iteratedDeriv 4 u x| ≤ M) (hua : u a = 0) (hub : u b = 0)
    {uh : Fin (n + 2) → ℝ} (huh : uh ∈ gridZero n)
    (hL : discreteLaplacian n (gridStep a b n) uh
      = fun i => f (uniformGrid a b n i.succ.castSucc)) :
    ‖u ∘ uniformGrid a b n - uh‖ ≤ (b - a) ^ 2 / 96 * gridStep a b n ^ 2 * M := by
  have he : u ∘ uniformGrid a b n - uh ∈ gridZero n := by
    refine Submodule.sub_mem _ ⟨?_, ?_⟩ huh
    · simp [hua]
    · simp [hub]
  have hbound := norm_le_of_discreteLaplacian_eq hab he
    (error_eq_of_discreteLaplacian_eq u f hL)
  calc ‖u ∘ uniformGrid a b n - uh‖ ≤ (b - a) ^ 2 / 8 * ‖truncationError a b n u f‖ := hbound
    _ ≤ (b - a) ^ 2 / 8 * (gridStep a b n ^ 2 / 12 * M) := by
        gcongr
        exact norm_truncationError_le_of_contDiffOn hab hu hu'' hM
    _ = (b - a) ^ 2 / 96 * gridStep a b n ^ 2 * M := by ring

/-- **Convergence of the centred scheme** ([quarteroni2000numerical] Theorem 12.1 on $[a, b]$). Let
$a < b$, let $u$ be of class $C^4$ on $[a, b]$ with $u'' = -f$ on $(a, b)$ and
$u(a) = u(b) = 0$, and let $|f''| \le M$ on $(a, b)$. Let $u_h \in V_h^0$ satisfy
$(L_h u_h)_j = f(x_j)$ at the interior nodes $j = 1, \dots, n$. Then
$$\max_{0 \le j \le n+1} |u(x_j) - (u_h)_j| \le \frac{(b - a)^2}{96} h^2 M.$$
On $[0, 1]$ this is the book's (12.27), $\|u - u_h\|_{h,\infty} \le (h^2/96) \|f''\|_\infty$.

The solution $u$ is a hypothesis; it is not constructed from $f$. Its existence and $C^4$
regularity for $f \in C^2$ come from the Green's function representation of
[quarteroni2000numerical] §12.1. The left side is the maximum norm of
`u ∘ FiniteDifference.uniformGrid a b n - uh`. -/
theorem norm_sub_le_of_discreteLaplacian_eq (hab : a < b) {u f : ℝ → ℝ} {M : ℝ}
    (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (hM : ∀ x ∈ Ioo a b, |iteratedDeriv 2 f x| ≤ M) (hua : u a = 0) (hub : u b = 0)
    {uh : Fin (n + 2) → ℝ} (huh : uh ∈ gridZero n)
    (hL : discreteLaplacian n (gridStep a b n) uh
      = fun i => f (uniformGrid a b n i.succ.castSucc)) :
    ‖u ∘ uniformGrid a b n - uh‖ ≤ (b - a) ^ 2 / 96 * gridStep a b n ^ 2 * M :=
  norm_sub_le_of_discreteLaplacian_eq_of_iteratedDeriv_four_le hab hu hu''
    (fun x hx => by
      rw [iteratedDeriv_four_eq_neg_iteratedDeriv_two hu'' hx, abs_neg]; exact hM x hx)
    hua hub huh hL

/-! ### Variable coefficients -/

/-- The midpoints $x_{j+1/2} = (x_j + x_{j+1})/2$ of the panels, $j = 0, \dots, n$. -/
noncomputable def midGrid (a b : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  (uniformGrid a b n j.castSucc + uniformGrid a b n j.succ) / 2

/-- The **variable-coefficient operator** of [quarteroni2000numerical] (12.32)–(12.33). For
coefficients $\alpha, \gamma : \mathbb{R} \to \mathbb{R}$ and a grid function $w$ on the uniform
grid, it is the interior grid function
$$(L_h w)_j = -\frac{J_{j+1/2}(w) - J_{j-1/2}(w)}{h} + \gamma(x_j) w_j,
  \qquad j = 1, \dots, n,$$
with the midpoint fluxes $J_{j+1/2}(w) = \alpha(x_{j+1/2}) (w_{j+1} - w_j)/h$. It discretizes
$-(\alpha u')' + \gamma u$.

The midpoints are `FiniteDifference.midGrid`. -/
noncomputable def variableCoeffOperator (a b : ℝ) (n : ℕ) (α γ : ℝ → ℝ) :
    (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun w i :=
    -(α (midGrid a b n i.succ) * (w i.succ.succ - w i.succ.castSucc) / gridStep a b n
        - α (midGrid a b n i.castSucc) * (w i.succ.castSucc - w i.castSucc.castSucc)
          / gridStep a b n)
      / gridStep a b n + γ (uniformGrid a b n i.succ.castSucc) * w i.succ.castSucc
  map_add' _ _ := by ext; simp only [Pi.add_apply]; ring
  map_smul' _ _ := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- At the interior node $j$, the variable-coefficient operator is
$-(\alpha_{j+1/2} (w_{j+1} - w_j)/h - \alpha_{j-1/2} (w_j - w_{j-1})/h)/h + \gamma(x_j) w_j$, with
$\alpha_{j \pm 1/2} = \alpha(x_{j \pm 1/2})$. -/
theorem variableCoeffOperator_apply (α γ : ℝ → ℝ) (w : Fin (n + 2) → ℝ) (i : Fin n) :
    variableCoeffOperator a b n α γ w i
      = -(α (midGrid a b n i.succ) * (w i.succ.succ - w i.succ.castSucc) / gridStep a b n
          - α (midGrid a b n i.castSucc) * (w i.succ.castSucc - w i.castSucc.castSucc)
            / gridStep a b n) / gridStep a b n
        + γ (uniformGrid a b n i.succ.castSucc) * w i.succ.castSucc := rfl

/-- With $\alpha = 1$ and $\gamma = 0$, the variable-coefficient operator is the discrete operator
$L_h$ of `FiniteDifference.discreteLaplacian`. -/
theorem variableCoeffOperator_one_zero :
    variableCoeffOperator a b n (fun _ => 1) (fun _ => 0)
      = discreteLaplacian n (gridStep a b n) := by
  refine LinearMap.ext fun w => funext fun i => ?_
  rw [variableCoeffOperator_apply, discreteLaplacian_apply]
  ring

/-- The **energy identity with variable coefficients**. Let $a < b$, let
$\alpha, \gamma : \mathbb{R} \to \mathbb{R}$, let $w$ be a grid function and let $v \in V_h^0$.
Then, with $\alpha_{j+1/2} = \alpha(x_{j+1/2})$ and $\gamma_j = \gamma(x_j)$,
$$\sum_{j=1}^{n} (L_h w)_j v_j
  = h^{-2} \sum_{j=0}^{n} \alpha_{j+1/2} (w_{j+1} - w_j)(v_{j+1} - v_j) +
  \sum_{j=1}^{n} \gamma_j w_j v_j.$$
Here $L_h$ is the variable-coefficient operator. Only $v$ needs to vanish at the endpoints. -/
theorem sum_variableCoeffOperator_mul_interior (hab : a < b) (α γ : ℝ → ℝ)
    {w v : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n) :
    ∑ i, variableCoeffOperator a b n α γ w i * interior n v i
      = (gridStep a b n ^ 2)⁻¹ * ∑ j : Fin (n + 1),
          α (midGrid a b n j) * (w j.succ - w j.castSucc) * (v j.succ - v j.castSucc)
        + ∑ i, γ (uniformGrid a b n i.succ.castSucc) * w i.succ.castSucc * interior n v i := by
  have hpos := gridStep_pos (n := n) hab
  have key := sum_succ_sub_castSucc_mul_eq_neg_sum
    (fun j => α (midGrid a b n j) * (w j.succ - w j.castSucc)) hv
  have e : ∀ i : Fin n, variableCoeffOperator a b n α γ w i * interior n v i
      = -(gridStep a b n ^ 2)⁻¹ * ((α (midGrid a b n i.succ) * (w i.succ.succ - w i.succ.castSucc)
          - α (midGrid a b n i.castSucc) * (w i.castSucc.succ - w i.castSucc.castSucc))
            * v i.succ.castSucc)
        + γ (uniformGrid a b n i.succ.castSucc) * w i.succ.castSucc * interior n v i := fun i => by
    rw [variableCoeffOperator_apply, interior_apply, Fin.succ_castSucc]
    field_simp
  simp only [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, key]
  ring

/-- The **matrix of the variable-coefficient operator** on $V_h^0$ ([quarteroni2000numerical]
(12.34), with the sign of the off-diagonal entries corrected). With
$\alpha_{j+1/2} = \alpha(x_{j+1/2})$ and $\gamma_j = \gamma(x_j)$, it is the $n \times n$ matrix
$$h^{-2} \operatorname{tridiag}\big(-\alpha_{j-1/2},\ \alpha_{j-1/2} + \alpha_{j+1/2},
  \ {-\alpha_{j+1/2}}\big) + \operatorname{diag}(\gamma_1, \dots, \gamma_n).$$
-/
noncomputable def variableCoeffMatrix (a b : ℝ) (n : ℕ) (α γ : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then
      (α (midGrid a b n i.castSucc) + α (midGrid a b n i.succ)) / gridStep a b n ^ 2
        + γ (uniformGrid a b n i.succ.castSucc)
    else if (i : ℕ) + 1 = j then -α (midGrid a b n i.succ) / gridStep a b n ^ 2
    else if (j : ℕ) + 1 = i then -α (midGrid a b n j.succ) / gridStep a b n ^ 2
    else 0

/-- The entries of the variable-coefficient matrix: $(\alpha_{i-1/2} + \alpha_{i+1/2})/h^2 +
\gamma_i$ on the diagonal, $-\alpha_{i+1/2}/h^2$ at positions $(i, i + 1)$ and $(i + 1, i)$, and
$0$ elsewhere. -/
theorem variableCoeffMatrix_apply (α γ : ℝ → ℝ) (i j : Fin n) :
    variableCoeffMatrix a b n α γ i j
      = if i = j then
          (α (midGrid a b n i.castSucc) + α (midGrid a b n i.succ)) / gridStep a b n ^ 2
            + γ (uniformGrid a b n i.succ.castSucc)
        else if (i : ℕ) + 1 = j then -α (midGrid a b n i.succ) / gridStep a b n ^ 2
        else if (j : ℕ) + 1 = i then -α (midGrid a b n j.succ) / gridStep a b n ^ 2
        else 0 := rfl

/-- The variable-coefficient matrix is symmetric. -/
theorem variableCoeffMatrix_isSymm (α γ : ℝ → ℝ) : (variableCoeffMatrix a b n α γ).IsSymm := by
  ext i j
  rw [transpose_apply, variableCoeffMatrix_apply, variableCoeffMatrix_apply]
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rw [ite_eq_right hij.symm, ite_eq_right hij]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- If $\alpha \ge 0$ at all midpoints, the off-diagonal entries of the variable-coefficient matrix
are nonpositive. -/
theorem variableCoeffMatrix_offDiag_nonpos (α γ : ℝ → ℝ) (hα : ∀ j, 0 ≤ α (midGrid a b n j))
    {i j : Fin n} (hij : i ≠ j) : variableCoeffMatrix a b n α γ i j ≤ 0 := by
  rw [variableCoeffMatrix_apply, ite_eq_right hij]
  split_ifs
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (hα _)) (sq_nonneg _)
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (hα _)) (sq_nonneg _)
  · exact le_rfl

/-- For $w \in V_h^0$, the variable-coefficient operator applied to $w$ is the variable-coefficient
matrix applied to the interior values $(w_1, \dots, w_n)$. -/
theorem variableCoeffOperator_eq_mulVec (α γ : ℝ → ℝ) {w : Fin (n + 2) → ℝ} (hw : w ∈ gridZero n) :
    variableCoeffOperator a b n α γ w = variableCoeffMatrix a b n α γ *ᵥ interior n w := by
  ext i
  have hsplit : ∀ j : Fin n, variableCoeffMatrix a b n α γ i j * interior n w j
      = (if j = i then ((α (midGrid a b n i.castSucc) + α (midGrid a b n i.succ))
              / gridStep a b n ^ 2
            + γ (uniformGrid a b n i.succ.castSucc)) * interior n w j else 0)
        - (if (i : ℕ) + 1 = j then α (midGrid a b n i.succ) / gridStep a b n ^ 2 * interior n w j
            else 0)
        - (if (j : ℕ) + 1 = i then
            α (midGrid a b n i.castSucc) / gridStep a b n ^ 2 * interior n w j
            else 0) := by
    intro j
    rw [variableCoeffMatrix_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : j ≠ i := Ne.symm hij
      rw [ite_eq_right hij, ite_eq_right hne]
      by_cases h1 : (i : ℕ) + 1 = j
      · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega)]; ring
      · rw [ite_eq_right h1, ite_eq_right h1]
        by_cases h2 : (j : ℕ) + 1 = i
        · have hji : j.succ = i.castSucc := Fin.ext (by simp [h2])
          rw [ite_eq_left h2, ite_eq_left h2, hji]; ring
        · rw [ite_eq_right h2, ite_eq_right h2]; ring
  rw [mulVec, dotProduct]
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i,
    sum_ite_succ_eq hw.2, sum_ite_pred_eq hw.1, variableCoeffOperator_apply]
  simp only [Finset.mem_univ, ite_true, interior_apply]
  have hpos : gridStep a b n ≠ 0 ∨ gridStep a b n = 0 := ne_or_eq _ _
  rcases hpos with hpos | hpos
  · field_simp
    ring
  · rw [hpos]; simp

/-- The **variable-coefficient matrix is positive definite** ([quarteroni2000numerical] §12.2.3).
Let $a < b$, and let $\alpha, \gamma : \mathbb{R} \to \mathbb{R}$ with $\alpha(x_{j+1/2}) > 0$
at every midpoint and $\gamma(x_j) \ge 0$ at every interior node. Then the matrix of
`FiniteDifference.variableCoeffMatrix` is positive definite.

Its quadratic form at $y \in \mathbb{R}^n$ is $h^{-2} \sum_{j=0}^{n} \alpha_{j+1/2} (y_{j+1} -
y_j)^2 + \sum_{j=1}^{n} \gamma_j y_j^2$ with $y_0 = y_{n+1} = 0$, by the energy identity
`FiniteDifference.sum_variableCoeffOperator_mul_interior`. -/
theorem variableCoeffMatrix_posDef (hab : a < b) (α γ : ℝ → ℝ)
    (hα : ∀ j, 0 < α (midGrid a b n j))
    (hγ : ∀ i : Fin n, 0 ≤ γ (uniformGrid a b n i.succ.castSucc)) :
    (variableCoeffMatrix a b n α γ).PosDef := by
  have hpos := gridStep_pos (n := n) hab
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
  · exact isHermitian_iff_isSymm.2 (variableCoeffMatrix_isSymm α γ)
  · have hw := ofInterior_mem_gridZero (n := n) x
    have hx' : interior n (ofInterior n x) = x := interior_ofInterior x
    rw [star_trivial, ← hx', ← variableCoeffOperator_eq_mulVec α γ hw, dotProduct_comm,
      dotProduct, sum_variableCoeffOperator_mul_interior hab α γ hw]
    have hterm : ∀ i : Fin n, 0 ≤ γ (uniformGrid a b n i.succ.castSucc)
        * ofInterior n x i.succ.castSucc
        * interior n (ofInterior n x) i := fun i => by
      rw [interior_apply, mul_assoc, ← sq]
      exact mul_nonneg (hγ i) (sq_nonneg _)
    refine add_pos_of_pos_of_nonneg (mul_pos (by positivity) (Finset.sum_pos' ?_ ?_))
      (Finset.sum_nonneg fun i _ => hterm i)
    · intro j _
      rw [mul_assoc, ← sq]
      exact mul_nonneg (hα j).le (sq_nonneg _)
    · by_contra hcon
      push Not at hcon
      refine hx (by
        rw [← hx']
        rw [eq_zero_of_forall_succ_eq hw.1 fun j => ?_]
        · simp
        have := hcon j (Finset.mem_univ j)
        rw [mul_assoc, ← sq] at this
        have h0 := le_antisymm this (mul_nonneg (hα j).le (sq_nonneg _))
        rw [mul_eq_zero, or_iff_right (hα j).ne', pow_eq_zero_iff two_ne_zero, sub_eq_zero] at h0
        exact h0)

/-- The **variable-coefficient matrix is an M-matrix**. Let $a < b$, $\alpha(x_{j+1/2}) > 0$ at
every midpoint and $\gamma(x_j) \ge 0$ at every interior node. Then the variable-coefficient
matrix is an M-matrix.

The proof is the Stieltjes criterion: the matrix is positive definite with nonpositive
off-diagonal entries. -/
theorem variableCoeffMatrix_isMMatrix (hab : a < b) (α γ : ℝ → ℝ)
    (hα : ∀ j, 0 < α (midGrid a b n j))
    (hγ : ∀ i : Fin n, 0 ≤ γ (uniformGrid a b n i.succ.castSucc)) :
    (variableCoeffMatrix a b n α γ).IsMMatrix :=
  IsMMatrix.of_posDef_of_offDiag_nonpos (variableCoeffMatrix_posDef hab α γ hα hγ)
    fun _ _ hij => variableCoeffMatrix_offDiag_nonpos α γ (fun j => (hα j).le) hij

/-- If $\alpha \ge 0$ at all midpoints, the sum of the absolute values of the off-diagonal entries
in row $i$ of the variable-coefficient matrix is at most
$(\alpha_{i-1/2} + \alpha_{i+1/2})/h^2$, the flux part of the diagonal entry. -/
theorem variableCoeffMatrix_sum_erase_le (α γ : ℝ → ℝ) (hα : ∀ j, 0 ≤ α (midGrid a b n j))
    (i : Fin n) : ∑ j ∈ Finset.univ.erase i, ‖variableCoeffMatrix a b n α γ i j‖
      ≤ (α (midGrid a b n i.castSucc) + α (midGrid a b n i.succ)) / gridStep a b n ^ 2 := by
  have hsplit : ∀ j : Fin n, j ≠ i → ‖variableCoeffMatrix a b n α γ i j‖
      = (if (i : ℕ) + 1 = j then α (midGrid a b n i.succ) / gridStep a b n ^ 2 else 0)
        + (if (j : ℕ) + 1 = i then α (midGrid a b n i.castSucc) / gridStep a b n ^ 2 else 0) := by
    intro j hj
    rw [variableCoeffMatrix_apply, ite_eq_right (Ne.symm hj), Real.norm_eq_abs]
    by_cases h1 : (i : ℕ) + 1 = j
    · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega), add_zero, abs_div, abs_neg,
        abs_of_nonneg (hα _), abs_of_nonneg (sq_nonneg _)]
    · rw [ite_eq_right h1, ite_eq_right h1, zero_add]
      by_cases h2 : (j : ℕ) + 1 = i
      · have hji : j.succ = i.castSucc := Fin.ext (by simp [h2])
        rw [ite_eq_left h2, ite_eq_left h2, hji, abs_div, abs_neg, abs_of_nonneg (hα _),
          abs_of_nonneg (sq_nonneg _)]
      · rw [ite_eq_right h2, ite_eq_right h2, abs_zero]
  rw [Finset.sum_congr rfl fun j hj => hsplit j (Finset.mem_erase.1 hj).1, Finset.sum_add_distrib]
  have h1 : ∑ j ∈ Finset.univ.erase i,
      (if (i : ℕ) + 1 = j then α (midGrid a b n i.succ) / gridStep a b n ^ 2 else 0)
      ≤ α (midGrid a b n i.succ) / gridStep a b n ^ 2 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_of_le_one_left (div_nonneg (hα _) (sq_nonneg _)) ?_
    have : ((Finset.univ.erase i).filter fun j : Fin n => (i : ℕ) + 1 = j).card ≤ 1 :=
      Finset.card_le_one.2 fun x hx y hy => Fin.ext (by
        have := (Finset.mem_filter.1 hx).2; have := (Finset.mem_filter.1 hy).2; omega)
    exact_mod_cast this
  have h2 : ∑ j ∈ Finset.univ.erase i,
      (if (j : ℕ) + 1 = i then α (midGrid a b n i.castSucc) / gridStep a b n ^ 2 else 0)
      ≤ α (midGrid a b n i.castSucc) / gridStep a b n ^ 2 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_of_le_one_left (div_nonneg (hα _) (sq_nonneg _)) ?_
    have : ((Finset.univ.erase i).filter fun j : Fin n => (j : ℕ) + 1 = i).card ≤ 1 :=
      Finset.card_le_one.2 fun x hx y hy => Fin.ext (by
        have := (Finset.mem_filter.1 hx).2; have := (Finset.mem_filter.1 hy).2; omega)
    exact_mod_cast this
  rw [add_div]
  linarith

/-- The **variable-coefficient matrix is strictly diagonally dominant** by rows
([quarteroni2000numerical] §12.2.3). Let $a < b$, $\alpha(x_{j+1/2}) \ge 0$ at every midpoint
and $\gamma(x_j) > 0$ at every interior node. Then the variable-coefficient matrix is strictly
diagonally dominant by rows. -/
theorem variableCoeffMatrix_isStrictDiagDominant (hab : a < b) (α γ : ℝ → ℝ)
    (hα : ∀ j, 0 ≤ α (midGrid a b n j))
    (hγ : ∀ i : Fin n, 0 < γ (uniformGrid a b n i.succ.castSucc)) :
    (variableCoeffMatrix a b n α γ).IsStrictDiagDominant := by
  intro i
  have hpos := gridStep_pos (n := n) hab
  refine (variableCoeffMatrix_sum_erase_le α γ hα i).trans_lt ?_
  rw [variableCoeffMatrix_apply, ite_eq_left rfl, Real.norm_eq_abs, abs_of_pos]
  · linarith [hγ i]
  · have := hγ i; have := hα i.castSucc; have := hα i.succ; positivity

/-! ### Neumann and Robin boundary rows -/

/-- The **mirror-imaging discretization of a Neumann condition** at $b$ ([quarteroni2000numerical]
(12.35) and the display after it). For coefficients $\alpha, \gamma$, a right side $f$, a
Dirichlet value $d_0$ at $a$ and a flux $g_1$, the condition $J(u)(b) = \alpha(b) u'(b) = g_1$
is discretized as follows. A grid function $u$ is a solution if $u_0 = d_0$, the
variable-coefficient operator satisfies $(L_h u)_j = f(x_j)$ at the interior nodes
$j = 1, \dots, n$, and the last row holds:
$$-\frac{\alpha_{n+1/2}}{h^2} u_n + \Big(\frac{\alpha_{n+1/2}}{h^2} + \frac{\gamma(b)}{2}\Big)
  u_{n+1} = \frac{g_1}{h} + \frac{f(b)}{2}.$$

The book proves nothing about this discretization; it asserts its second-order accuracy without
proof. -/
def IsNeumannSolution (a b : ℝ) (n : ℕ) (α γ f : ℝ → ℝ) (d₀ g₁ : ℝ) (u : Fin (n + 2) → ℝ) : Prop :=
  u 0 = d₀ ∧
  (∀ i : Fin n, variableCoeffOperator a b n α γ u i = f (uniformGrid a b n i.succ.castSucc)) ∧
  -α (midGrid a b n (Fin.last n)) * u (Fin.last n).castSucc / gridStep a b n ^ 2
    + (α (midGrid a b n (Fin.last n)) / gridStep a b n ^ 2 + γ b / 2) * u (Fin.last (n + 1))
    = g₁ / gridStep a b n + f b / 2

/-- The **mirror-imaging discretization of Robin conditions** $\lambda_0 u(a) + \mu_0 u'(a) = g_0$
and $\lambda_1 u(b) + \mu_1 u'(b) = g_1$ at both ends ([quarteroni2000numerical] Exercise 12.10,
with the missing prime on $u'$ restored). For coefficients $\alpha, \gamma$ and a right side
$f$, a grid function $u$ is a solution if the variable-coefficient operator satisfies
$(L_h u)_j = f(x_j)$ at the interior nodes $j = 1, \dots, n$ and the two end rows hold:
$$\Big(\frac{\alpha_{1/2}}{h^2} + \frac{\gamma(a)}{2} + \frac{\alpha(a) \lambda_0}{\mu_0 h}\Big)
  u_0 - \frac{\alpha_{1/2}}{h^2} u_1 = \frac{\alpha(a) g_0}{\mu_0 h} + \frac{f(a)}{2},$$
$$\Big(\frac{\alpha_{n+1/2}}{h^2} + \frac{\gamma(b)}{2} + \frac{\alpha(b) \lambda_1}{\mu_1
  h}\Big) u_{n+1} - \frac{\alpha_{n+1/2}}{h^2} u_n = \frac{\alpha(b) g_1}{\mu_1 h} +
  \frac{f(b)}{2}.$$

The book proves nothing about this discretization. The parameters
$\lambda_0, \mu_0, \lambda_1, \mu_1$ are `lam₀`, `mu₀`, `lam₁`, `mu₁`. By Lean's convention
$x / 0 = 0$, the terms with the denominator $\mu_0 h$ (or $\mu_1 h$) are $0$ when $\mu_0 = 0$
(or $\mu_1 = 0$). -/
def IsRobinSolution (a b : ℝ) (n : ℕ) (α γ f : ℝ → ℝ) (lam₀ mu₀ g₀ lam₁ mu₁ g₁ : ℝ)
    (u : Fin (n + 2) → ℝ) : Prop :=
  (∀ i : Fin n, variableCoeffOperator a b n α γ u i = f (uniformGrid a b n i.succ.castSucc)) ∧
  (α (midGrid a b n 0) / gridStep a b n ^ 2 + γ a / 2 + α a * lam₀ / (mu₀ * gridStep a b n)) * u 0
      - α (midGrid a b n 0) * u 1 / gridStep a b n ^ 2
    = α a * g₀ / (mu₀ * gridStep a b n) + f a / 2 ∧
  (α (midGrid a b n (Fin.last n)) / gridStep a b n ^ 2 + γ b / 2
      + α b * lam₁ / (mu₁ * gridStep a b n)) * u (Fin.last (n + 1))
      - α (midGrid a b n (Fin.last n)) * u (Fin.last n).castSucc / gridStep a b n ^ 2
    = α b * g₁ / (mu₁ * gridStep a b n) + f b / 2

end FiniteDifference
