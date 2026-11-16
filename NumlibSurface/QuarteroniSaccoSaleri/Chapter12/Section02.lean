/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Interval
import Numlib.FiniteDifference.BoundaryValue
import NumlibSurface.QuarteroniSaccoSaleri.Chapter12.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 12.2: Finite Difference Approximation

This module formalizes Section 12.2 of [quarteroni2000numerical]. The model problem $-u'' = f$ on
$(0, 1)$ with $u(0) = u(1) = 0$ is discretized on the uniform grid $x_j = jh$, $h = 1/n$, by the
centred second difference (12.6):
$$-\frac{u_{j+1} - 2u_j + u_{j-1}}{h^2} = f(x_j), \quad j = 1, \dots, n - 1, \qquad u_0 = u_n = 0.$$
The resulting linear system (12.7) has the matrix $A_{fd} = h^{-2} \operatorname{tridiag}(-1, 2,
-1)$ (12.8), which is symmetric, diagonally dominant, positive definite and an M-matrix; the last
property gives the discrete maximum principle. In operator form (12.9)–(12.10) the scheme reads
$L_h u_h = f$ on the grid functions that vanish at both ends. The energy method of Section 12.2.1
gives the symmetry and positivity of $L_h$ (Lemma 12.1), the discrete Poincaré inequality (Lemma
12.2) and the stability estimate (12.17). Taylor expansion gives the consistency (12.19)–(12.20) and
its refinement for a Lipschitz third derivative (Remark 12.2). The discrete Green's function
(12.24)–(12.26) and the stability in the maximum norm (12.28) give Theorem 12.1, the convergence of
the nodal error with order $h^2$. Section 12.2.3 treats the problem $-(\alpha u')' + \gamma u = f$
with variable coefficients, and the discretization of a Neumann or Robin condition by mirror
imaging.

The proofs specialize `Numlib.FiniteDifference.BoundaryValue`, and the Poincaré inequality (12.16)
specializes `Numlib.Analysis.Sobolev.Interval`.

## Main definitions

* Section 12.2, `QuarteroniSaccoSaleri.Chapter12.meshSize`: the mesh size $h = 1/n$.
* Equation (12.6), `QuarteroniSaccoSaleri.Chapter12.IsFiniteDifferenceSolution`: the finite
  difference scheme, equivalently (12.10).
* Equation (12.8), `QuarteroniSaccoSaleri.Chapter12.finiteDifferenceMatrix`: the matrix $A_{fd}$.
* Equation (12.9), `QuarteroniSaccoSaleri.Chapter12.equation_12_9`: the discrete operator $L_h$.
* Equation (12.24), `QuarteroniSaccoSaleri.Chapter12.discreteGreen`: the discrete Green's function
  $G^k$.
* Equation (12.25), `QuarteroniSaccoSaleri.Chapter12.discreteSolutionOperator`: the discrete
  solution operator $T_h$.
* Equation (12.31), `QuarteroniSaccoSaleri.Chapter12.IsVariableCoeffSolution`: the scheme with
  variable coefficients.
* Equations (12.32)–(12.33), `QuarteroniSaccoSaleri.Chapter12.equation_12_32`: the operator with
  variable coefficients.
* Equation (12.34), `QuarteroniSaccoSaleri.Chapter12.equation_12_34`: its matrix.
* Equation (12.35), `QuarteroniSaccoSaleri.Chapter12.equation_12_35`: the Neumann condition by
  mirror imaging.
* Exercise 12.10, `QuarteroniSaccoSaleri.Chapter12.exercise_12_10`: the Robin conditions by mirror
  imaging.
* Exercise 12.11, `QuarteroniSaccoSaleri.Chapter12.exercise_12_11`: the discretization
  $L_h \circ L_h$ of a fourth-order operator.

## Main results

* Equation (12.7), `QuarteroniSaccoSaleri.Chapter12.isFiniteDifferenceSolution_iff_mulVec`: the
  scheme is the linear system $A_{fd} u = f$.
* Section 12.2, `QuarteroniSaccoSaleri.Chapter12.finiteDifferenceMatrix_isSymm`,
  `QuarteroniSaccoSaleri.Chapter12.finiteDifferenceMatrix_posDef` and
  `QuarteroniSaccoSaleri.Chapter12.finiteDifferenceMatrix_diagDominant`: $A_{fd}$ is symmetric,
  positive definite and diagonally dominant.
* Exercise 12.2, `QuarteroniSaccoSaleri.Chapter12.exercise_12_2`: $A_{fd}$ is an M-matrix;
  `QuarteroniSaccoSaleri.Chapter12.exercise_12_2_nonneg` is the discrete maximum principle.
* Equation (12.10), `QuarteroniSaccoSaleri.Chapter12.equation_12_10`: the scheme in operator form.
* Lemma 12.1, `QuarteroniSaccoSaleri.Chapter12.lemma_12_1_symm` and
  `QuarteroniSaccoSaleri.Chapter12.lemma_12_1_pos`: $L_h$ is symmetric and positive definite on
  $V_h^0$.
* Equation (12.13), `QuarteroniSaccoSaleri.Chapter12.equation_12_13`:
  $(L_h v_h, v_h)_h = \|| v_h |\|_h^2$.
* Exercise 12.4, `QuarteroniSaccoSaleri.Chapter12.exercise_12_4`: the inequality (12.15).
* Lemma 12.2, `QuarteroniSaccoSaleri.Chapter12.lemma_12_2`: the discrete Poincaré inequality
  (12.14).
* Remark 12.1, `QuarteroniSaccoSaleri.Chapter12.remark_12_1`: the Poincaré inequality (12.16).
* Equation (12.17), `QuarteroniSaccoSaleri.Chapter12.equation_12_17`: the stability estimate
  $\|u_h\|_h \le \|f_h\|_h / 2$.
* Equation (12.19), `QuarteroniSaccoSaleri.Chapter12.equation_12_19`: the truncation error in
  Lagrange form.
* Equation (12.20), `QuarteroniSaccoSaleri.Chapter12.equation_12_20`: consistency,
  $|\tau_h(x_j)| \le h^2 \|f''\|_\infty / 12$.
* Remark 12.2, `QuarteroniSaccoSaleri.Chapter12.remark_12_2`: consistency when $u'''$ is Lipschitz.
* Remark 12.3, `QuarteroniSaccoSaleri.Chapter12.remark_12_3`: the error equation (12.22)
  $L_h e = \tau_h$.
* Exercise 12.5, `QuarteroniSaccoSaleri.Chapter12.exercise_12_5`: the bound (12.23) $\|\tau_h\|_h^2
  \le 3(\|f\|_h^2 + \|f\|_{L^2(0,1)}^2)$.
* Equations (12.25)–(12.26), `QuarteroniSaccoSaleri.Chapter12.equation_12_25` and
  `QuarteroniSaccoSaleri.Chapter12.equation_12_26`: $T_h$ inverts $L_h$, and $u_h = T_h f$.
* Exercise 12.6, `QuarteroniSaccoSaleri.Chapter12.exercise_12_6`: $G^k(x_j) = h G(x_j, x_k)$.
* Exercise 12.7, `QuarteroniSaccoSaleri.Chapter12.exercise_12_7`: $T_h 1 (x_j) = x_j (1 - x_j)/2$.
* Equation (12.28), `QuarteroniSaccoSaleri.Chapter12.equation_12_28`: stability in the maximum norm.
* Theorem 12.1, `QuarteroniSaccoSaleri.Chapter12.theorem_12_1`: $\|u - u_h\|_{h,\infty} \le h^2
  \|f''\|_\infty / 96$.
* Equation (12.34), `QuarteroniSaccoSaleri.Chapter12.equation_12_34_posDef` and
  `QuarteroniSaccoSaleri.Chapter12.equation_12_34_diagDominant`: the matrix with variable
  coefficients is positive definite, and strictly diagonally dominant when $\gamma > 0$.

## Conventions

* The source counts $n$ subintervals, so there are $n - 1$ interior nodes. The backbone
  `Numlib.FiniteDifference.BoundaryValue` counts the interior nodes. The Lean statements therefore
  use $N = n - 1$ interior nodes, the grid `FiniteDifference.uniformGrid 0 1 N : Fin (N + 2) → ℝ`
  with the nodes $x_0, \dots, x_n$, and the mesh size `QuarteroniSaccoSaleri.Chapter12.meshSize N`
  $= 1/(N + 1)$. The prose uses $n$, as the source does.
* A grid function is `Fin (N + 2) → ℝ`, its values $v_0, \dots, v_n$ at all nodes. A function on the
  interior nodes is `Fin N → ℝ`, where the index `j` stands for the node $x_{j+1}$.
* The space $V_h^0$ of grid functions with $v_0 = v_n = 0$ is `FiniteDifference.gridZero N`. The
  discrete inner product $(w, v)_h = h \sum_{k=0}^n c_k w_k v_k$ with the trapezoidal weights
  $c_0 = c_n = 1/2$ and $c_k = 1$ otherwise is `FiniteDifference.discreteInner N (meshSize N)`. The
  norm $\|v\|_h = (v, v)_h^{1/2}$ is `FiniteDifference.discreteL2Norm N (meshSize N)`. The seminorm
  $\|| v |\|_h = (h \sum_{j=0}^{n-1} ((v_{j+1} - v_j)/h)^2)^{1/2}$ of (12.12) is
  `FiniteDifference.discreteH1Seminorm N (meshSize N)`. The discrete maximum norm
  $\|\cdot\|_{h,\infty}$ is the supremum norm `‖·‖` of `Fin (N + 2) → ℝ` or of `Fin N → ℝ`.
* A function on the interior nodes, such as $L_h w$, enters the inner product $(\cdot, \cdot)_h$
  through its extension by zero, `FiniteDifference.ofInterior N`.
* The truncation error $\tau_h(x_j) = (L_h u)(x_j) - f(x_j)$ of (12.18), for $j = 1, \dots, n - 1$,
  is `FiniteDifference.truncationError 0 1 N u f`.

## Implementation notes

* The name of `FiniteDifference.discreteL2Norm` avoids `FiniteDifference.discreteNorm`, which is the
  $\ell^p$ mesh norm of `Numlib.FiniteDifference.Stencil`.

## Deviations from the source

* **Remark 12.1, equation (12.16)** (generalization). The source states the Poincaré inequality for
  $v \in C^1([a, b])$ with $v(a) = v(b) = 0$; it is proved on $H_0^1(a, b)$. See
  `QuarteroniSaccoSaleri.Chapter12.remark_12_1`.
* **Equation (12.19)** (typo). The source prints the factor $+h^2/24$; with $u''''$ the sign is
  $-h^2/24$. See `QuarteroniSaccoSaleri.Chapter12.equation_12_19`.
* **Remark 12.2** (generalization). The source gives the bound $M h^2$; the bound $M h^2/12$ is
  proved. See `QuarteroniSaccoSaleri.Chapter12.remark_12_2`.
* **Exercise 12.5** (generalization). The source assumes $f \in C^2([0, 1])$; continuity of $f$ is
  enough. See `QuarteroniSaccoSaleri.Chapter12.exercise_12_5`.
* **Equation (12.34)** (typo). The off-diagonal entries $a = (\alpha_{1/2}, \dots)$ of the source
  lack a minus sign. See `QuarteroniSaccoSaleri.Chapter12.equation_12_34`.
* **Exercise 12.10** (typo). The source prints $u(0)$ for $u'(0)$ in the left Robin condition. See
  `QuarteroniSaccoSaleri.Chapter12.exercise_12_10`.

## Not formalized

* **Equation (12.35)**, the second-order accuracy of the discretization of the Neumann condition by
  mirror imaging. The source asserts it without proof.
-/

open Set Finset Matrix MeasureTheory FiniteDifference

namespace QuarteroniSaccoSaleri.Chapter12

variable {N : ℕ}

/-! ### The grid -/

/-- **Section 12.2** of [quarteroni2000numerical], the mesh size. The uniform grid $x_j = jh$,
$j = 0, \dots, n$, of $[0, 1]$ has the **mesh size** $h = 1/n$.

The argument `N` is the number $n - 1$ of interior nodes, so the value is $1/(N + 1)$. The
definition is `FiniteDifference.gridStep 0 1 N`. -/
noncomputable def meshSize (N : ℕ) : ℝ := FiniteDifference.gridStep 0 1 N

/-- The mesh size $h$ is `FiniteDifference.gridStep 0 1 N`. -/
theorem meshSize_def (N : ℕ) : meshSize N = FiniteDifference.gridStep 0 1 N := rfl

/-- The mesh size is $h = 1/n$, where $n = N + 1$ is the number of subintervals. -/
theorem meshSize_eq (N : ℕ) : meshSize N = 1 / ((N : ℝ) + 1) := by
  simp [meshSize, FiniteDifference.gridStep]

/-- The mesh size is positive: $h > 0$. -/
theorem meshSize_pos (N : ℕ) : 0 < meshSize N := gridStep_pos zero_lt_one

/-- The mesh size is not zero: $h \neq 0$. -/
theorem meshSize_ne_zero (N : ℕ) : meshSize N ≠ 0 := (meshSize_pos N).ne'

/-- The $n$ subintervals fill $[0, 1]$: $nh = 1$. -/
theorem succ_mul_meshSize (N : ℕ) : ((N : ℝ) + 1) * meshSize N = 1 := by
  rw [meshSize_def]
  simpa using gridStep_mul_succ (a := (0 : ℝ)) (b := 1) (n := N)

/-- The nodes of the grid are $x_j = jh$ for $j = 0, \dots, n$. -/
theorem uniformGrid_eq (N : ℕ) (j : Fin (N + 2)) :
    FiniteDifference.uniformGrid 0 1 N j = ((j : ℕ) : ℝ) * meshSize N := by
  simp [FiniteDifference.uniformGrid, meshSize]

/-- The interior node with the Lean index `j` is $x_{j+1} = (j + 1) h$. -/
theorem uniformGrid_interior_eq (N : ℕ) (j : Fin N) :
    FiniteDifference.uniformGrid 0 1 N j.succ.castSucc = (((j : ℕ) : ℝ) + 1) * meshSize N := by
  rw [uniformGrid_eq]
  norm_num

/-! ### The scheme (12.6)–(12.8) -/

/-- **Equation (12.8)** of [quarteroni2000numerical]. The **finite difference matrix** is
$$A_{fd} = h^{-2} \operatorname{tridiag}_{n-1}(-1, 2, -1) \in \mathbb{R}^{(n-1) \times (n-1)},$$
the matrix of order $n - 1$ with $2/h^2$ on the diagonal and $-1/h^2$ on the two adjacent
diagonals.

The tridiagonal matrix is `Matrix.symmTridiagonalToeplitz N (-1) 2`. -/
noncomputable def finiteDifferenceMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (meshSize N ^ 2)⁻¹ • Matrix.symmTridiagonalToeplitz N (-1) 2

/-- The entries of $A_{fd}$ are $h^{-2}$ times the entries of $\operatorname{tridiag}(-1, 2, -1)$.
-/
theorem finiteDifferenceMatrix_apply (N : ℕ) (i j : Fin N) :
    finiteDifferenceMatrix N i j
      = (meshSize N ^ 2)⁻¹ * Matrix.symmTridiagonalToeplitz N (-1) 2 i j := rfl

/-- The factor $h^{-2}$ of $A_{fd}$ is positive. -/
theorem inv_meshSize_sq_pos (N : ℕ) : (0 : ℝ) < (meshSize N ^ 2)⁻¹ :=
  inv_pos.2 (pow_pos (meshSize_pos N) 2)

/-- **Section 12.2** of [quarteroni2000numerical], after (12.8). The matrix $A_{fd}$ is symmetric.
-/
theorem finiteDifferenceMatrix_isSymm (N : ℕ) : (finiteDifferenceMatrix N).IsSymm := by
  change (finiteDifferenceMatrix N)ᵀ = finiteDifferenceMatrix N
  rw [finiteDifferenceMatrix, Matrix.transpose_smul, Matrix.symmTridiagonalToeplitz_isSymm]

/-- **Section 12.2** of [quarteroni2000numerical], after (12.8). The matrix $A_{fd}$ is positive
definite, so the linear system (12.7) has a unique solution. -/
theorem finiteDifferenceMatrix_posDef (N : ℕ) : (finiteDifferenceMatrix N).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨Matrix.isHermitian_iff_isSymm.2 (finiteDifferenceMatrix_isSymm N), fun x hx => ?_⟩
  have h := (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two N).dotProduct_mulVec_pos hx
  rw [finiteDifferenceMatrix, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_pos (inv_meshSize_sq_pos N) h

/-- In each row of $\operatorname{tridiag}(-1, 2, -1)$, the off-diagonal entries have absolute
values with sum at most $2$. -/
theorem sum_erase_norm_symmTridiagonalToeplitz_le (N : ℕ) (i : Fin N) :
    ∑ j ∈ Finset.univ.erase i, ‖Matrix.symmTridiagonalToeplitz N (-1) 2 i j‖ ≤ 2 := by
  have hsplit : ∀ j ∈ Finset.univ.erase i, ‖Matrix.symmTridiagonalToeplitz N (-1) 2 i j‖
      = (if (i : ℕ) + 1 = (j : ℕ) then (1 : ℝ) else 0)
        + (if (j : ℕ) + 1 = (i : ℕ) then (1 : ℝ) else 0) := by
    intro j hj
    have hij : ¬((i : ℕ) = (j : ℕ)) := fun h => (Finset.mem_erase.1 hj).1 (Fin.ext h.symm)
    rw [Matrix.symmTridiagonalToeplitz_apply', ite_eq_right hij]
    split_ifs <;> first | (exfalso; omega) | norm_num
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h1 : ∑ j ∈ Finset.univ.erase i, (if (i : ℕ) + 1 = (j : ℕ) then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((Finset.univ.erase i).filter
        fun j : Fin N => (i : ℕ) + 1 = (j : ℕ)).card ≤ 1 :=
      Finset.card_le_one.2 fun x hx y hy => Fin.ext (by
        have h := (Finset.mem_filter.1 hx).2
        have h' := (Finset.mem_filter.1 hy).2
        omega)
    exact_mod_cast hcard
  have h2 : ∑ j ∈ Finset.univ.erase i, (if (j : ℕ) + 1 = (i : ℕ) then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((Finset.univ.erase i).filter
        fun j : Fin N => (j : ℕ) + 1 = (i : ℕ)).card ≤ 1 :=
      Finset.card_le_one.2 fun x hx y hy => Fin.ext (by
        have h := (Finset.mem_filter.1 hx).2
        have h' := (Finset.mem_filter.1 hy).2
        omega)
    exact_mod_cast hcard
  linarith

/-- **Section 12.2** of [quarteroni2000numerical], after (12.8). The matrix $A_{fd}$ is diagonally
dominant by rows:
$$\sum_{j \neq i} |(A_{fd})_{ij}| \le |(A_{fd})_{ii}| \qquad \text{for every } i.$$
-/
theorem finiteDifferenceMatrix_diagDominant (N : ℕ) :
    (finiteDifferenceMatrix N).IsDiagDominant := by
  intro i
  have hc := inv_meshSize_sq_pos N
  have hsum : ∑ j ∈ Finset.univ.erase i, ‖finiteDifferenceMatrix N i j‖
      = (meshSize N ^ 2)⁻¹ * ∑ j ∈ Finset.univ.erase i,
        ‖Matrix.symmTridiagonalToeplitz N (-1) 2 i j‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [finiteDifferenceMatrix_apply, norm_mul, Real.norm_eq_abs, abs_of_pos hc]
  rw [hsum, finiteDifferenceMatrix_apply, norm_mul, Real.norm_eq_abs, abs_of_pos hc,
    Matrix.symmTridiagonalToeplitz_apply_self]
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  simpa using sum_erase_norm_symmTridiagonalToeplitz_le N i

/-- **Equation (12.6)** of [quarteroni2000numerical]. A grid function $u_h = (u_0, \dots, u_n)$ is a
**finite difference solution** with datum $f$ if $u_0 = u_n = 0$ and
$$-\frac{u_{j+1} - 2u_j + u_{j-1}}{h^2} = f(x_j), \qquad j = 1, \dots, n - 1.$$

In operator form this is (12.10), $L_h u_h = f$ at the interior nodes. -/
def IsFiniteDifferenceSolution (N : ℕ) (f : ℝ → ℝ) (u : Fin (N + 2) → ℝ) : Prop :=
  u ∈ FiniteDifference.gridZero N ∧
    FiniteDifference.discreteLaplacian N (meshSize N) u
      = fun j => f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc)

/-- **Equation (12.7)** of [quarteroni2000numerical]. Let $u_h \in V_h^0$. Then $u_h$ is a finite
difference solution with datum $f$ if and only if its interior values solve the linear system
$$A_{fd} \, (u_1, \dots, u_{n-1})^T = (f(x_1), \dots, f(x_{n-1}))^T.$$
-/
theorem isFiniteDifferenceSolution_iff_mulVec (N : ℕ) (f : ℝ → ℝ) {u : Fin (N + 2) → ℝ}
    (hu : u ∈ FiniteDifference.gridZero N) :
    IsFiniteDifferenceSolution N f u ↔
      finiteDifferenceMatrix N *ᵥ FiniteDifference.interior N u
        = fun j => f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc) := by
  rw [IsFiniteDifferenceSolution, and_iff_right hu,
    FiniteDifference.discreteLaplacian_eq_mulVec (meshSize N) hu, finiteDifferenceMatrix,
    Matrix.smul_mulVec]

/-- **Exercise 12.2** of [quarteroni2000numerical], cited in Section 12.2. The matrix $A_{fd}$ is an
M-matrix.

The source hints at a proof by the continuity of $(A_{fd} + \alpha I)^{-1}$ in $\alpha$. The
proof here uses the Stieltjes criterion instead: $A_{fd}$ is positive definite and its
off-diagonal entries are nonpositive (`Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos`).
M-matrices are `Matrix.IsMMatrix`. -/
theorem exercise_12_2 (N : ℕ) : (finiteDifferenceMatrix N).IsMMatrix :=
  Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos (finiteDifferenceMatrix_posDef N) fun i j hij => by
    rw [finiteDifferenceMatrix_apply]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_meshSize_sq_pos N).le
      (Matrix.symmTridiagonalToeplitz_offDiag_nonpos (by norm_num) 2 hij)

/-- **Section 12.2** of [quarteroni2000numerical], the discrete maximum principle. Let $u_h$ be a
finite difference solution with datum $f$, and let $f(x_j) \ge 0$ for $j = 1, \dots, n - 1$.
Then $u_j \ge 0$ for $j = 0, \dots, n$, as for the exact solution. -/
theorem exercise_12_2_nonneg (N : ℕ) {f : ℝ → ℝ} {u : Fin (N + 2) → ℝ}
    (hu : IsFiniteDifferenceSolution N f u)
    (hf : ∀ j : Fin N, 0 ≤ f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc)) : 0 ≤ u :=
  FiniteDifference.nonneg_of_discreteLaplacian_nonneg (meshSize_pos N) hu.1
    (by rw [hu.2]; exact hf)

/-! ### The operator $L_h$ (12.9) -/

/-- **Equation (12.9)** of [quarteroni2000numerical]. The **discrete operator** $L_h$ maps a grid
function $w = (w_0, \dots, w_n)$ to the function on the interior nodes
$$(L_h w)(x_j) = -\frac{w_{j+1} - 2w_j + w_{j-1}}{h^2}, \qquad j = 1, \dots, n - 1.$$

The operator is the linear map `FiniteDifference.discreteLaplacian N (meshSize N)`. -/
noncomputable def equation_12_9 (N : ℕ) : (Fin (N + 2) → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  FiniteDifference.discreteLaplacian N (meshSize N)

/-- The value of the operator (12.9) at an interior node:
$(L_h w)(x_j) = -(w_{j+1} - 2w_j + w_{j-1})/h^2$. -/
theorem equation_12_9_apply (N : ℕ) (w : Fin (N + 2) → ℝ) (j : Fin N) :
    equation_12_9 N w j
      = -(w j.succ.succ - 2 * w j.succ.castSucc + w j.castSucc.castSucc) / meshSize N ^ 2 := rfl

/-- **Equation (12.10)** of [quarteroni2000numerical]. A grid function $u_h$ is a finite difference
solution with datum $f$ if and only if $u_h \in V_h^0$ and $(L_h u_h)(x_j) = f(x_j)$ for
$j = 1, \dots, n - 1$. -/
theorem equation_12_10 (N : ℕ) (f : ℝ → ℝ) (u : Fin (N + 2) → ℝ) :
    IsFiniteDifferenceSolution N f u ↔ u ∈ FiniteDifference.gridZero N ∧
      ∀ j : Fin N, equation_12_9 N u j
        = f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc) :=
  and_congr_right' funext_iff

/-- The operator $L_h$ is injective on $V_h^0$: if $u, v \in V_h^0$ and $L_h u = L_h v$, then
$u = v$. -/
theorem eq_of_equation_12_9_eq (N : ℕ) {u v : Fin (N + 2) → ℝ}
    (hu : u ∈ FiniteDifference.gridZero N) (hv : v ∈ FiniteDifference.gridZero N)
    (h : equation_12_9 N u = equation_12_9 N v) : u = v := by
  have hL : FiniteDifference.discreteLaplacian N (meshSize N) (u - v) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 h
  exact sub_eq_zero.1 (FiniteDifference.discreteLaplacian_injective_on_gridZero
    (meshSize_ne_zero N) (Submodule.sub_mem _ hu hv) hL)

/-- The inner product $(L_h w, v)_h$ for $v \in V_h^0$: for every grid function $w$,
$$(L_h w, v)_h = h \sum_{j=1}^{n-1} (L_h w)(x_j) \, v_j,$$
because the endpoint weights of the trapezoidal rule meet only the zero values of the extension. -/
theorem discreteInner_equation_12_9 (N : ℕ) (w : Fin (N + 2) → ℝ) {v : Fin (N + 2) → ℝ}
    (hv : v ∈ FiniteDifference.gridZero N) :
    FiniteDifference.discreteInner N (meshSize N)
        (FiniteDifference.ofInterior N (equation_12_9 N w)) v
      = meshSize N * ∑ i, equation_12_9 N w i * FiniteDifference.interior N v i :=
  FiniteDifference.discreteInner_ofInterior _ _ hv

/-! ### Lemma 12.1 and the energy identity -/

/-- **Lemma 12.1** of [quarteroni2000numerical], symmetry. For $w_h, v_h \in V_h^0$,
$$(L_h w_h, v_h)_h = (w_h, L_h v_h)_h.$$
-/
theorem lemma_12_1_symm (N : ℕ) {w v : Fin (N + 2) → ℝ}
    (hw : w ∈ FiniteDifference.gridZero N) (hv : v ∈ FiniteDifference.gridZero N) :
    FiniteDifference.discreteInner N (meshSize N)
        (FiniteDifference.ofInterior N (equation_12_9 N w)) v
      = FiniteDifference.discreteInner N (meshSize N) w
        (FiniteDifference.ofInterior N (equation_12_9 N v)) :=
  FiniteDifference.discreteInner_discreteLaplacian_comm (meshSize_ne_zero N) hw hv

/-- **Equation (12.13)** of [quarteroni2000numerical]. For $v_h \in V_h^0$,
$$(L_h v_h, v_h)_h = \|| v_h |\|_h^2.$$
-/
theorem equation_12_13 (N : ℕ) {v : Fin (N + 2) → ℝ} (hv : v ∈ FiniteDifference.gridZero N) :
    FiniteDifference.discreteInner N (meshSize N)
        (FiniteDifference.ofInterior N (equation_12_9 N v)) v
      = FiniteDifference.discreteH1Seminorm N (meshSize N) v ^ 2 := by
  rw [discreteInner_equation_12_9 N v hv]
  exact FiniteDifference.discreteInner_discreteLaplacian_self (meshSize_pos N) hv

/-- **Lemma 12.1** of [quarteroni2000numerical], positivity. For $v_h \in V_h^0$,
$(L_h v_h, v_h)_h \ge 0$, and $(L_h v_h, v_h)_h = 0$ if and only if $v_h = 0$. -/
theorem lemma_12_1_pos (N : ℕ) {v : Fin (N + 2) → ℝ} (hv : v ∈ FiniteDifference.gridZero N) :
    0 ≤ FiniteDifference.discreteInner N (meshSize N)
        (FiniteDifference.ofInterior N (equation_12_9 N v)) v ∧
      (FiniteDifference.discreteInner N (meshSize N)
        (FiniteDifference.ofInterior N (equation_12_9 N v)) v = 0 ↔ v = 0) := by
  rw [equation_12_13 N hv]
  refine ⟨sq_nonneg _, fun h => ?_, fun h => ?_⟩
  · exact (FiniteDifference.discreteH1Seminorm_eq_zero_iff (meshSize_pos N) hv).1
      (pow_eq_zero_iff two_ne_zero |>.1 h)
  · rw [h]
    simp [FiniteDifference.discreteH1Seminorm, FiniteDifference.discreteDeriv]

/-! ### Lemma 12.2, the discrete Poincaré inequality -/

/-- **Exercise 12.4** of [quarteroni2000numerical], the inequality (12.15) used in the proof of
Lemma 12.2. For $m \in \mathbb{N}$ and $p_0, \dots, p_{m-1} \in \mathbb{R}$,
$$\Big(\sum_{k=0}^{m-1} p_k\Big)^2 \le m \sum_{k=0}^{m-1} p_k^2.$$

The source calls this the Minkowski inequality. It is the Cauchy–Schwarz inequality against the
constant vector. -/
theorem exercise_12_4 {m : ℕ} (p : Fin m → ℝ) : (∑ k, p k) ^ 2 ≤ m * ∑ k, p k ^ 2 := by
  simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := p)

/-- **Lemma 12.2** of [quarteroni2000numerical] (discrete Poincaré inequality, (12.14)). For every
$v_h \in V_h^0$,
$$\|v_h\|_h \le \frac{1}{\sqrt{2}} \|| v_h |\|_h.$$
-/
theorem lemma_12_2 (N : ℕ) {v : Fin (N + 2) → ℝ} (hv : v ∈ FiniteDifference.gridZero N) :
    FiniteDifference.discreteL2Norm N (meshSize N) v
      ≤ 1 / Real.sqrt 2 * FiniteDifference.discreteH1Seminorm N (meshSize N) v := by
  have h1 : ((N : ℝ) + 1) * meshSize N / Real.sqrt 2 = 1 / Real.sqrt 2 := by
    rw [succ_mul_meshSize]
  rw [← h1]
  exact FiniteDifference.discreteL2Norm_le_discreteH1Seminorm (meshSize_pos N) hv

/-- **Remark 12.1** of [quarteroni2000numerical], the seminorm through the discrete derivative. For
every grid function $v_h$,
$$\|| v_h |\|_h = \Big(h \sum_{j=0}^{n-1} \big(v_h^{(1)}\big)_j^2\Big)^{1/2},$$
where $(v_h^{(1)})_j = (v_{j+1} - v_j)/h$ is the discrete derivative. This is the form in which
Remark 12.1 reads (12.14). -/
theorem lemma_12_2_discreteDeriv (N : ℕ) (v : Fin (N + 2) → ℝ) :
    FiniteDifference.discreteH1Seminorm N (meshSize N) v
      = Real.sqrt (meshSize N * ∑ j, FiniteDifference.discreteDeriv N (meshSize N) v j ^ 2) :=
  rfl

/-- **Remark 12.1** of [quarteroni2000numerical] (Poincaré inequality, (12.16)). Let $a < b$ and
$u \in H_0^1(a, b)$. Then
$$\|u\|_{L^2(a, b)} \le C_P \|u'\|_{L^2(a, b)}, \qquad C_P = \frac{b - a}{\sqrt{2}}.$$

**Generalization.** The source states the inequality for $v \in C^1([a, b])$ with
$v(a) = v(b) = 0$. Such a function lies in $H_0^1(a, b)$.
`QuarteroniSaccoSaleri.Chapter12.remark_12_1_of_eq_integral` is an elementary form that covers
these functions directly, since such a $v$ is the antiderivative $\int_a^x v'$.

$H_0^1(a, b)$ is `SobolevIntervalZero a b`, and `SobolevInterval.deriv u 0` and
`SobolevInterval.deriv u 1` are $u$ and $u'$ in $L^2(a, b)$. -/
theorem remark_12_1 {a b : ℝ} (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) :
    ‖SobolevInterval.deriv u 0‖ ≤ (b - a) / Real.sqrt 2 * ‖SobolevInterval.deriv u 1‖ :=
  SobolevIntervalZero.norm_deriv_zero_le hab hu

/-- **Remark 12.1** of [quarteroni2000numerical], (12.16) in elementary form. Let $a \le b$, and let
$w, g \in L^2(a, b)$ with $g(x) = \int_a^x w(t)\, dt$ for almost every $x \in (a, b)$. Then
$$\|g\|_{L^2(a, b)} \le \frac{b - a}{\sqrt{2}} \|w\|_{L^2(a, b)}.$$

Every $v \in C^1([a, b])$ with $v(a) = 0$ has this form, with $w = v'$. -/
theorem remark_12_1_of_eq_integral {a b : ℝ} (hab : a ≤ b)
    {w g : Lp ℝ 2 (volume.restrict (Ioo a b))}
    (hg : g =ᵐ[volume.restrict (Ioo a b)] fun x => ∫ t in a..x, w t) :
    ‖g‖ ≤ (b - a) / Real.sqrt 2 * ‖w‖ :=
  SobolevInterval.norm_le_of_eq_integral hab hg

/-! ### Stability by the energy method (12.17) -/

/-- **Equation (12.17)** of [quarteroni2000numerical] (stability estimate). Let $u_h$ be a finite
difference solution with datum $f$, and let $f_h = (f(x_0), \dots, f(x_n))$ be the grid function
of the nodal values of $f$. Then
$$\|u_h\|_h \le \frac{1}{2} \|f_h\|_h.$$
-/
theorem equation_12_17 (N : ℕ) {f : ℝ → ℝ} {u : Fin (N + 2) → ℝ}
    (hu : IsFiniteDifferenceSolution N f u) :
    FiniteDifference.discreteL2Norm N (meshSize N) u
      ≤ 1 / 2 * FiniteDifference.discreteL2Norm N (meshSize N)
        (f ∘ FiniteDifference.uniformGrid 0 1 N) := by
  have hL : FiniteDifference.discreteLaplacian N (meshSize N) u
      = FiniteDifference.interior N (f ∘ FiniteDifference.uniformGrid 0 1 N) := hu.2
  have h := (FiniteDifference.discreteL2Norm_le_of_discreteLaplacian_eq
    (meshSize_pos N) hu.1 hL).2
  rwa [succ_mul_meshSize, one_pow] at h

/-- **Section 12.2** of [quarteroni2000numerical], uniqueness of the finite difference solution, the
consequence of (12.17). If $u_h$ and $v_h$ are finite difference solutions with the same datum
$f$, then $u_h = v_h$. -/
theorem equation_12_17_unique (N : ℕ) {f : ℝ → ℝ} {u v : Fin (N + 2) → ℝ}
    (hu : IsFiniteDifferenceSolution N f u) (hv : IsFiniteDifferenceSolution N f v) : u = v :=
  eq_of_equation_12_9_eq N hu.1 hv.1 (hu.2.trans hv.2.symm)

/-! ### Consistency (12.18)–(12.22) -/

/-- The maximum norm $\|f''\|_\infty = \sup_{x \in [0, 1]} |f''(x)|$ of the second derivative of
$f \in C^2([0, 1])$. The second derivative is taken within $[0, 1]$, so that it is defined at
the endpoints too.

The supremum is `sSup` of a set of reals, which is $0$ for a set that is not bounded above. -/
noncomputable def normSecondDeriv (f : ℝ → ℝ) : ℝ :=
  sSup ((fun s => |iteratedDerivWithin 2 f (Icc 0 1) s|) '' Icc 0 1)

/-- Let $f \in C^2([0, 1])$ and $x \in (0, 1)$. Then $|f''(x)| \le \|f''\|_\infty$. -/
theorem abs_iteratedDeriv_two_le_normSecondDeriv {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : |iteratedDeriv 2 f x| ≤ normSecondDeriv f := by
  have hcont : ContinuousOn (fun s => |iteratedDerivWithin 2 f (Icc 0 1) s|) (Icc 0 1) :=
    (hf.continuousOn_iteratedDerivWithin (by norm_num) (uniqueDiffOn_Icc zero_lt_one)).abs
  have hbdd : BddAbove ((fun s => |iteratedDerivWithin 2 f (Icc 0 1) s|) '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  have heq : iteratedDeriv 2 f x = iteratedDerivWithin 2 f (Icc 0 1) x :=
    (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (hf.contDiffAt (Icc_mem_nhds hx.1 hx.2)) (Ioo_subset_Icc_self hx)).symm
  rw [heq]
  exact le_csSup hbdd (mem_image_of_mem _ (Ioo_subset_Icc_self hx))

/-- Regularity of the solution used for (12.19): if $u$ solves the boundary value problem
(12.1)–(12.2) with datum $f \in C^2([0, 1])$, then $u \in C^4([0, 1])$. -/
theorem IsSolution.contDiffOn_four {f u : ℝ → ℝ} (hu : IsSolution f u)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) : ContDiffOn ℝ 4 u (Icc 0 1) :=
  (hu.contDiffOn_of_contDiffOn (m := 2) hf).of_le (by norm_num)

/-- A solution $u$ of the boundary value problem (12.1)–(12.2) with datum $f$ has $u''(x) = -f(x)$
for $x \in (0, 1)$. -/
theorem IsSolution.iteratedDeriv_two {f u : ℝ → ℝ} (hu : IsSolution f u) :
    ∀ x ∈ Ioo (0 : ℝ) 1, iteratedDeriv 2 u x = -f x :=
  fun x hx => by rw [← hu.equation_12_1 x hx, neg_neg]

/-- **Equation (12.19)** of [quarteroni2000numerical], the truncation error in Lagrange form. Let
$f \in C^2([0, 1])$, and let $u$ solve the boundary value problem (12.1)–(12.2) with datum $f$.
Then for every $j = 1, \dots, n - 1$ there are $\xi_j \in (x_{j-1}, x_j)$ and
$\eta_j \in (x_j, x_{j+1})$ with
$$\tau_h(x_j) = -\frac{h^2}{24} \big(u''''(\xi_j) + u''''(\eta_j)\big).$$

**Typo.** The source prints the factor $+h^2/24$. Written with $u''''$ rather than with
$f'' = -u''''$, the sign is $-h^2/24$. -/
theorem equation_12_19 (N : ℕ) {f u : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hu : IsSolution f u) (j : Fin N) :
    ∃ ξ ∈ Ioo (FiniteDifference.uniformGrid 0 1 N j.castSucc.castSucc)
        (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc),
      ∃ η ∈ Ioo (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc)
        (FiniteDifference.uniformGrid 0 1 N j.succ.succ),
        FiniteDifference.truncationError 0 1 N u f j
          = -(meshSize N ^ 2 / 24) * (iteratedDeriv 4 u ξ + iteratedDeriv 4 u η) :=
  FiniteDifference.truncationError_eq_of_contDiffOn zero_lt_one (hu.contDiffOn_four hf)
    hu.iteratedDeriv_two j

/-- **Equation (12.20)** of [quarteroni2000numerical], with an explicit bound. Let
$f \in C^2([0, 1])$ with $|f''(x)| \le M$ for $x \in (0, 1)$, and let $u$ solve the boundary
value problem (12.1)–(12.2) with datum $f$. Then $|\tau_h(x_j)| \le (h^2/12) M$ for every
$j = 1, \dots, n - 1$. -/
theorem equation_12_20_of_forall_le (N : ℕ) {f u : ℝ → ℝ} {M : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) (hu : IsSolution f u)
    (hM : ∀ x ∈ Ioo (0 : ℝ) 1, |iteratedDeriv 2 f x| ≤ M) (j : Fin N) :
    |FiniteDifference.truncationError 0 1 N u f j| ≤ meshSize N ^ 2 / 12 * M :=
  FiniteDifference.abs_truncationError_le_of_contDiffOn zero_lt_one (hu.contDiffOn_four hf)
    hu.iteratedDeriv_two
    (fun x hx => by
      rw [FiniteDifference.iteratedDeriv_four_eq_neg_iteratedDeriv_two hu.iteratedDeriv_two hx,
        abs_neg]
      exact hM x hx) j

/-- **Equation (12.20)** of [quarteroni2000numerical] (consistency). Let $f \in C^2([0, 1])$, and
let $u$ solve the boundary value problem (12.1)–(12.2) with datum $f$. Then for every
$j = 1, \dots, n - 1$
$$|\tau_h(x_j)| \le \frac{h^2}{12} \|f''\|_\infty.$$
Hence $\tau_h \to 0$ as $h \to 0$, and the scheme is consistent.

The norm $\|f''\|_\infty$ is `QuarteroniSaccoSaleri.Chapter12.normSecondDeriv f`. -/
theorem equation_12_20 (N : ℕ) {f u : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hu : IsSolution f u) (j : Fin N) :
    |FiniteDifference.truncationError 0 1 N u f j| ≤ meshSize N ^ 2 / 12 * normSecondDeriv f :=
  equation_12_20_of_forall_le N hf hu
    (fun _ hx => abs_iteratedDeriv_two_le_normSecondDeriv hf hx) j

/-- **Equation (12.20)** of [quarteroni2000numerical], in the discrete maximum norm. Let
$f \in C^2([0, 1])$, and let $u$ solve the boundary value problem (12.1)–(12.2) with datum $f$.
Then $\|\tau_h\|_{h,\infty} \le h^2 \|f''\|_\infty / 12$. -/
theorem equation_12_20_norm (N : ℕ) {f u : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hu : IsSolution f u) :
    ‖FiniteDifference.truncationError 0 1 N u f‖ ≤ meshSize N ^ 2 / 12 * normSecondDeriv f :=
  FiniteDifference.norm_truncationError_le_of_contDiffOn zero_lt_one (hu.contDiffOn_four hf)
    hu.iteratedDeriv_two fun x hx ↦ by
      rw [FiniteDifference.iteratedDeriv_four_eq_neg_iteratedDeriv_two hu.iteratedDeriv_two hx,
        abs_neg]
      exact abs_iteratedDeriv_two_le_normSecondDeriv hf hx

/-- **Remark 12.2** of [quarteroni2000numerical]. Let $u \in C^3([0, 1])$ with $u'''$ Lipschitz on
$(0, 1)$ with constant $M \ge 0$, so that $u \in C^{3,1}(0, 1)$, and let $u'' = -f$ on $(0, 1)$.
Then for every $j = 1, \dots, n - 1$
$$|\tau_h(x_j)| \le \frac{M h^2}{12}.$$

**Generalization.** The source gives the bound $M h^2$. The bound proved here is smaller by the
factor $12$.

The function $u$ need not satisfy the boundary conditions. -/
theorem remark_12_2 (N : ℕ) {f u : ℝ → ℝ} {M : NNReal} (hu : ContDiffOn ℝ 3 u (Icc 0 1))
    (hM : LipschitzOnWith M (iteratedDeriv 3 u) (Ioo 0 1))
    (hu'' : ∀ x ∈ Ioo (0 : ℝ) 1, iteratedDeriv 2 u x = -f x) (j : Fin N) :
    |FiniteDifference.truncationError 0 1 N u f j| ≤ (M : ℝ) * meshSize N ^ 2 / 12 :=
  FiniteDifference.abs_truncationError_le_of_lipschitzOnWith zero_lt_one hu hM hu'' j

/-- **Remark 12.3** of [quarteroni2000numerical], the error equation (12.22). Let
$u : \mathbb{R} \to \mathbb{R}$, and let $u_h$ be a finite difference solution with datum $f$.
Then the discretization error $e = u - u_h$ at the nodes satisfies
$$L_h e = L_h u - f_h = \tau_h.$$

The function $u$ can be any function; $\tau_h$ is its truncation error (12.18). -/
theorem remark_12_3 (N : ℕ) {f : ℝ → ℝ} (u : ℝ → ℝ) {uh : Fin (N + 2) → ℝ}
    (hu : IsFiniteDifferenceSolution N f uh) :
    equation_12_9 N (u ∘ FiniteDifference.uniformGrid 0 1 N - uh)
      = FiniteDifference.truncationError 0 1 N u f :=
  FiniteDifference.error_eq_of_discreteLaplacian_eq u f hu.2

/-! ### Exercise 12.5, the bound (12.23) on the truncation error in the norm $\|\cdot\|_h$ -/

section Exercise125

open intervalIntegral

/-- The Cauchy–Schwarz inequality for interval integrals, used in Exercise 12.5. Let $p \le q$, and
let $f$ and $k$ be continuous on $[p, q]$. Then
$$\Big(\int_p^q f(t) k(t)\, dt\Big)^2 \le \int_p^q f(t)^2\, dt \int_p^q k(t)^2\, dt.$$

The proof specializes `intervalIntegral.sq_integral_mul_le_of_continuousOn`. -/
theorem sq_integral_mul_le {f k : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hf : ContinuousOn f (Icc p q)) (hk : ContinuousOn k (Icc p q)) :
    (∫ t in p..q, f t * k t) ^ 2 ≤ (∫ t in p..q, f t ^ 2) * ∫ t in p..q, k t ^ 2 :=
  intervalIntegral.sq_integral_mul_le_of_continuousOn hpq hf hk

/-- Taylor's formula with integral remainder at the right end, used in Exercise 12.5. Let $p \le q$,
let $u$, $u_1$ and $u_2$ be continuous on $[p, q]$, and let $u' = u_1$ and $u_1' = u_2$ on
$(p, q)$. Then
$$\int_p^q u_2(t) (q - t)\, dt = u(q) - u(p) - (q - p) u_1(p).$$

Only differentiability in the open interval is assumed, so the formula applies on a subinterval
that touches an endpoint of $[0, 1]$. -/
theorem integral_mul_sub_right {u u₁ u₂ : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hu : ContinuousOn u (Icc p q)) (hu₁ : ContinuousOn u₁ (Icc p q))
    (hu₂ : ContinuousOn u₂ (Icc p q))
    (hd1 : ∀ t ∈ Ioo p q, HasDerivAt u (u₁ t) t)
    (hd2 : ∀ t ∈ Ioo p q, HasDerivAt u₁ (u₂ t) t) :
    (∫ t in p..q, u₂ t * (q - t)) = u q - u p - (q - p) * u₁ p := by
  have hF : ContinuousOn (fun t => u₁ t * (q - t) + u t) (Icc p q) :=
    (hu₁.mul (continuousOn_const.sub continuousOn_id)).add hu
  have hderiv : ∀ t ∈ Ioo p q,
      HasDerivAt (fun s => u₁ s * (q - s) + u s) (u₂ t * (q - t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => q - s) (-1 : ℝ) t := by
      simpa using (hasDerivAt_id t).const_sub q
    have he : u₂ t * (q - t) = u₂ t * (q - t) + u₁ t * (-1) + u₁ t := by ring
    rw [he]
    exact ((hd2 t ht).mul h1).add (hd1 t ht)
  have hint : IntervalIntegrable (fun t => u₂ t * (q - t)) volume p q :=
    (hu₂.mul (continuousOn_const.sub continuousOn_id)).intervalIntegrable_of_Icc hpq
  rw [integral_eq_sub_of_hasDerivAt_of_le hpq hF hderiv hint]
  ring


/-- Taylor's formula with integral remainder at the left end, used in Exercise 12.5. Let $p \le q$,
let $u$, $u_1$ and $u_2$ be continuous on $[p, q]$, and let $u' = u_1$ and $u_1' = u_2$ on
$(p, q)$. Then
$$\int_p^q u_2(t) (t - p)\, dt = u(p) - u(q) + (q - p) u_1(q).$$
-/
theorem integral_mul_sub_left {u u₁ u₂ : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hu : ContinuousOn u (Icc p q)) (hu₁ : ContinuousOn u₁ (Icc p q))
    (hu₂ : ContinuousOn u₂ (Icc p q))
    (hd1 : ∀ t ∈ Ioo p q, HasDerivAt u (u₁ t) t)
    (hd2 : ∀ t ∈ Ioo p q, HasDerivAt u₁ (u₂ t) t) :
    (∫ t in p..q, u₂ t * (t - p)) = u p - u q + (q - p) * u₁ q := by
  have hG : ContinuousOn (fun t => u₁ t * (t - p) - u t) (Icc p q) :=
    (hu₁.mul (continuousOn_id.sub continuousOn_const)).sub hu
  have hderiv : ∀ t ∈ Ioo p q,
      HasDerivAt (fun s => u₁ s * (s - p) - u s) (u₂ t * (t - p)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => s - p) (1 : ℝ) t := by
      simpa using (hasDerivAt_id t).sub_const p
    have he : u₂ t * (t - p) = u₂ t * (t - p) + u₁ t * 1 - u₁ t := by ring
    rw [he]
    exact ((hd2 t ht).mul h1).sub (hd1 t ht)
  have hint : IntervalIntegrable (fun t => u₂ t * (t - p)) volume p q :=
    (hu₂.mul (continuousOn_id.sub continuousOn_const)).intervalIntegrable_of_Icc hpq
  rw [integral_eq_sub_of_hasDerivAt_of_le hpq hG hderiv hint]
  ring

/-- The square of the right Taylor kernel integrates to $h^3/3$: for $h \ge 0$,
$\int_x^{x+h} (x + h - t)^2\, dt = h^3/3$. -/
theorem integral_kernel_sq_right {x h : ℝ} (hh : 0 ≤ h) :
    (∫ t in x..(x + h), (x + h - t) ^ 2) = h ^ 3 / 3 := by
  have hle : x ≤ x + h := by linarith
  have hderiv : ∀ t ∈ Ioo x (x + h),
      HasDerivAt (fun s => -(x + h - s) ^ 3 / 3) ((x + h - t) ^ 2) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => x + h - s) (-1 : ℝ) t := by
      simpa using (hasDerivAt_id t).const_sub (x + h)
    have h2 := ((h1.pow 3).neg.div_const 3)
    have he : (x + h - t) ^ 2 = -((3 : ℕ) * (x + h - t) ^ (3 - 1) * (-1)) / 3 := by
      push_cast
      ring
    rw [he]
    exact h2
  have hcont : ContinuousOn (fun s : ℝ => -(x + h - s) ^ 3 / 3) (Icc x (x + h)) :=
    (((continuousOn_const.sub continuousOn_id).pow 3).neg.div_const 3)
  have hint : IntervalIntegrable (fun t => (x + h - t) ^ 2) volume x (x + h) :=
    (((continuousOn_const.sub continuousOn_id).pow 2)).intervalIntegrable_of_Icc hle
  rw [integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint]
  ring

/-- The square of the left Taylor kernel integrates to $h^3/3$: for $h \ge 0$,
$\int_{x-h}^x (t - (x - h))^2\, dt = h^3/3$. -/
theorem integral_kernel_sq_left {x h : ℝ} (hh : 0 ≤ h) :
    (∫ t in (x - h)..x, (t - (x - h)) ^ 2) = h ^ 3 / 3 := by
  have hle : x - h ≤ x := by linarith
  have hderiv : ∀ t ∈ Ioo (x - h) x,
      HasDerivAt (fun s => (s - (x - h)) ^ 3 / 3) ((t - (x - h)) ^ 2) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s - (x - h)) (1 : ℝ) t := by
      simpa using (hasDerivAt_id t).sub_const (x - h)
    have h2 := (h1.pow 3).div_const 3
    have he : (t - (x - h)) ^ 2 = ((3 : ℕ) * (t - (x - h)) ^ (3 - 1) * 1) / 3 := by
      push_cast
      ring
    rw [he]
    exact h2
  have hcont : ContinuousOn (fun s : ℝ => (s - (x - h)) ^ 3 / 3) (Icc (x - h) x) :=
    (((continuousOn_id.sub continuousOn_const).pow 3).div_const 3)
  have hint : IntervalIntegrable (fun t => (t - (x - h)) ^ 2) volume (x - h) x :=
    (((continuousOn_id.sub continuousOn_const).pow 2)).intervalIntegrable_of_Icc hle
  rw [integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint]
  ring


/-- The second difference of (12.21) in terms of the datum, used in Exercise 12.5. Let
$f \in C^0([0, 1])$, let $u$ solve the boundary value problem (12.1)–(12.2) with datum $f$, and
let $h > 0$ and $x$ satisfy $0 \le x - h$ and $x + h \le 1$. Then
$$u(x + h) - 2u(x) + u(x - h) = -\Big(\int_x^{x+h} f(t) (x + h - t)\, dt + \int_{x-h}^x f(t)
  (t - x + h)\, dt\Big).$$

The two integrals are the Taylor remainders of $u'' = -f$. -/
theorem secondDiff_eq_integral {f u : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hu : IsSolution f u) {x h : ℝ} (hh : 0 < h) (hx0 : 0 ≤ x - h) (hx1 : x + h ≤ 1) :
    u (x + h) - 2 * u x + u (x - h)
      = -((∫ t in x..(x + h), f t * (x + h - t))
          + ∫ t in (x - h)..x, f t * (t - (x - h))) := by
  set u₁ := derivWithin u (Icc (0 : ℝ) 1) with hu₁def
  have hcu : ContinuousOn u (Icc (0 : ℝ) 1) := hu.contDiffOn.continuousOn
  have hcu1 : ContinuousOn u₁ (Icc (0 : ℝ) 1) :=
    hu.contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) (by norm_num)
  have hcf : ContinuousOn (fun t => -f t) (Icc (0 : ℝ) 1) := hf.neg
  have hd1 : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt u (u₁ t) t := fun t ht =>
    (hasDerivAt_of_contDiffOn_two hu.contDiffOn ht).1
  have hd2 : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt u₁ (-f t) t := by
    intro t ht
    have h2 := (hasDerivAt_of_contDiffOn_two hu.contDiffOn ht).2
    have he : iteratedDeriv 2 u t = -f t := by rw [← hu.equation_12_1 t ht]; ring
    rwa [he] at h2
  have hxpos : 0 < x := lt_of_lt_of_le hh (by linarith)
  have hsubR : Icc x (x + h) ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (by linarith) hx1
  have hsubL : Icc (x - h) x ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx0 (by linarith)
  have hoR : Ioo x (x + h) ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hoL : Ioo (x - h) x ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hR := integral_mul_sub_right (u := u) (u₁ := u₁) (u₂ := fun t => -f t)
    (by linarith : x ≤ x + h) (hcu.mono hsubR) (hcu1.mono hsubR) (hcf.mono hsubR)
    (fun t ht => hd1 t (hoR ht)) (fun t ht => hd2 t (hoR ht))
  have hL := integral_mul_sub_left (u := u) (u₁ := u₁) (u₂ := fun t => -f t)
    (by linarith : x - h ≤ x) (hcu.mono hsubL) (hcu1.mono hsubL) (hcf.mono hsubL)
    (fun t ht => hd1 t (hoL ht)) (fun t ht => hd2 t (hoL ht))
  have eR : (∫ t in x..(x + h), -f t * (x + h - t))
      = -∫ t in x..(x + h), f t * (x + h - t) := by
    rw [← intervalIntegral.integral_neg]
    exact integral_congr fun t _ => by ring
  have eL : (∫ t in (x - h)..x, -f t * (t - (x - h)))
      = -∫ t in (x - h)..x, f t * (t - (x - h)) := by
    rw [← intervalIntegral.integral_neg]
    exact integral_congr fun t _ => by ring
  rw [eR] at hR
  rw [eL] at hL
  have hxx : x - (x - h) = h := by ring
  rw [hxx] at hL
  have hxx2 : x + h - x = h := by ring
  rw [hxx2] at hR
  linarith


/-- The estimate at one node behind the bound (12.23) of Exercise 12.5. Let $f \in C^0([0, 1])$, let
$u$ solve the boundary value problem (12.1)–(12.2) with datum $f$, and let $h > 0$ and $x$
satisfy $0 \le x - h$ and $x + h \le 1$. Let $\tau = -(u(x + h) - 2u(x) + u(x - h))/h^2 - f(x)$.
Then
$$h \tau^2 \le \int_{x-h}^{x+h} f(t)^2\, dt + 3h f(x)^2.$$

The three terms of $\tau = h^{-2}(I^+ + I^-) - f(x)$ are squared with
$(a + b + c)^2 \le 3(a^2 + b^2 + c^2)$, and the two integrals are bounded by the Cauchy–Schwarz
inequality against the kernels, whose squares integrate to $h^3/3$. -/
theorem node_bound {f u : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) (hu : IsSolution f u)
    {x h : ℝ} (hh : 0 < h) (hx0 : 0 ≤ x - h) (hx1 : x + h ≤ 1) :
    h * (-(u (x + h) - 2 * u x + u (x - h)) / h ^ 2 - f x) ^ 2
      ≤ (∫ t in (x - h)..(x + h), f t ^ 2) + 3 * h * f x ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le hh (by linarith)
  have hsubR : Icc x (x + h) ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (by linarith) hx1
  have hsubL : Icc (x - h) x ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx0 (by linarith)
  set A := ∫ t in x..(x + h), f t * (x + h - t) with hA
  set B := ∫ t in (x - h)..x, f t * (t - (x - h)) with hB
  set FR := ∫ t in x..(x + h), f t ^ 2 with hFR
  set FL := ∫ t in (x - h)..x, f t ^ 2 with hFL
  have hid := secondDiff_eq_integral hf hu hh hx0 hx1
  have hA2 : A ^ 2 ≤ FR * (h ^ 3 / 3) := by
    have hcs := sq_integral_mul_le (k := fun t => x + h - t) (by linarith : x ≤ x + h)
      (hf.mono hsubR) ((continuous_const.sub continuous_id).continuousOn)
    rw [integral_kernel_sq_right hh.le] at hcs
    exact hcs
  have hB2 : B ^ 2 ≤ FL * (h ^ 3 / 3) := by
    have hcs := sq_integral_mul_le (k := fun t => t - (x - h)) (by linarith : x - h ≤ x)
      (hf.mono hsubL) ((continuous_id.sub continuous_const).continuousOn)
    rw [integral_kernel_sq_left hh.le] at hcs
    exact hcs
  have hadj : FL + FR = ∫ t in (x - h)..(x + h), f t ^ 2 := by
    rw [hFL, hFR]
    exact integral_add_adjacent_intervals
      ((hf.mono hsubL).pow 2 |>.intervalIntegrable_of_Icc (by linarith))
      ((hf.mono hsubR).pow 2 |>.intervalIntegrable_of_Icc (by linarith))
  have hexpr : -(u (x + h) - 2 * u x + u (x - h)) / h ^ 2 - f x = (A + B) / h ^ 2 - f x := by
    rw [hid]
    ring
  rw [hexpr, ← hadj]
  have hh3 : (0 : ℝ) < h ^ 3 := by positivity
  have hrw : h * ((A + B) / h ^ 2 - f x) ^ 2 = (A + B - f x * h ^ 2) ^ 2 / h ^ 3 := by
    field_simp
  rw [hrw, div_le_iff₀ hh3]
  nlinarith [sq_nonneg (A - B), sq_nonneg (A + f x * h ^ 2), sq_nonneg (B + f x * h ^ 2),
    hA2, hB2, hh.le, sq_nonneg h, hh3]


/-- The nodes of the uniform grid of $[0, 1]$ are $x_j = jh$. -/
theorem grid_eq_mul (N : ℕ) (j : Fin (N + 2)) :
    uniformGrid 0 1 N j = (j : ℕ) * meshSize N := by
  rw [uniformGrid_apply, meshSize_def, zero_add]

/-- The count of subintervals, used in Exercise 12.5. Let $f \in C^0([0, 1])$. Then
$$\sum_{j=1}^{n-1} \int_{x_{j-1}}^{x_{j+1}} f(t)^2\, dt \le 2 \int_0^1 f(t)^2\, dt.$$

Each double subinterval $[x_{j-1}, x_{j+1}]$ covers two of the $n$ subintervals, and each
subinterval is covered at most twice. -/
theorem sum_panel_le (N : ℕ) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    ∑ i : Fin N, (∫ t in (uniformGrid 0 1 N i.castSucc.castSucc)..
        (uniformGrid 0 1 N i.succ.succ), f t ^ 2)
      ≤ 2 * ∫ t in (0 : ℝ)..1, f t ^ 2 := by
  have hh : 0 < meshSize N := by
    rw [meshSize_eq]
    positivity
  set a : ℕ → ℝ := fun k => (k : ℝ) * meshSize N with ha
  have hamono : ∀ k l : ℕ, k ≤ l → a k ≤ a l := by
    intro k l hkl
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) hh.le
  have ha0 : a 0 = 0 := by simp [ha]
  have haN : a (N + 1) = 1 := by
    rw [ha, meshSize_eq]
    push_cast
    field_simp
  have hasub : ∀ k, k ≤ N → Icc (a k) (a (k + 1)) ⊆ Icc (0 : ℝ) 1 := by
    intro k hk
    refine Icc_subset_Icc ?_ ?_
    · rw [← ha0]; exact hamono 0 k (Nat.zero_le k)
    · rw [← haN]; exact hamono (k + 1) (N + 1) (by omega)
  set Q : ℕ → ℝ := fun k => ∫ t in (a k)..(a (k + 1)), f t ^ 2 with hQ
  have hQint : ∀ k, k ≤ N → IntervalIntegrable (fun t => f t ^ 2) volume (a k) (a (k + 1)) :=
    fun k hk => ((hf.mono (hasub k hk)).pow 2).intervalIntegrable_of_Icc
      (hamono k (k + 1) (by omega))
  have hQnn : ∀ k, 0 ≤ Q k := fun k =>
    integral_nonneg (hamono k (k + 1) (by omega)) fun t _ => sq_nonneg _
  have hQsum : ∑ k ∈ Finset.range (N + 1), Q k = ∫ t in (0 : ℝ)..1, f t ^ 2 := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hQint k (by omega)),
      ha0, haN]
  have hgrid : ∀ j : Fin (N + 2), uniformGrid 0 1 N j = a (j : ℕ) := fun j => grid_eq_mul N j
  have hP : ∀ j : Fin (N + 1),
      (∫ t in (uniformGrid 0 1 N j.castSucc)..(uniformGrid 0 1 N j.succ), f t ^ 2)
        = Q (j : ℕ) := by
    intro j
    rw [hQ, grid_eq_mul, grid_eq_mul]
    norm_num [ha, Fin.val_succ]
  have hsplit : ∀ i : Fin N,
      (∫ t in (uniformGrid 0 1 N i.castSucc.castSucc)..(uniformGrid 0 1 N i.succ.succ), f t ^ 2)
        = Q (i.castSucc : ℕ) + Q (i.succ : ℕ) := by
    intro i
    have e1 := (hP i.castSucc).symm
    have e2 := (hP i.succ).symm
    rw [e1, e2, ← Fin.succ_castSucc]
    refine (integral_add_adjacent_intervals ?_ ?_).symm
    · rw [hgrid, hgrid]
      exact hQint (i : ℕ) i.isLt.le
    · rw [hgrid, hgrid]
      exact hQint ((i : ℕ) + 1) i.isLt
  have hcast : ∑ i : Fin N, Q (i.castSucc : ℕ) ≤ ∑ k ∈ Finset.range (N + 1), Q k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => Q k) (N + 1), Fin.sum_univ_castSucc]
    linarith [hQnn ((Fin.last N : Fin (N + 1)) : ℕ)]
  have hsucc : ∑ i : Fin N, Q (i.succ : ℕ) ≤ ∑ k ∈ Finset.range (N + 1), Q k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => Q k) (N + 1), Fin.sum_univ_succ]
    linarith [hQnn ((0 : Fin (N + 1)) : ℕ)]
  calc ∑ i : Fin N, (∫ t in (uniformGrid 0 1 N i.castSucc.castSucc)..
          (uniformGrid 0 1 N i.succ.succ), f t ^ 2)
      = ∑ i : Fin N, (Q (i.castSucc : ℕ) + Q (i.succ : ℕ)) :=
        Finset.sum_congr rfl fun i _ => hsplit i
    _ = (∑ i : Fin N, Q (i.castSucc : ℕ)) + ∑ i : Fin N, Q (i.succ : ℕ) := Finset.sum_add_distrib
    _ ≤ (∑ k ∈ Finset.range (N + 1), Q k) + ∑ k ∈ Finset.range (N + 1), Q k :=
        add_le_add hcast hsucc
    _ = 2 * ∫ t in (0 : ℝ)..1, f t ^ 2 := by rw [hQsum]; ring


/-- The interior part of the trapezoidal sum is at most the whole sum: for every $h \ge 0$ and every
grid function $w$,
$$h \sum_{j=1}^{n-1} w_j^2 \le (w, w)_h,$$
because the two endpoint terms of the trapezoidal weights are nonnegative. -/
theorem sum_interior_le_discreteInner (N : ℕ) {h : ℝ} (hh : 0 ≤ h) (w : Fin (N + 2) → ℝ) :
    h * ∑ i : Fin N, w i.succ.castSucc ^ 2 ≤ FiniteDifference.discreteInner N h w w := by
  have hsum : ∑ k : Fin (N + 2), FiniteDifference.gridWeight N k * w k * w k
      = FiniteDifference.gridWeight N 0 * w 0 * w 0
        + ((∑ i : Fin N, FiniteDifference.gridWeight N i.castSucc.succ * w i.castSucc.succ
              * w i.castSucc.succ)
          + FiniteDifference.gridWeight N (Fin.last N).succ * w (Fin.last N).succ
              * w (Fin.last N).succ) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hmid : ∀ i : Fin N, FiniteDifference.gridWeight N i.castSucc.succ * w i.castSucc.succ
      * w i.castSucc.succ = w i.succ.castSucc ^ 2 := by
    intro i
    rw [Fin.succ_castSucc, FiniteDifference.gridWeight_succ_castSucc]
    ring
  have h0 : 0 ≤ FiniteDifference.gridWeight N 0 * w 0 * w 0 := by
    have := FiniteDifference.gridWeight_nonneg (n := N) 0
    nlinarith [sq_nonneg (w 0)]
  have hl : 0 ≤ FiniteDifference.gridWeight N (Fin.last N).succ * w (Fin.last N).succ
      * w (Fin.last N).succ := by
    have := FiniteDifference.gridWeight_nonneg (n := N) (Fin.last N).succ
    nlinarith [sq_nonneg (w (Fin.last N).succ)]
  rw [FiniteDifference.discreteInner, hsum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    hmid i]
  nlinarith [h0, hl, hh]

/-- **Exercise 12.5** of [quarteroni2000numerical], the bound (12.23) of Remark 12.3. Let
$f \in C^0([0, 1])$, and let $u$ solve the boundary value problem (12.1)–(12.2) with datum $f$.
Then
$$\|\tau_h\|_h^2 \le 3 \big(\|f_h\|_h^2 + \|f\|_{L^2(0, 1)}^2\big),$$
where $f_h = (f(x_0), \dots, f(x_n))$ and $\tau_h$ is extended by zero at $x_0$ and $x_n$. So
the discrete second derivative of the discretization error stays bounded as $h \to 0$ whenever
the two norms of $f$ on the right do.

**Generalization.** The source assumes $f \in C^2([0, 1])$, which its route to $u \in C^4$
needs. Continuity of $f$ is enough here.

The proof makes the hint of the source precise; the printed hint omits the factors $h^{-2}$ and
$1/2$. It integrates (12.21) by parts twice on each side, to write $\tau_h(x_j)$ as $-f(x_j)$
plus $h^{-2}$ times the integrals of $f$ against the kernels $x_j + h - t$ and $t - x_j + h$. It
squares with $(a + b + c)^2 \le 3(a^2 + b^2 + c^2)$, bounds each integral by the Cauchy–Schwarz
inequality, and sums over the nodes, where each subinterval is counted at most twice. The norm
$\|f\|_{L^2(0,1)}^2$ is the integral $\int_0^1 f^2$. -/
theorem exercise_12_5 (N : ℕ) {f u : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hu : IsSolution f u) :
    FiniteDifference.discreteL2Norm N (meshSize N)
        (FiniteDifference.ofInterior N (FiniteDifference.truncationError 0 1 N u f)) ^ 2
      ≤ 3 * (FiniteDifference.discreteL2Norm N (meshSize N)
            (f ∘ FiniteDifference.uniformGrid 0 1 N) ^ 2 + ∫ t in (0 : ℝ)..1, f t ^ 2) := by
  set h := meshSize N with hdef
  have hh : 0 < h := by rw [hdef, meshSize_eq]; positivity
  set τ := FiniteDifference.truncationError 0 1 N u f with hτ
  -- the left-hand side is `h ∑ τ_i²`
  have hlhs : FiniteDifference.discreteL2Norm N h (FiniteDifference.ofInterior N τ) ^ 2
      = h * ∑ i : Fin N, τ i ^ 2 := by
    rw [FiniteDifference.discreteL2Norm_sq hh.le,
      FiniteDifference.discreteInner_ofInterior h τ (FiniteDifference.ofInterior_mem_gridZero τ),
      FiniteDifference.interior_ofInterior]
    exact congrArg (h * ·) (Finset.sum_congr rfl fun i _ => (sq (τ i)).symm)
  -- the node estimate
  have hnode : ∀ i : Fin N, h * τ i ^ 2
      ≤ (∫ t in (FiniteDifference.uniformGrid 0 1 N i.castSucc.castSucc)..
          (FiniteDifference.uniformGrid 0 1 N i.succ.succ), f t ^ 2)
        + 3 * h * f (FiniteDifference.uniformGrid 0 1 N i.succ.castSucc) ^ 2 := by
    intro i
    set x := FiniteDifference.uniformGrid 0 1 N i.succ.castSucc with hx
    have hxp : FiniteDifference.uniformGrid 0 1 N i.succ.succ = x + h := by
      rw [hx, hdef, meshSize_def]
      exact FiniteDifference.uniformGrid_succ i.succ
    have hxm : FiniteDifference.uniformGrid 0 1 N i.castSucc.castSucc = x - h := by
      have e := FiniteDifference.uniformGrid_succ (a := 0) (b := 1) i.castSucc
      rw [Fin.succ_castSucc] at e
      rw [hx, hdef, meshSize_def, e]
      ring
    have hx0 : 0 ≤ x - h := by
      rw [← hxm]
      exact (FiniteDifference.uniformGrid_mem_Icc zero_le_one _).1
    have hx1 : x + h ≤ 1 := by
      rw [← hxp]
      exact (FiniteDifference.uniformGrid_mem_Icc zero_le_one _).2
    have hτi : τ i = -(u (x + h) - 2 * u x + u (x - h)) / h ^ 2 - f x := by
      rw [hτ, FiniteDifference.truncationError_apply, FiniteDifference.discreteLaplacian_apply]
      simp only [Function.comp_apply]
      rw [show FiniteDifference.gridStep 0 1 N = h from by rw [hdef, meshSize_def], hxp, hxm,
        ← hx]
    rw [hτi, hxp, hxm]
    exact node_bound hf hu hh hx0 hx1
  calc FiniteDifference.discreteL2Norm N h (FiniteDifference.ofInterior N τ) ^ 2
      = ∑ i : Fin N, h * τ i ^ 2 := by rw [hlhs, Finset.mul_sum]
    _ ≤ ∑ i : Fin N, ((∫ t in (FiniteDifference.uniformGrid 0 1 N i.castSucc.castSucc)..
          (FiniteDifference.uniformGrid 0 1 N i.succ.succ), f t ^ 2)
        + 3 * h * f (FiniteDifference.uniformGrid 0 1 N i.succ.castSucc) ^ 2) :=
        Finset.sum_le_sum fun i _ => hnode i
    _ = (∑ i : Fin N, ∫ t in (FiniteDifference.uniformGrid 0 1 N i.castSucc.castSucc)..
          (FiniteDifference.uniformGrid 0 1 N i.succ.succ), f t ^ 2)
        + 3 * (h * ∑ i : Fin N,
            f (FiniteDifference.uniformGrid 0 1 N i.succ.castSucc) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        refine congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
    _ ≤ 2 * (∫ t in (0 : ℝ)..1, f t ^ 2)
        + 3 * FiniteDifference.discreteInner N h (f ∘ FiniteDifference.uniformGrid 0 1 N)
            (f ∘ FiniteDifference.uniformGrid 0 1 N) := by
        have h1 := sum_panel_le N hf
        have h2 := sum_interior_le_discreteInner N hh.le (f ∘ FiniteDifference.uniformGrid 0 1 N)
        simp only [Function.comp_apply] at h2
        linarith
    _ ≤ 3 * (FiniteDifference.discreteL2Norm N h (f ∘ FiniteDifference.uniformGrid 0 1 N) ^ 2
          + ∫ t in (0 : ℝ)..1, f t ^ 2) := by
        rw [FiniteDifference.discreteL2Norm_sq hh.le]
        have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, f t ^ 2 :=
          integral_nonneg zero_le_one fun t _ => sq_nonneg _
        linarith

end Exercise125

/-! ### The discrete Green's function (12.24)–(12.26) -/

/-- The determinant of $A_{fd}$ is not zero. -/
theorem isUnit_det_finiteDifferenceMatrix (N : ℕ) : IsUnit (finiteDifferenceMatrix N).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (exercise_12_2 N).isUnit

/-- The inverse of $A_{fd}$ is $h^2$ times the inverse of $\operatorname{tridiag}(-1, 2, -1)$. -/
theorem inv_finiteDifferenceMatrix (N : ℕ) :
    (finiteDifferenceMatrix N)⁻¹
      = meshSize N ^ 2 • (Matrix.symmTridiagonalToeplitz N (-1) 2)⁻¹ := by
  have hT : IsUnit (Matrix.symmTridiagonalToeplitz N (-1) 2).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_symmTridiagonalToeplitz_neg_one_two N)
  refine Matrix.inv_eq_right_inv ?_
  rw [finiteDifferenceMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_nonsing_inv _ hT, inv_mul_cancel₀ (pow_pos (meshSize_pos N) 2).ne', one_smul]

/-- **Equation (12.24)** of [quarteroni2000numerical]. For $k = 1, \dots, n - 1$, the **discrete
Green's function** $G^k$ is the grid function in $V_h^0$ with $L_h G^k = e^k$, where $e^k$ is
the $k$-th unit vector on the interior nodes. It is the $k$-th column of $A_{fd}^{-1}$, extended
by zero at $x_0$ and $x_n$. -/
noncomputable def discreteGreen (N : ℕ) (k : Fin N) : Fin (N + 2) → ℝ :=
  FiniteDifference.ofInterior N fun j => (finiteDifferenceMatrix N)⁻¹ j k

/-- The discrete Green's function $G^k$ lies in $V_h^0$. -/
theorem discreteGreen_mem_gridZero (N : ℕ) (k : Fin N) :
    discreteGreen N k ∈ FiniteDifference.gridZero N :=
  FiniteDifference.ofInterior_mem_gridZero _

/-- **Equation (12.25)** of [quarteroni2000numerical]. The **discrete solution operator** maps a
function $g$ on the interior nodes to the grid function
$$T_h g = \sum_{k=1}^{n-1} g(x_k) G^k.$$
-/
noncomputable def discreteSolutionOperator (N : ℕ) (g : Fin N → ℝ) : Fin (N + 2) → ℝ :=
  ∑ k, g k • discreteGreen N k

/-- The discrete solution operator applies $A_{fd}^{-1}$: $T_h g$ is $A_{fd}^{-1} g$ extended by
zero at $x_0$ and $x_n$. -/
theorem discreteSolutionOperator_eq (N : ℕ) (g : Fin N → ℝ) :
    discreteSolutionOperator N g
      = FiniteDifference.ofInterior N ((finiteDifferenceMatrix N)⁻¹ *ᵥ g) := by
  have h : discreteSolutionOperator N g
      = FiniteDifference.ofInterior N
        (∑ k, g k • fun j => (finiteDifferenceMatrix N)⁻¹ j k) := by
    rw [map_sum, discreteSolutionOperator]
    exact Finset.sum_congr rfl fun k _ => (map_smul _ _ _).symm
  rw [h]
  congr 1
  funext j
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- The discrete solution operator takes values in $V_h^0$. -/
theorem discreteSolutionOperator_mem_gridZero (N : ℕ) (g : Fin N → ℝ) :
    discreteSolutionOperator N g ∈ FiniteDifference.gridZero N := by
  rw [discreteSolutionOperator_eq]
  exact FiniteDifference.ofInterior_mem_gridZero _

/-- **Equation (12.25)** of [quarteroni2000numerical]. The operator $T_h$ inverts $L_h$: for every
function $g$ on the interior nodes, $L_h (T_h g) = g$. -/
theorem equation_12_25 (N : ℕ) (g : Fin N → ℝ) :
    equation_12_9 N (discreteSolutionOperator N g) = g := by
  have h1 : equation_12_9 N (discreteSolutionOperator N g)
      = finiteDifferenceMatrix N *ᵥ ((finiteDifferenceMatrix N)⁻¹ *ᵥ g) := by
    rw [discreteSolutionOperator_eq, equation_12_9,
      FiniteDifference.discreteLaplacian_eq_mulVec _ (FiniteDifference.ofInterior_mem_gridZero _),
      FiniteDifference.interior_ofInterior, finiteDifferenceMatrix, Matrix.smul_mulVec]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_finiteDifferenceMatrix N),
    Matrix.one_mulVec]

/-- **Equation (12.26)** of [quarteroni2000numerical]. If $u_h$ is a finite difference solution with
datum $f$, then $u_h = T_h f$, with $f$ evaluated at the interior nodes. -/
theorem equation_12_26 (N : ℕ) {f : ℝ → ℝ} {u : Fin (N + 2) → ℝ}
    (hu : IsFiniteDifferenceSolution N f u) :
    u = discreteSolutionOperator N
      fun k => f (FiniteDifference.uniformGrid 0 1 N k.succ.castSucc) :=
  eq_of_equation_12_9_eq N hu.1 (discreteSolutionOperator_mem_gridZero N _)
    (by rw [equation_12_25]; exact hu.2)

/-- **Exercise 12.6** of [quarteroni2000numerical], used in Section 12.2.2. For
$j, k = 1, \dots, n - 1$,
$$G^k(x_j) = h \, G(x_j, x_k),$$
where $G$ is the Green's function (12.4) of Section 12.1. -/
theorem exercise_12_6 (N : ℕ) (j k : Fin N) :
    discreteGreen N k j.succ.castSucc
      = meshSize N * greenFunction (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc)
        (FiniteDifference.uniformGrid 0 1 N k.succ.castSucc) := by
  have hpos := meshSize_pos N
  have hh : meshSize N = 1 / ((N : ℝ) + 1) := meshSize_eq N
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hxj := uniformGrid_interior_eq N j
  have hxk := uniformGrid_interior_eq N k
  rw [discreteGreen, FiniteDifference.ofInterior_succ_castSucc, inv_finiteDifferenceMatrix,
    Matrix.smul_apply, smul_eq_mul, Matrix.inv_symmTridiagonalToeplitz_neg_one_two_apply]
  rcases le_total (k : ℕ) (j : ℕ) with hjk | hjk
  · have hle : FiniteDifference.uniformGrid 0 1 N k.succ.castSucc
        ≤ FiniteDifference.uniformGrid 0 1 N j.succ.castSucc := by
      rw [hxj, hxk]
      have : ((k : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hjk
      nlinarith
    rw [greenFunction_of_le hle, hxj, hxk, min_eq_right hjk, max_eq_left hjk, hh]
    field_simp
    ring
  · have hle : FiniteDifference.uniformGrid 0 1 N j.succ.castSucc
        ≤ FiniteDifference.uniformGrid 0 1 N k.succ.castSucc := by
      rw [hxj, hxk]
      have : ((j : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hjk
      nlinarith
    rw [greenFunction_of_ge hle, hxj, hxk, min_eq_left hjk, max_eq_right hjk, hh]
    field_simp
    ring

/-- **Exercise 12.7** of [quarteroni2000numerical], used in the proof of Theorem 12.1. For the
constant function $1$ on the interior nodes,
$$(T_h 1)(x_j) = \frac{x_j (1 - x_j)}{2}, \qquad j = 0, \dots, n.$$
-/
theorem exercise_12_7 (N : ℕ) :
    discreteSolutionOperator N 1
      = fun j => FiniteDifference.uniformGrid 0 1 N j
        * (1 - FiniteDifference.uniformGrid 0 1 N j) / 2 := by
  have hpar : (fun j : Fin (N + 2) => FiniteDifference.uniformGrid 0 1 N j
      * (1 - FiniteDifference.uniformGrid 0 1 N j) / 2)
      = fun j => (FiniteDifference.uniformGrid 0 1 N j - 0)
        * (1 - FiniteDifference.uniformGrid 0 1 N j) / 2 := by simp
  rw [hpar]
  refine eq_of_equation_12_9_eq N (discreteSolutionOperator_mem_gridZero N 1)
    FiniteDifference.parabola_mem_gridZero ?_
  rw [equation_12_25 N 1]
  exact (FiniteDifference.discreteLaplacian_parabola zero_lt_one).symm

/-! ### Convergence (12.27)–(12.28) -/

/-- **Equation (12.28)** of [quarteroni2000numerical], the stability in the maximum norm proved
inside Theorem 12.1. For every $e \in V_h^0$,
$$\|e\|_{h,\infty} \le \frac{1}{8} \|L_h e\|_{h,\infty}.$$

For a finite difference solution $u_h$ with datum $f$ this gives $\|u_h\|_{h,\infty} \le
\frac{1}{8} \max_{1 \le j \le n-1} |f(x_j)|$, the discrete counterpart of (12.5). -/
theorem equation_12_28 (N : ℕ) {e : Fin (N + 2) → ℝ} (he : e ∈ FiniteDifference.gridZero N) :
    ‖e‖ ≤ 1 / 8 * ‖equation_12_9 N e‖ := by
  have h := FiniteDifference.norm_le_of_discreteLaplacian_eq (n := N) (a := 0) (b := 1)
    zero_lt_one he (g := equation_12_9 N e) rfl
  norm_num at h ⊢
  exact h

/-- **Theorem 12.1** of [quarteroni2000numerical], with an explicit bound. Let $f \in C^2([0, 1])$
with $|f''(x)| \le M$ for $x \in (0, 1)$, let $u$ solve the boundary value problem (12.1)–(12.2)
with datum $f$, and let $u_h$ be the finite difference solution with datum $f$. Then
$$\max_{0 \le j \le n} |u(x_j) - u_j| \le \frac{h^2}{96} M.$$
-/
theorem theorem_12_1_of_forall_le (N : ℕ) {f u : ℝ → ℝ} {M : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) (hu : IsSolution f u)
    (hM : ∀ x ∈ Ioo (0 : ℝ) 1, |iteratedDeriv 2 f x| ≤ M) {uh : Fin (N + 2) → ℝ}
    (huh : IsFiniteDifferenceSolution N f uh) :
    ‖u ∘ FiniteDifference.uniformGrid 0 1 N - uh‖ ≤ 1 / 96 * meshSize N ^ 2 * M := by
  have h := FiniteDifference.norm_sub_le_of_discreteLaplacian_eq zero_lt_one
    (hu.contDiffOn_four hf) hu.iteratedDeriv_two hM hu.equation_12_2_left
    hu.equation_12_2_right huh.1 huh.2
  rw [meshSize_def]
  norm_num at h ⊢
  exact h

/-- **Theorem 12.1** of [quarteroni2000numerical]. Let $f \in C^2([0, 1])$, let $u$ solve the
boundary value problem (12.1)–(12.2) with datum $f$, and let $u_h$ be the finite difference
solution with datum $f$. Then the nodal error satisfies
$$\|u - u_h\|_{h,\infty} \le \frac{h^2}{96} \|f''\|_\infty.$$
This is convergence of order two in the discrete maximum norm.

The proof combines the stability (12.28) with the consistency (12.20). The nodal error is the
grid function $(u(x_j) - u_j)_{j=0}^n$, and $\|f''\|_\infty$ is
`QuarteroniSaccoSaleri.Chapter12.normSecondDeriv f`. -/
theorem theorem_12_1 (N : ℕ) {f u : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hu : IsSolution f u) {uh : Fin (N + 2) → ℝ} (huh : IsFiniteDifferenceSolution N f uh) :
    ‖u ∘ FiniteDifference.uniformGrid 0 1 N - uh‖
      ≤ 1 / 96 * meshSize N ^ 2 * normSecondDeriv f :=
  theorem_12_1_of_forall_le N hf hu
    (fun _ hx => abs_iteratedDeriv_two_le_normSecondDeriv hf hx) huh

/-! ### Variable coefficients (§12.2.3) -/

/-- **Equations (12.32)–(12.33)** of [quarteroni2000numerical]. For the problem
$-(\alpha u')' + \gamma u = f$ on $(0, 1)$, the **discrete operator with variable coefficients**
maps a grid function $w$ to
$$(L_h w)(x_j) = -\frac{J_{j+1/2}(w) - J_{j-1/2}(w)}{h} + \gamma(x_j) w_j, \qquad j = 1, \dots,
  n - 1,$$
with the fluxes $J_{j+1/2}(w) = \alpha(x_{j+1/2}) (w_{j+1} - w_j)/h$ at the midpoints
$x_{j+1/2} = (x_j + x_{j+1})/2$.

The definition is `FiniteDifference.variableCoeffOperator 0 1 N α γ`. -/
noncomputable def equation_12_32 (N : ℕ) (α γ : ℝ → ℝ) :
    (Fin (N + 2) → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  FiniteDifference.variableCoeffOperator 0 1 N α γ

/-- **Equation (12.31)** of [quarteroni2000numerical]. A grid function $u_h$ solves the **scheme
with variable coefficients** and Dirichlet data $d_0$, $d_1$ if $u_0 = d_0$, $u_n = d_1$, and
$(L_h u_h)(x_j) = f(x_j)$ for $j = 1, \dots, n - 1$, with the operator $L_h$ of (12.32)–(12.33). -/
def IsVariableCoeffSolution (N : ℕ) (α γ f : ℝ → ℝ) (d₀ d₁ : ℝ) (u : Fin (N + 2) → ℝ) : Prop :=
  u 0 = d₀ ∧ u (Fin.last (N + 1)) = d₁ ∧
    ∀ j : Fin N, equation_12_32 N α γ u j
      = f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc)

/-- **Equation (12.34)** of [quarteroni2000numerical]. The **matrix of the scheme with variable
coefficients** is
$$h^{-2} \operatorname{tridiag}(-\alpha_{j+1/2},\ \alpha_{j-1/2} + \alpha_{j+1/2},\
  -\alpha_{j+1/2}) + \operatorname{diag}(\gamma_j),$$
with $\alpha_{j+1/2} = \alpha(x_{j+1/2})$ and $\gamma_j = \gamma(x_j)$. That is, row $j$ has the
diagonal entry $(\alpha_{j-1/2} + \alpha_{j+1/2})/h^2 + \gamma_j$ and the off-diagonal entries
$-\alpha_{j-1/2}/h^2$ and $-\alpha_{j+1/2}/h^2$.

**Typo.** The source writes the off-diagonal vector as $a = (\alpha_{1/2}, \dots)$, without the
minus sign.

The definition is `FiniteDifference.variableCoeffMatrix 0 1 N α γ`. -/
noncomputable def equation_12_34 (N : ℕ) (α γ : ℝ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  FiniteDifference.variableCoeffMatrix 0 1 N α γ

/-- **Equation (12.34)** of [quarteroni2000numerical], positive definiteness. If
$\alpha(x_{j+1/2}) > 0$ at every midpoint, $j = 0, \dots, n - 1$, and $\gamma(x_j) \ge 0$ at
every interior node, then the matrix (12.34) is symmetric positive definite. -/
theorem equation_12_34_posDef (N : ℕ) (α γ : ℝ → ℝ)
    (hα : ∀ j : Fin (N + 1), 0 < α (FiniteDifference.midGrid 0 1 N j))
    (hγ : ∀ i : Fin N, 0 ≤ γ (FiniteDifference.uniformGrid 0 1 N i.succ.castSucc)) :
    (equation_12_34 N α γ).PosDef :=
  FiniteDifference.variableCoeffMatrix_posDef zero_lt_one α γ hα hγ

/-- **Equation (12.34)** of [quarteroni2000numerical], diagonal dominance. If
$\alpha(x_{j+1/2}) \ge 0$ at every midpoint and $\gamma(x_j) > 0$ at every interior node, then
the matrix (12.34) is strictly diagonally dominant by rows. -/
theorem equation_12_34_diagDominant (N : ℕ) (α γ : ℝ → ℝ)
    (hα : ∀ j : Fin (N + 1), 0 ≤ α (FiniteDifference.midGrid 0 1 N j))
    (hγ : ∀ i : Fin N, 0 < γ (FiniteDifference.uniformGrid 0 1 N i.succ.castSucc)) :
    (equation_12_34 N α γ).IsStrictDiagDominant :=
  FiniteDifference.variableCoeffMatrix_isStrictDiagDominant zero_lt_one α γ hα hγ

/-- **Equation (12.35)** of [quarteroni2000numerical], the Neumann condition by mirror imaging. A
grid function $u_h$ solves the scheme with the Dirichlet condition $u_0 = d_0$ and the Neumann
condition $J(u)(1) = \alpha(1) u'(1) = g_1$ if $u_0 = d_0$, $(L_h u_h)(x_j) = f(x_j)$ for
$j = 1, \dots, n - 1$ with the operator (12.32)–(12.33), and the last row
$$-\frac{\alpha_{n-1/2}}{h^2} u_{n-1} + \Big(\frac{\alpha_{n-1/2}}{h^2} +
  \frac{\gamma(1)}{2}\Big) u_n = \frac{g_1}{h} + \frac{f(1)}{2}$$
holds, the discretization given by (12.35) and the display after it.

The source calls this discretization second-order accurate without proof; this is not
formalized. The definition is `FiniteDifference.IsNeumannSolution`. -/
def equation_12_35 (N : ℕ) (α γ f : ℝ → ℝ) (d₀ g₁ : ℝ) (u : Fin (N + 2) → ℝ) : Prop :=
  FiniteDifference.IsNeumannSolution 0 1 N α γ f d₀ g₁ u

/-- **Exercise 12.10** of [quarteroni2000numerical], referred to at the end of Section 12.2.3. A
grid function $u_h$ solves the scheme with the Robin conditions
$\lambda_0 u(0) + \mu_0 u'(0) = g_0$ and $\lambda_1 u(1) + \mu_1 u'(1) = g_1$, discretized by
mirror imaging, if $(L_h u_h)(x_j) = f(x_j)$ for $j = 1, \dots, n - 1$ with the operator
(12.32)–(12.33), and
$$\Big(\frac{\alpha_{1/2}}{h^2} + \frac{\gamma(0)}{2} + \frac{\alpha(0) \lambda_0}{\mu_0 h}\Big)
  u_0 - \frac{\alpha_{1/2}}{h^2} u_1 = \frac{\alpha(0) g_0}{\mu_0 h} + \frac{f(0)}{2},$$
$$\Big(\frac{\alpha_{n-1/2}}{h^2} + \frac{\gamma(1)}{2} + \frac{\alpha(1) \lambda_1}{\mu_1
  h}\Big) u_n - \frac{\alpha_{n-1/2}}{h^2} u_{n-1} = \frac{\alpha(1) g_1}{\mu_1 h} +
  \frac{f(1)}{2}.$$

**Typo.** The source prints the left condition with $u(0)$ in place of $u'(0)$.

The definition is `FiniteDifference.IsRobinSolution`. -/
def exercise_12_10 (N : ℕ) (α γ f : ℝ → ℝ) (lam₀ mu₀ g₀ lam₁ mu₁ g₁ : ℝ)
    (u : Fin (N + 2) → ℝ) : Prop :=
  FiniteDifference.IsRobinSolution 0 1 N α γ f lam₀ mu₀ g₀ lam₁ mu₁ g₁ u

/-- **Exercise 12.11** of [quarteroni2000numerical], referred to in Section 12.2. On a grid function
$w = (w_0, \dots, w_{n+2})$ with step $h$, the centred discretization of the fourth-order
operator is the composition $L_h \circ L_h$ of the operator (12.9) with itself, with values at
the nodes $j = 2, \dots, n$.

The exercise names the operator $Lu = -u''''$. Since $L_h$ approximates $-u''$, the composition
approximates $u''''$, so it discretizes $L$ up to the sign. The inner operator acts on $n + 1$
interior nodes and the outer one on $n - 1$, both with the step $h = 1/n$. -/
noncomputable def exercise_12_11 (N : ℕ) : (Fin (N + 4) → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  (FiniteDifference.discreteLaplacian N (meshSize N)).comp
    (FiniteDifference.discreteLaplacian (N + 2) (meshSize N))

/-- The five-point stencil of $L_h \circ L_h$ in Exercise 12.11: at the node $j = 2, \dots, n$,
$$(L_h L_h w)_j = \frac{w_{j+2} - 4w_{j+1} + 6w_j - 4w_{j-1} + w_{j-2}}{h^4}.$$
-/
theorem exercise_12_11_apply (N : ℕ) (w : Fin (N + 4) → ℝ) (i : Fin N) :
    exercise_12_11 N w i
      = (w ⟨(i : ℕ) + 4, by omega⟩ - 4 * w ⟨(i : ℕ) + 3, by omega⟩
          + 6 * w ⟨(i : ℕ) + 2, by omega⟩ - 4 * w ⟨(i : ℕ) + 1, by omega⟩
          + w ⟨(i : ℕ), by omega⟩) / meshSize N ^ 4 := by
  have h4 : (⟨(i : ℕ) + 4, by omega⟩ : Fin (N + 4)) = i.succ.succ.succ.succ := Fin.ext (by simp)
  have h3 : (⟨(i : ℕ) + 3, by omega⟩ : Fin (N + 4)) = i.succ.succ.succ.castSucc :=
    Fin.ext (by simp)
  have h2 : (⟨(i : ℕ) + 2, by omega⟩ : Fin (N + 4)) = i.succ.succ.castSucc.castSucc :=
    Fin.ext (by simp)
  have h1 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (N + 4)) = i.succ.castSucc.castSucc.castSucc :=
    Fin.ext (by simp)
  have h0 : (⟨(i : ℕ), by omega⟩ : Fin (N + 4)) = i.castSucc.castSucc.castSucc.castSucc :=
    Fin.ext (by simp)
  have hne := meshSize_ne_zero N
  rw [h4, h3, h2, h1, h0, exercise_12_11]
  simp only [LinearMap.comp_apply, FiniteDifference.discreteLaplacian_apply, Fin.castSucc_succ]
  field_simp
  ring

end QuarteroniSaccoSaleri.Chapter12
