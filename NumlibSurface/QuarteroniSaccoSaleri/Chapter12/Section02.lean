import Numlib.Analysis.Sobolev.Interval
import Numlib.FiniteDifference.BoundaryValue
import NumlibSurface.QuarteroniSaccoSaleri.Chapter12.Section01

/-!
# Quarteroni–Sacco–Saleri §12.2: finite difference approximation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §12.2.

The model problem `-u'' = f` on `(0, 1)` with `u(0) = u(1) = 0` is discretized on the uniform
grid `x_j = j h`, `h = 1/n`, by the centred second difference (12.6). The resulting linear system
(12.7) has the matrix `A_fd = h⁻² tridiag(-1, 2, -1)` (12.8), which is symmetric, diagonally
dominant, positive definite and an M-matrix — whence the discrete maximum principle. In operator
form (12.9)–(12.10) the scheme reads `L_h u_h = f` on the grid functions vanishing at the ends.
The energy method (§12.2.1) gives the symmetry and positivity of `L_h` (Lemma 12.1), the discrete
Poincaré inequality (Lemma 12.2) and the stability estimate (12.17); Taylor expansion gives the
consistency (12.19)–(12.20) and its Lipschitz refinement (Remark 12.2); the discrete Green's
function (12.24)–(12.26) and the maximum-norm stability (12.28) give Theorem 12.1, the `O(h²)`
convergence of the nodal error. §12.2.3 treats the variable-coefficient problem
`-(α u')' + γ u = f` and the mirror-imaging discretization of a Neumann or Robin condition.

## Conventions

The book counts `n` subintervals, so `n - 1` interior nodes; the backbone
`Numlib/FiniteDifference/BoundaryValue.lean` counts the *interior* nodes. Everything here is
therefore written with `N = n - 1` interior nodes, `n = N + 1` subintervals, the grid
`FiniteDifference.uniformGrid 0 1 N : Fin (N + 2) → ℝ` and the mesh size
`meshSize N = 1/(N + 1)`.

The objects of §12.2.1 are the backbone's, at `a = 0`, `b = 1` and `h = meshSize N`: `V_h^0` is
`FiniteDifference.gridZero N`, the discrete inner product `(·, ·)_h` is
`FiniteDifference.discreteInner N (meshSize N)`, the norm `‖·‖_h` is
`FiniteDifference.discreteL2Norm N (meshSize N)` (the backbone avoids the name `discreteNorm`,
which the `ℓ^p` mesh norm of `Numlib/FiniteDifference/Stencil.lean` already carries), the
seminorm `‖|·|‖_h` (12.12) is `FiniteDifference.discreteH1Seminorm N (meshSize N)`, and the
discrete maximum norm `‖·‖_{h,∞}` is the supremum norm `‖·‖` of `Fin (N + 2) → ℝ`. `L_h` is
`equation_12_9`.

## Main definitions

* `meshSize` — the mesh size `h = 1/n = 1/(N + 1)`.
* `finiteDifferenceMatrix` — `A_fd` of (12.8).
* `IsFiniteDifferenceSolution` — the scheme (12.6), equivalently (12.10).
* `equation_12_9` — the operator `L_h` of (12.9).
* `discreteGreen`, `discreteSolutionOperator` — `G^k` and `T_h` of (12.24)–(12.25).
* `equation_12_32`, `equation_12_34`, `equation_12_35`, `exercise_12_10`, `exercise_12_11` — the
  variable-coefficient scheme with its matrix, the Neumann and Robin rows, and the fourth-order
  operator.

## Main results

* `finiteDifferenceMatrix_isSymm`, `_posDef`, `_diagDominant`, `exercise_12_2` — the properties
  of `A_fd` listed after (12.8), and the discrete maximum principle.
* `lemma_12_1_symm`, `lemma_12_1_pos`, `equation_12_13` — Lemma 12.1 and (12.13).
* `exercise_12_4`, `lemma_12_2`, `remark_12_1` — the inequality (12.15), the discrete Poincaré
  inequality (12.14) and its continuous counterpart (12.16).
* `equation_12_17` — the stability estimate `‖u_h‖_h ≤ ‖f_h‖_h / 2`, and uniqueness.
* `equation_12_19`, `equation_12_20`, `remark_12_2`, `remark_12_3` — consistency, and
  `exercise_12_5` the bound (12.23) `‖τ_h‖_h² ≤ 3(‖f‖_h² + ‖f‖²_{L²(0,1)})`.
* `equation_12_24`, `equation_12_25`, `equation_12_26`, `exercise_12_6`, `exercise_12_7` — the
  discrete Green's function.
* `equation_12_28`, `theorem_12_1` — maximum-norm stability and `O(h²)` convergence.
-/

open Set Finset Matrix MeasureTheory FiniteDifference

namespace QuarteroniSaccoSaleri.Chapter12

variable {N : ℕ}

/-! ### The grid -/

/-- **The mesh size** `h = 1/n` of the uniform grid `x_j = j h` of §12.2, written with the number
`N = n - 1` of *interior* nodes: `h = 1/(N + 1)`. -/
noncomputable def meshSize (N : ℕ) : ℝ := FiniteDifference.gridStep 0 1 N

theorem meshSize_def (N : ℕ) : meshSize N = FiniteDifference.gridStep 0 1 N := rfl

theorem meshSize_eq (N : ℕ) : meshSize N = 1 / ((N : ℝ) + 1) := by
  simp [meshSize, FiniteDifference.gridStep]

theorem meshSize_pos (N : ℕ) : 0 < meshSize N := gridStep_pos zero_lt_one

theorem meshSize_ne_zero (N : ℕ) : meshSize N ≠ 0 := (meshSize_pos N).ne'

/-- `(N + 1) h = 1`: the `N + 1` panels fill `[0, 1]`. -/
theorem succ_mul_meshSize (N : ℕ) : ((N : ℝ) + 1) * meshSize N = 1 := by
  rw [meshSize_def]
  simpa using gridStep_mul_succ (a := (0 : ℝ)) (b := 1) (n := N)

/-- The nodes `x_j = j h` of the grid. -/
theorem uniformGrid_eq (N : ℕ) (j : Fin (N + 2)) :
    FiniteDifference.uniformGrid 0 1 N j = ((j : ℕ) : ℝ) * meshSize N := by
  simp [FiniteDifference.uniformGrid, meshSize]

/-- The interior nodes are `x_{j+1} = (j + 1) h`. -/
theorem uniformGrid_interior_eq (N : ℕ) (j : Fin N) :
    FiniteDifference.uniformGrid 0 1 N j.succ.castSucc = (((j : ℕ) : ℝ) + 1) * meshSize N := by
  rw [uniformGrid_eq]
  norm_num

/-! ### The scheme (12.6)–(12.8) -/

/-- **The finite difference matrix** `A_fd = h⁻² tridiag_{n-1}(-1, 2, -1)` of
[quarteroni2000numerical] (12.8), on the `N = n - 1` interior nodes. -/
noncomputable def finiteDifferenceMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (meshSize N ^ 2)⁻¹ • Matrix.symmTridiagonalToeplitz N (-1) 2

theorem finiteDifferenceMatrix_apply (N : ℕ) (i j : Fin N) :
    finiteDifferenceMatrix N i j
      = (meshSize N ^ 2)⁻¹ * Matrix.symmTridiagonalToeplitz N (-1) 2 i j := rfl

theorem inv_meshSize_sq_pos (N : ℕ) : (0 : ℝ) < (meshSize N ^ 2)⁻¹ :=
  inv_pos.2 (pow_pos (meshSize_pos N) 2)

/-- `A_fd` is symmetric ([quarteroni2000numerical], the line after (12.8)). -/
theorem finiteDifferenceMatrix_isSymm (N : ℕ) : (finiteDifferenceMatrix N).IsSymm := by
  change (finiteDifferenceMatrix N)ᵀ = finiteDifferenceMatrix N
  rw [finiteDifferenceMatrix, Matrix.transpose_smul, Matrix.symmTridiagonalToeplitz_isSymm]

/-- **`A_fd` is positive definite** ([quarteroni2000numerical], the display after (12.8)), whence
the linear system (12.7) has a unique solution. -/
theorem finiteDifferenceMatrix_posDef (N : ℕ) : (finiteDifferenceMatrix N).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨Matrix.isHermitian_iff_isSymm.2 (finiteDifferenceMatrix_isSymm N), fun x hx => ?_⟩
  have h := (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two N).dotProduct_mulVec_pos hx
  rw [finiteDifferenceMatrix, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_pos (inv_meshSize_sq_pos N) h

/-- At most two off-diagonal entries of a row of `tridiag(-1, 2, -1)` are nonzero, and each has
modulus `1`. -/
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

/-- **`A_fd` is diagonally dominant by rows** ([quarteroni2000numerical], the line after
(12.8)): `∑_{j ≠ i} |A_fd i j| ≤ |A_fd i i|`. -/
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

/-- **The finite difference scheme** (12.6), equivalently the operator form (12.10): a grid
function `u_h` vanishing at the endpoints with `L_h u_h (x_j) = f(x_j)` at every interior node. -/
def IsFiniteDifferenceSolution (N : ℕ) (f : ℝ → ℝ) (u : Fin (N + 2) → ℝ) : Prop :=
  u ∈ FiniteDifference.gridZero N ∧
    FiniteDifference.discreteLaplacian N (meshSize N) u
      = fun j => f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc)

/-- **The scheme is the linear system (12.7)** `A_fd u = f` on the interior values. -/
theorem isFiniteDifferenceSolution_iff_mulVec (N : ℕ) (f : ℝ → ℝ) {u : Fin (N + 2) → ℝ}
    (hu : u ∈ FiniteDifference.gridZero N) :
    IsFiniteDifferenceSolution N f u ↔
      finiteDifferenceMatrix N *ᵥ FiniteDifference.interior N u
        = fun j => f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc) := by
  rw [IsFiniteDifferenceSolution, and_iff_right hu,
    FiniteDifference.discreteLaplacian_eq_mulVec (meshSize N) hu, finiteDifferenceMatrix,
    Matrix.smul_mulVec]

/-- **Exercise 12.2**, cited in §12.2: `A_fd` is an M-matrix. The book's hint — continuity of
`(A_fd + αI)⁻¹` in `α` — is not the route; the backbone uses the Stieltjes criterion. -/
theorem exercise_12_2 (N : ℕ) : (finiteDifferenceMatrix N).IsMMatrix :=
  Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos (finiteDifferenceMatrix_posDef N) fun i j hij => by
    rw [finiteDifferenceMatrix_apply]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_meshSize_sq_pos N).le
      (Matrix.symmTridiagonalToeplitz_offDiag_nonpos (by norm_num) 2 hij)

/-- **The discrete maximum principle** of §12.2: the finite difference solution is nonnegative
whenever the datum is, as the exact solution is. -/
theorem exercise_12_2_nonneg (N : ℕ) {f : ℝ → ℝ} {u : Fin (N + 2) → ℝ}
    (hu : IsFiniteDifferenceSolution N f u)
    (hf : ∀ j : Fin N, 0 ≤ f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc)) : 0 ≤ u :=
  FiniteDifference.nonneg_of_discreteLaplacian_nonneg (meshSize_pos N) hu.1
    (by rw [hu.2]; exact hf)

/-! ### The operator `L_h` (12.9) -/

/-- **The discrete operator `L_h`** of [quarteroni2000numerical] (12.9):
`(L_h w)(x_j) = -(w_{j+1} - 2 w_j + w_{j-1})/h²` at the interior nodes. -/
noncomputable def equation_12_9 (N : ℕ) : (Fin (N + 2) → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  FiniteDifference.discreteLaplacian N (meshSize N)

theorem equation_12_9_apply (N : ℕ) (w : Fin (N + 2) → ℝ) (j : Fin N) :
    equation_12_9 N w j
      = -(w j.succ.succ - 2 * w j.succ.castSucc + w j.castSucc.castSucc) / meshSize N ^ 2 := rfl

/-- **(12.10)**: the finite difference problem in operator form, node by node. -/
theorem equation_12_10 (N : ℕ) (f : ℝ → ℝ) (u : Fin (N + 2) → ℝ) :
    IsFiniteDifferenceSolution N f u ↔ u ∈ FiniteDifference.gridZero N ∧
      ∀ j : Fin N, equation_12_9 N u j
        = f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc) :=
  and_congr_right' funext_iff

/-- `L_h` determines a grid function of `V_h^0`. -/
theorem eq_of_equation_12_9_eq (N : ℕ) {u v : Fin (N + 2) → ℝ}
    (hu : u ∈ FiniteDifference.gridZero N) (hv : v ∈ FiniteDifference.gridZero N)
    (h : equation_12_9 N u = equation_12_9 N v) : u = v := by
  have hL : FiniteDifference.discreteLaplacian N (meshSize N) (u - v) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 h
  exact sub_eq_zero.1 (FiniteDifference.discreteLaplacian_injective_on_gridZero
    (meshSize_ne_zero N) (Submodule.sub_mem _ hu hv) hL)

/-- `(L_h w, v)_h` written out for `v ∈ V_h^0`: the endpoint weights of the trapezoidal rule do
not see the extension by zero. -/
theorem discreteInner_equation_12_9 (N : ℕ) (w : Fin (N + 2) → ℝ) {v : Fin (N + 2) → ℝ}
    (hv : v ∈ FiniteDifference.gridZero N) :
    FiniteDifference.discreteInner N (meshSize N)
        (FiniteDifference.ofInterior N (equation_12_9 N w)) v
      = meshSize N * ∑ i, equation_12_9 N w i * FiniteDifference.interior N v i :=
  FiniteDifference.discreteInner_ofInterior _ _ hv

/-! ### Lemma 12.1 and the energy identity -/

/-- **Lemma 12.1, symmetry**: `(L_h w_h, v_h)_h = (w_h, L_h v_h)_h` on `V_h^0`. -/
theorem lemma_12_1_symm (N : ℕ) {w v : Fin (N + 2) → ℝ}
    (hw : w ∈ FiniteDifference.gridZero N) (hv : v ∈ FiniteDifference.gridZero N) :
    FiniteDifference.discreteInner N (meshSize N)
        (FiniteDifference.ofInterior N (equation_12_9 N w)) v
      = FiniteDifference.discreteInner N (meshSize N) w
        (FiniteDifference.ofInterior N (equation_12_9 N v)) :=
  FiniteDifference.discreteInner_discreteLaplacian_comm (meshSize_ne_zero N) hw hv

/-- **(12.13)**: `(L_h v_h, v_h)_h = ‖|v_h|‖_h²` on `V_h^0`. -/
theorem equation_12_13 (N : ℕ) {v : Fin (N + 2) → ℝ} (hv : v ∈ FiniteDifference.gridZero N) :
    FiniteDifference.discreteInner N (meshSize N)
        (FiniteDifference.ofInterior N (equation_12_9 N v)) v
      = FiniteDifference.discreteH1Seminorm N (meshSize N) v ^ 2 := by
  rw [discreteInner_equation_12_9 N v hv]
  exact FiniteDifference.discreteInner_discreteLaplacian_self (meshSize_pos N) hv

/-- **Lemma 12.1, positivity**: `(L_h v_h, v_h)_h ≥ 0` on `V_h^0`, with equality only for
`v_h = 0`. -/
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

/-- **Exercise 12.4**, the inequality (12.15) used in the proof of Lemma 12.2:
`(∑_{k<m} p_k)² ≤ m ∑_{k<m} p_k²`. The book calls it the Minkowski inequality; it is
Cauchy–Schwarz against the constant vector. -/
theorem exercise_12_4 {m : ℕ} (p : Fin m → ℝ) : (∑ k, p k) ^ 2 ≤ m * ∑ k, p k ^ 2 := by
  simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := p)

/-- **Lemma 12.2**, the discrete Poincaré inequality (12.14): `‖v_h‖_h ≤ (1/√2) ‖|v_h|‖_h` for
every `v_h ∈ V_h^0`. -/
theorem lemma_12_2 (N : ℕ) {v : Fin (N + 2) → ℝ} (hv : v ∈ FiniteDifference.gridZero N) :
    FiniteDifference.discreteL2Norm N (meshSize N) v
      ≤ 1 / Real.sqrt 2 * FiniteDifference.discreteH1Seminorm N (meshSize N) v := by
  have h1 : ((N : ℝ) + 1) * meshSize N / Real.sqrt 2 = 1 / Real.sqrt 2 := by
    rw [succ_mul_meshSize]
  rw [← h1]
  exact FiniteDifference.discreteL2Norm_le_discreteH1Seminorm (meshSize_pos N) hv

/-- **Remark 12.1**: (12.14) read with the discrete derivative `v_h^{(1)}`, whose values are
`(v_{j+1} - v_j)/h`. -/
theorem lemma_12_2_discreteDeriv (N : ℕ) (v : Fin (N + 2) → ℝ) :
    FiniteDifference.discreteH1Seminorm N (meshSize N) v
      = Real.sqrt (meshSize N * ∑ j, FiniteDifference.discreteDeriv N (meshSize N) v j ^ 2) :=
  rfl

/-- **Remark 12.1**, the continuous Poincaré inequality (12.16) with `C_P = (b - a)/√2`: the
`L²` norm of a function of `H^1_0(a, b)` is at most `C_P` times the `L²` norm of its derivative.
The book states it for `v ∈ C¹([a, b])` with `v(a) = v(b) = 0`;
`remark_12_1_of_eq_integral` is the elementary form that covers those, since such a `v` is the
antiderivative `∫_a^x v'`. -/
theorem remark_12_1 {a b : ℝ} (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) :
    ‖SobolevInterval.deriv u 0‖ ≤ (b - a) / Real.sqrt 2 * ‖SobolevInterval.deriv u 1‖ :=
  SobolevIntervalZero.norm_deriv_zero_le hab hu

/-- **Remark 12.1**, (12.16) in elementary form: an `L²` function that is almost everywhere the
antiderivative `∫_a^x w` of an `L²` function `w` satisfies `‖g‖_{L²} ≤ ((b - a)/√2) ‖w‖_{L²}`.
Every `v ∈ C¹([a, b])` with `v(a) = 0` is of this form, with `w = v'`. -/
theorem remark_12_1_of_eq_integral {a b : ℝ} (hab : a ≤ b)
    {w g : Lp ℝ 2 (volume.restrict (Ioo a b))}
    (hg : g =ᵐ[volume.restrict (Ioo a b)] fun x => ∫ t in a..x, w t) :
    ‖g‖ ≤ (b - a) / Real.sqrt 2 * ‖w‖ :=
  SobolevInterval.norm_le_of_eq_integral hab hg

/-! ### Stability by the energy method (12.17) -/

/-- **The stability estimate (12.17)**: `‖u_h‖_h ≤ ‖f_h‖_h / 2` for the finite difference
solution, `f_h` the grid function of the nodal values of `f`. -/
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

/-- **Uniqueness of the finite difference solution**, the consequence of (12.17). -/
theorem equation_12_17_unique (N : ℕ) {f : ℝ → ℝ} {u v : Fin (N + 2) → ℝ}
    (hu : IsFiniteDifferenceSolution N f u) (hv : IsFiniteDifferenceSolution N f v) : u = v :=
  eq_of_equation_12_9_eq N hu.1 hv.1 (hu.2.trans hv.2.symm)

/-! ### Consistency (12.18)–(12.22) -/

/-- The maximum norm `‖f''‖_∞` of the second derivative of `f ∈ C²([0, 1])`, written with
`iteratedDerivWithin` so that it is defined at the endpoints as well. -/
noncomputable def normSecondDeriv (f : ℝ → ℝ) : ℝ :=
  sSup ((fun s => |iteratedDerivWithin 2 f (Icc 0 1) s|) '' Icc 0 1)

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

/-- The `C⁴` regularity of the solution, from (12.1) and `f ∈ C²([0, 1])`. -/
theorem IsSolution.contDiffOn_four {f u : ℝ → ℝ} (hu : IsSolution f u)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) : ContDiffOn ℝ 4 u (Icc 0 1) :=
  (hu.contDiffOn_of_contDiffOn (m := 2) hf).of_le (by norm_num)

theorem IsSolution.iteratedDeriv_two {f u : ℝ → ℝ} (hu : IsSolution f u) :
    ∀ x ∈ Ioo (0 : ℝ) 1, iteratedDeriv 2 u x = -f x :=
  fun x hx => by rw [← hu.equation_12_1 x hx, neg_neg]

/-- **(12.19)**, the truncation error in Lagrange form: `τ_h(x_j) = -(h²/24)(u⁗(ξ_j) + u⁗(η_j))`
with `ξ_j ∈ (x_{j-1}, x_j)` and `η_j ∈ (x_j, x_{j+1})`. The book prints `+h²/24`; written with
`u⁗` rather than `f''` the sign is a misprint (see `notes/book-errata.md`). -/
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

/-- **(12.20)**, consistency with an explicit bound on `f''`. -/
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

/-- **(12.20)**, consistency: `‖τ_h‖_{h,∞} ≤ h² ‖f''‖_∞ / 12` for `f ∈ C²([0, 1])`, so that
`τ_h → 0` as `h → 0` and the scheme is consistent. -/
theorem equation_12_20 (N : ℕ) {f u : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hu : IsSolution f u) (j : Fin N) :
    |FiniteDifference.truncationError 0 1 N u f j| ≤ meshSize N ^ 2 / 12 * normSecondDeriv f :=
  equation_12_20_of_forall_le N hf hu
    (fun _ hx => abs_iteratedDeriv_two_le_normSecondDeriv hf hx) j

/-- **(12.20) in the discrete maximum norm**, the book's form: `‖τ_h‖_{h,∞} ≤ h² ‖f''‖_∞/12`. -/
theorem equation_12_20_norm (N : ℕ) {f u : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hu : IsSolution f u) :
    ‖FiniteDifference.truncationError 0 1 N u f‖ ≤ meshSize N ^ 2 / 12 * normSecondDeriv f :=
  FiniteDifference.norm_truncationError_le_of_contDiffOn zero_lt_one (hu.contDiffOn_four hf)
    hu.iteratedDeriv_two fun x hx ↦ by
      rw [FiniteDifference.iteratedDeriv_four_eq_neg_iteratedDeriv_two hu.iteratedDeriv_two hx,
        abs_neg]
      exact abs_iteratedDeriv_two_le_normSecondDeriv hf hx

/-- **Remark 12.2**: `u ∈ C^{3,1}(0, 1)` — `u'''` Lipschitz with constant `M` — already gives
`‖τ_h‖_{h,∞} ≤ M h²/12`, sharper than the book's `M h²`. -/
theorem remark_12_2 (N : ℕ) {f u : ℝ → ℝ} {M : NNReal} (hu : ContDiffOn ℝ 3 u (Icc 0 1))
    (hM : LipschitzOnWith M (iteratedDeriv 3 u) (Ioo 0 1))
    (hu'' : ∀ x ∈ Ioo (0 : ℝ) 1, iteratedDeriv 2 u x = -f x) (j : Fin N) :
    |FiniteDifference.truncationError 0 1 N u f j| ≤ (M : ℝ) * meshSize N ^ 2 / 12 :=
  FiniteDifference.abs_truncationError_le_of_lipschitzOnWith zero_lt_one hu hM hu'' j

/-- **Remark 12.3**, the error equation (12.22): `L_h e = L_h u - f_h = τ_h` for the
discretization error `e = u - u_h`. -/
theorem remark_12_3 (N : ℕ) {f : ℝ → ℝ} (u : ℝ → ℝ) {uh : Fin (N + 2) → ℝ}
    (hu : IsFiniteDifferenceSolution N f uh) :
    equation_12_9 N (u ∘ FiniteDifference.uniformGrid 0 1 N - uh)
      = FiniteDifference.truncationError 0 1 N u f :=
  FiniteDifference.error_eq_of_discreteLaplacian_eq u f hu.2

/-! ### Exercise 12.5, the `‖·‖_h` bound (12.23) on the truncation error -/

section Exercise125

open intervalIntegral

/-- **Cauchy–Schwarz for interval integrals**: `(∫ f k)² ≤ (∫ f²)(∫ k²)` on `[p, q]`, by the
nonnegativity of `∫ (λ f + k)²` and the discriminant; the backbone's
`intervalIntegral.sq_integral_mul_le_of_continuousOn`. -/
theorem sq_integral_mul_le {f k : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hf : ContinuousOn f (Icc p q)) (hk : ContinuousOn k (Icc p q)) :
    (∫ t in p..q, f t * k t) ^ 2 ≤ (∫ t in p..q, f t ^ 2) * ∫ t in p..q, k t ^ 2 :=
  intervalIntegral.sq_integral_mul_le_of_continuousOn hpq hf hk

/-- **Taylor's formula with integral remainder, right end**:
`∫_p^q u''(t)(q - t) dt = u(q) - u(p) - (q - p) u'(p)`, by the fundamental theorem of calculus
applied to the primitive `u'(t)(q - t) + u(t)`. Only interior differentiability is asked for, so it
applies on a panel abutting an endpoint of `[0, 1]`. -/
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


/-- **Taylor's formula with integral remainder, left end**:
`∫_p^q u''(t)(t - p) dt = u(p) - u(q) + (q - p) u'(q)`, by the fundamental theorem of calculus
applied to the primitive `u'(t)(t - p) - u(t)`. -/
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

/-- The square of the right Taylor kernel integrates to `h³/3`. -/
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

/-- The square of the left Taylor kernel integrates to `h³/3`. -/
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


/-- **(12.21) in terms of the datum**: for a solution `u` of (12.1)–(12.2) and a node `x` with
`[x - h, x + h] ⊆ [0, 1]`, the second difference of `u` is minus the two Taylor remainders of
`u'' = -f`:
`u(x+h) - 2u(x) + u(x-h) = -(∫_x^{x+h} f(t)(x+h-t) dt + ∫_{x-h}^x f(t)(t-x+h) dt)`. -/
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


/-- **The nodal estimate behind (12.23)**: at every interior node,
`h τ_h(x)² ≤ ∫_{x-h}^{x+h} f² + 3 h f(x)²`. The three terms of
`τ_h(x) = h⁻²(I⁺ + I⁻) - f(x)` are squared through `(a + b + c)² ≤ 3(a² + b² + c²)` and the two
integrals are bounded by Cauchy–Schwarz against the kernels, whose squares integrate to `h³/3`. -/
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


/-- The nodes of the uniform grid of `[0, 1]` are `x_j = j h`. -/
theorem grid_eq_mul (N : ℕ) (j : Fin (N + 2)) :
    uniformGrid 0 1 N j = (j : ℕ) * meshSize N := by
  rw [uniformGrid_apply, meshSize_def, zero_add]

/-- **The panel count**: each of the `n - 1` double panels `[x_{j-1}, x_{j+1}]` covers two of the
`n` panels, and every panel is covered at most twice, so
`∑_j ∫_{x_{j-1}}^{x_{j+1}} f² ≤ 2 ∫_0^1 f²`. -/
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


/-- The interior part of the trapezoidal sum is at most the whole: `h ∑_{j=1}^{n-1} w_j² ≤ ‖w‖_h²`,
the two endpoint terms of the trapezoidal weights being nonnegative. -/
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

/-- **Exercise 12.5, the bound (12.23) of Remark 12.3**:
`‖τ_h‖_h² ≤ 3 (‖f‖_h² + ‖f‖²_{L²(0,1)})`, so that the discrete second derivative of the
discretization error stays bounded as `h → 0` whenever the two norms of `f` on the right do.

The proof is the book's hint made precise (the printed hint drops the factors `h⁻²` and the `/2` of
the kernels; see `notes/book-errata.md`): integrate (12.21) by parts twice on each side to write
`τ_h(x_j)` as `-f(x_j)` plus `h⁻²` times two integrals of `f` against the kernels `x_j + h - t` and
`t - x_j + h`; square with `(a + b + c)² ≤ 3(a² + b² + c²)`, bound each integral by Cauchy–Schwarz,
and sum, each panel being counted at most twice. Continuity of `f` is all that is used — the book's
`f ∈ C²([0, 1])` is what its route to `u ∈ C⁴` needs, and is not needed here
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Exercise 12.5 and equation (12.23)). -/
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

theorem isUnit_det_finiteDifferenceMatrix (N : ℕ) : IsUnit (finiteDifferenceMatrix N).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (exercise_12_2 N).isUnit

/-- The inverse of `A_fd` is `h²` times the inverse of `tridiag(-1, 2, -1)`. -/
theorem inv_finiteDifferenceMatrix (N : ℕ) :
    (finiteDifferenceMatrix N)⁻¹
      = meshSize N ^ 2 • (Matrix.symmTridiagonalToeplitz N (-1) 2)⁻¹ := by
  have hT : IsUnit (Matrix.symmTridiagonalToeplitz N (-1) 2).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_symmTridiagonalToeplitz_neg_one_two N)
  refine Matrix.inv_eq_right_inv ?_
  rw [finiteDifferenceMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_nonsing_inv _ hT, inv_mul_cancel₀ (pow_pos (meshSize_pos N) 2).ne', one_smul]

/-- **The discrete Green's function** `G^k` of [quarteroni2000numerical] (12.24): the grid
function of `V_h^0` with `L_h G^k = e^k`, the `k`-th column of `A_fd⁻¹` extended by zero. -/
noncomputable def discreteGreen (N : ℕ) (k : Fin N) : Fin (N + 2) → ℝ :=
  FiniteDifference.ofInterior N fun j => (finiteDifferenceMatrix N)⁻¹ j k

theorem discreteGreen_mem_gridZero (N : ℕ) (k : Fin N) :
    discreteGreen N k ∈ FiniteDifference.gridZero N :=
  FiniteDifference.ofInterior_mem_gridZero _

/-- **The discrete solution operator** `T_h` of (12.25): `T_h g = ∑_k g(x_k) G^k`. -/
noncomputable def discreteSolutionOperator (N : ℕ) (g : Fin N → ℝ) : Fin (N + 2) → ℝ :=
  ∑ k, g k • discreteGreen N k

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

theorem discreteSolutionOperator_mem_gridZero (N : ℕ) (g : Fin N → ℝ) :
    discreteSolutionOperator N g ∈ FiniteDifference.gridZero N := by
  rw [discreteSolutionOperator_eq]
  exact FiniteDifference.ofInterior_mem_gridZero _

/-- **(12.25)**: `T_h` inverts `L_h`, `L_h (T_h g) = g`. -/
theorem equation_12_25 (N : ℕ) (g : Fin N → ℝ) :
    equation_12_9 N (discreteSolutionOperator N g) = g := by
  have h1 : equation_12_9 N (discreteSolutionOperator N g)
      = finiteDifferenceMatrix N *ᵥ ((finiteDifferenceMatrix N)⁻¹ *ᵥ g) := by
    rw [discreteSolutionOperator_eq, equation_12_9,
      FiniteDifference.discreteLaplacian_eq_mulVec _ (FiniteDifference.ofInterior_mem_gridZero _),
      FiniteDifference.interior_ofInterior, finiteDifferenceMatrix, Matrix.smul_mulVec]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_finiteDifferenceMatrix N),
    Matrix.one_mulVec]

/-- **(12.26)**: the finite difference solution is `u_h = T_h f`. -/
theorem equation_12_26 (N : ℕ) {f : ℝ → ℝ} {u : Fin (N + 2) → ℝ}
    (hu : IsFiniteDifferenceSolution N f u) :
    u = discreteSolutionOperator N
      fun k => f (FiniteDifference.uniformGrid 0 1 N k.succ.castSucc) :=
  eq_of_equation_12_9_eq N hu.1 (discreteSolutionOperator_mem_gridZero N _)
    (by rw [equation_12_25]; exact hu.2)

/-- **Exercise 12.6**, used in §12.2.2: `G^k(x_j) = h G(x_j, x_k)`, with `G` the Green's function
(12.4) of §12.1. -/
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

/-- **Exercise 12.7**, used in the proof of Theorem 12.1: `T_h 1 (x_j) = x_j (1 - x_j)/2`. -/
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

/-- **(12.28)**, the maximum-norm stability proved inside Theorem 12.1:
`‖e‖_{h,∞} ≤ (1/8) ‖L_h e‖_{h,∞}` for every `e ∈ V_h^0`; for the finite difference solution it
is `‖u_h‖_{h,∞} ≤ (1/8) ‖f‖_{h,∞}`, the discrete counterpart of (12.5). -/
theorem equation_12_28 (N : ℕ) {e : Fin (N + 2) → ℝ} (he : e ∈ FiniteDifference.gridZero N) :
    ‖e‖ ≤ 1 / 8 * ‖equation_12_9 N e‖ := by
  have h := FiniteDifference.norm_le_of_discreteLaplacian_eq (n := N) (a := 0) (b := 1)
    zero_lt_one he (g := equation_12_9 N e) rfl
  norm_num at h ⊢
  exact h

/-- **Theorem 12.1** with an explicit bound on `f''`. -/
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

/-- **Theorem 12.1**: for `f ∈ C²([0, 1])` the nodal error of the finite difference solution
satisfies `‖u - u_h‖_{h,∞} ≤ (h²/96) ‖f''‖_∞` — second-order convergence in the discrete maximum
norm, from the stability (12.28) and the consistency (12.20). -/
theorem theorem_12_1 (N : ℕ) {f u : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hu : IsSolution f u) {uh : Fin (N + 2) → ℝ} (huh : IsFiniteDifferenceSolution N f uh) :
    ‖u ∘ FiniteDifference.uniformGrid 0 1 N - uh‖
      ≤ 1 / 96 * meshSize N ^ 2 * normSecondDeriv f :=
  theorem_12_1_of_forall_le N hf hu
    (fun _ hx => abs_iteratedDeriv_two_le_normSecondDeriv hf hx) huh

/-! ### Variable coefficients (§12.2.3) -/

/-- **The variable-coefficient operator** of (12.32)–(12.33) on `[0, 1]`: `L_h w (x_j) =
-(J_{j+1/2}(w) - J_{j-1/2}(w))/h + γ_j w_j` with the midpoint fluxes
`J_{j+1/2}(w) = α_{j+1/2} (w_{j+1} - w_j)/h`. -/
noncomputable def equation_12_32 (N : ℕ) (α γ : ℝ → ℝ) :
    (Fin (N + 2) → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  FiniteDifference.variableCoeffOperator 0 1 N α γ

/-- **The variable-coefficient scheme (12.31)**: the interior equations with the Dirichlet data
`u_h(x_0) = d₀`, `u_h(x_n) = d₁`. -/
def IsVariableCoeffSolution (N : ℕ) (α γ f : ℝ → ℝ) (d₀ d₁ : ℝ) (u : Fin (N + 2) → ℝ) : Prop :=
  u 0 = d₀ ∧ u (Fin.last (N + 1)) = d₁ ∧
    ∀ j : Fin N, equation_12_32 N α γ u j
      = f (FiniteDifference.uniformGrid 0 1 N j.succ.castSucc)

/-- **The matrix (12.34)** `A_fd = h⁻² tridiag(a, d, a) + diag(c)` of the variable-coefficient
scheme. The book's `a = (α_{1/2}, …)` needs a minus sign (see `notes/book-errata.md`). -/
noncomputable def equation_12_34 (N : ℕ) (α γ : ℝ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  FiniteDifference.variableCoeffMatrix 0 1 N α γ

/-- **(12.34) is symmetric positive definite** for `α ≥ α₀ > 0` and `γ ≥ 0`. -/
theorem equation_12_34_posDef (N : ℕ) (α γ : ℝ → ℝ)
    (hα : ∀ j : Fin (N + 1), 0 < α (FiniteDifference.midGrid 0 1 N j))
    (hγ : ∀ i : Fin N, 0 ≤ γ (FiniteDifference.uniformGrid 0 1 N i.succ.castSucc)) :
    (equation_12_34 N α γ).PosDef :=
  FiniteDifference.variableCoeffMatrix_posDef zero_lt_one α γ hα hγ

/-- **(12.34) is strictly diagonally dominant** when `γ > 0` at the nodes. -/
theorem equation_12_34_diagDominant (N : ℕ) (α γ : ℝ → ℝ)
    (hα : ∀ j : Fin (N + 1), 0 ≤ α (FiniteDifference.midGrid 0 1 N j))
    (hγ : ∀ i : Fin N, 0 < γ (FiniteDifference.uniformGrid 0 1 N i.succ.castSucc)) :
    (equation_12_34 N α γ).IsStrictDiagDominant :=
  FiniteDifference.variableCoeffMatrix_isStrictDiagDominant zero_lt_one α γ hα hγ

/-- **The mirror-imaging discretization of a Neumann condition** `J(u)(1) = g₁` at the last node,
(12.35) and the display below it. The book's "second-order accurate" is asserted, not proved, and
is not a node. -/
def equation_12_35 (N : ℕ) (α γ f : ℝ → ℝ) (d₀ g₁ : ℝ) (u : Fin (N + 2) → ℝ) : Prop :=
  FiniteDifference.IsNeumannSolution 0 1 N α γ f d₀ g₁ u

/-- **Exercise 12.10**, referred to at the end of §12.2.3: the Robin conditions
`λ₀ u(0) + μ₀ u'(0) = g₀` and `λ₁ u(1) + μ₁ u'(1) = g₁` discretized by mirror imaging (the book
prints `u(0)` for `u'(0)`; see `notes/book-errata.md`). -/
def exercise_12_10 (N : ℕ) (α γ f : ℝ → ℝ) (lam₀ mu₀ g₀ lam₁ mu₁ g₁ : ℝ)
    (u : Fin (N + 2) → ℝ) : Prop :=
  FiniteDifference.IsRobinSolution 0 1 N α γ f lam₀ mu₀ g₀ lam₁ mu₁ g₁ u

/-- **Exercise 12.11**, referred to in §12.2: the centred discretization of the fourth-order
operator `L u = -u⁗` is `L_h ∘ L_h`, up to the sign — `L_h` approximates `-u''`, so the
composition approximates `u⁗`. -/
noncomputable def exercise_12_11 (N : ℕ) : (Fin (N + 4) → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  (FiniteDifference.discreteLaplacian N (meshSize N)).comp
    (FiniteDifference.discreteLaplacian (N + 2) (meshSize N))

/-- The five-point stencil of `L_h ∘ L_h`:
`(u_{j+2} - 4 u_{j+1} + 6 u_j - 4 u_{j-1} + u_{j-2})/h⁴`. -/
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
