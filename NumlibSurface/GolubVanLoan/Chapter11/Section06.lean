import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Multigrid.Basic
import Numlib.Multigrid.ModelProblem
import NumlibSurface.GolubVanLoan.Chapter11.Section02

/-!
# Golub–Van Loan §11.6: the multigrid framework

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §11.6:
the one-dimensional model problem with its explicit eigen-decomposition ((11.6.2)–(11.6.10)),
weighted Jacobi as a smoother ((11.6.11)–(11.6.12) and the choice `ω = 2/3`), restriction and
prolongation ((11.6.13)–(11.6.15)), the two-grid cycle and its error operator ((11.6.16)–(11.6.19)),
Lemma 11.6.1 and Theorem 11.6.2 with the mode-by-mode damping analysis ((11.6.20)–(11.6.22)).

## Design

The book's analysis is an exact computation in the sine eigenbasis, and so is this file: it works
over the discrete sine vectors `Matrix.sineVec` of `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz`
and the mode identities of `Numlib/Multigrid/ModelProblem` (linear interpolation, full weighting and
the exact coarse-grid correction acting on the fine modes `j`, their aliases `2m − j` and the middle
mode `m`). One bridge connects the section to the abstract two-grid theory of
`Numlib/Multigrid/Basic`: the book's `E^h` is the `A^h`-orthogonal coarse-grid correction
`Multigrid.coarseCorrection` of the prolongation `P^h_{2h}` (`twoGridError_eq_coarseCorrection`).

**Grid sizes.** The book takes `n = 2^k − 1`, `m = 2^{k−1} − 1`, `h = 1/2^k`. Everything it proves
uses only `n = 2m + 1`, so the file is indexed by the coarse size `m`, the fine grid being
`Fin (2 * m + 1)` (the book's case is `m = 2^{k−1} − 1`); a matrix of a grid of `n` points has mesh
width `h = 1/(n + 1)`, so `modelA n` is the book's `A^h` for `n = 2m + 1` and its `A^{2h}` for
`n = m`. Indices are 0-based: the book's `q_j` (`j = 1:n`) is `modelq n (j − 1)`; the fine mode `j`
of the coarse mode `j` is `Multigrid.fineIndex j`, the book's `q_{n−j+1}` is
`Multigrid.aliasIndex j` (0-based `2m − j`), the book's `q_{m+1}` is `Multigrid.middleIndex m`, and
the book's even fine point `2j` is `evenIndex j` (0-based `2j + 1`). The block matrices of (11.6.9),
(11.6.20) and (11.6.21), over `Fin m ⊕ Fin 1 ⊕ Fin m` in the book, are stated entry by entry on
these three kinds of indices; the exchange permutation `ℰ_m` of the book is what turns the book's
block index into `aliasIndex`.

The two-grid cycle (11.6.16) is a program over a rounding hook, built from ch01's gaxpy and §11.2's
`vecSub`; the smoother and the coarse solve are routine arguments (the book delegates both: the
weighted Jacobi iteration to §11.6.2, the coarse system to recursion), whose exact semantics are the
weighted Jacobi step and `(A^{2h})⁻¹`.

## Main results

* `equation_11_6_4` — `Q^h` is orthogonal and diagonalizes `A^h`.
* `equation_11_6_12`, `weightedJacobi_tau_mem`, `weightedJacobi_twoThirds` — weighted Jacobi in the
  sine basis, its convergence and the damping factor `1/3` of `ω = 2/3` on the high frequencies.
* `galerkin_coarse_eq` — `R A^h P = A^{2h}`.
* `equation_11_6_17`, `equation_11_6_19` — the error of the two-grid cycle.
* `lemma_11_6_1`, `theorem_11_6_2`, `equation_11_6_22` — the transfer operators and `E^h` in the
  sine basis.
* `twoGrid_error_coeffs`, `twoGrid_damping_bounds` — the mode-by-mode error of one cycle.

## Not formalized here

The PDE (11.6.1) and the discretization claim, the `n = 7` example matrices (11.6.13) and the
`n = 7` instance of (11.6.21) (which the source prints with a row missing), the V-cycle `mgV`, full
multigrid and §11.6.5 (the text states no property of them beyond flop counts and the heuristic that
the rate is independent of `n`), and the Problems. Errata recorded in the docstrings: (11.6.16)
updates `u_c` instead of `u_{p₁}`; the proof of Theorem 11.6.2 prints the wrong coarse eigenvalue
matrix.
-/

open Matrix Finset
open scoped Matrix

namespace GolubVanLoan.Chapter11

open Multigrid

/-! ### The model problem and its eigen-decomposition -/

/-- **(11.6.3).** `A^h = h⁻² tridiag(−1, 2, −1)` on a grid of `n` interior points, `h = 1/(n + 1)`:
the book's `A^h` for `n = 2^k − 1` and its coarse `A^{2h}` for `n = 2^{k−1} − 1`. -/
noncomputable def modelA (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (((n : ℝ) + 1) ^ 2) • symmTridiagonalToeplitz n (-1) 2

/-- **(11.6.5).** `λ_j^h = (4/h²) sin²(jπ/(2(n + 1)))`, `j = 1:n` (0-based: `j + 1`). -/
noncomputable def modelAEigenvalues (n : ℕ) : Fin n → ℝ := fun j =>
  4 * ((n : ℝ) + 1) ^ 2 * Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) ^ 2

/-- **(11.6.6)**, one column: `q_j = √(2/(n + 1)) (sin θ_j, …, sin nθ_j)ᵀ`, `θ_j = jπ/(n + 1)`. -/
noncomputable def modelq (n : ℕ) (j : Fin n) : Fin n → ℝ :=
  Real.sqrt (2 / ((n : ℝ) + 1)) • sineVec n j

/-- **(11.6.6).** `Q^h = [q_1 ⋯ q_n]`. -/
noncomputable def modelQ (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => modelq n j i

/-- **(11.6.7).** `S^h = diag(s_1², …, s_m²)`, `s_j = sin(jπ/(2(n + 1)))` with `n = 2m + 1`: the
angle is half the fine mode angle `Multigrid.modeAngle m j = (j + 1)π/(2m + 2)`. -/
noncomputable def modelS (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  diagonal fun j => Real.sin (modeAngle m j / 2) ^ 2

/-- **(11.6.8).** `C^h = diag(c_1², …, c_m²)`, `c_j = cos(jπ/(2(n + 1)))`, the twin of `modelS`
(`S^h + C^h = I`). -/
noncomputable def modelC (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  diagonal fun j => Real.cos (modeAngle m j / 2) ^ 2

/-- The columns of `Q^h` are orthonormal. -/
private theorem modelq_dotProduct (n : ℕ) (k l : Fin n) :
    modelq n k ⬝ᵥ modelq n l = if k = l then 1 else 0 := by
  rw [modelq, modelq, smul_dotProduct, dotProduct_smul, dotProduct_sineVec, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, Real.mul_self_sqrt (by positivity)]
  split_ifs
  · field_simp
  · simp

/-- `(Q^h)ᵀ Q^h = I`. -/
theorem modelQ_transpose_mul (n : ℕ) : (modelQ n)ᵀ * modelQ n = 1 := by
  ext k l
  rw [mul_apply, one_apply, ← modelq_dotProduct]
  rfl

/-- `Q^h (Q^h)ᵀ = I`. -/
private theorem modelQ_mul_transpose (n : ℕ) : modelQ n * (modelQ n)ᵀ = 1 :=
  mul_eq_one_comm.1 (modelQ_transpose_mul n)

/-- `Q^h` is nonsingular, with inverse `(Q^h)ᵀ`. -/
private theorem inv_modelQ (n : ℕ) : (modelQ n)⁻¹ = (modelQ n)ᵀ :=
  inv_eq_left_inv (modelQ_transpose_mul n)

/-- `Q^h` is nonsingular. -/
private theorem isUnit_modelQ (n : ℕ) : IsUnit (modelQ n) :=
  (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse (modelQ_transpose_mul n))

/-- Each `q_j` is an eigenvector of `A^h` with eigenvalue `λ_j^h`: the Dirichlet–Dirichlet
eigenpairs of §4.8.6 (`Chapter04.dd_eigen`), scaled. -/
theorem modelA_mulVec_modelq (n : ℕ) (j : Fin n) :
    modelA n *ᵥ modelq n j = modelAEigenvalues n j • modelq n j := by
  have h := (GolubVanLoan.Chapter04.dd_eigen n).1 j
  rw [show (fun k => dst1 n k j) = sineVec n j from funext fun k => dst1_apply_eq_sineVec k j]
    at h
  rw [modelA, modelq, smul_mulVec, mulVec_smul, h, smul_smul, smul_smul, smul_smul,
    modelAEigenvalues]
  congr 1
  ring

/-- `A^h Q^h = Q^h Λ^h`. -/
private theorem modelA_mul_modelQ (n : ℕ) :
    modelA n * modelQ n = modelQ n * diagonal (modelAEigenvalues n) := by
  ext i j
  rw [mul_diagonal]
  change (modelA n *ᵥ modelq n j) i = modelq n j i * _
  rw [modelA_mulVec_modelq, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **(11.6.4).** `A^h` has the known Schur decomposition `(Q^h)ᵀ A^h Q^h = Λ^h = diag(λ^h)`, with
`Q^h` orthogonal. -/
theorem equation_11_6_4 (n : ℕ) :
    (modelQ n)ᵀ * modelQ n = 1 ∧
      (modelQ n)ᵀ * modelA n * modelQ n = diagonal (modelAEigenvalues n) := by
  refine ⟨modelQ_transpose_mul n, ?_⟩
  rw [Matrix.mul_assoc, modelA_mul_modelQ, ← Matrix.mul_assoc, modelQ_transpose_mul,
    Matrix.one_mul]

/-- `√(2/(n + 1)) = √(2/(m + 1))/√2` for `n = 2m + 1`: the normalizations of the fine and coarse
sine bases. -/
private theorem sqrt_fine (m : ℕ) :
    Real.sqrt (2 / (((2 * m + 1 : ℕ) : ℝ) + 1)) = Real.sqrt (2 / ((m : ℝ) + 1)) / Real.sqrt 2 := by
  rw [eq_div_iff (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  push_cast
  field_simp
  ring

/-- **(11.6.9).** `Λ^h = (4/h²) diag(S^h, 1/2, ℰ_m C^h ℰ_m)`, entry by entry: at the fine mode `j`
the eigenvalue is `(4/h²) s_j²`, at the middle mode `(4/h²)/2`, and at the alias `n − j + 1`
(0-based `2m − j`) it is `(4/h²) c_j²` (`h = 1/(n + 1)`, `n = 2m + 1`; the book's P11.6.1). -/
theorem equation_11_6_9 (m : ℕ) (j : Fin m) :
    modelAEigenvalues (2 * m + 1) (fineIndex j) =
        4 * (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2 * modelS m j j ∧
      modelAEigenvalues (2 * m + 1) (middleIndex m) =
        4 * (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2 * (1 / 2) ∧
      modelAEigenvalues (2 * m + 1) (aliasIndex j) =
        4 * (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2 * modelC m j j := by
  have hj : (j : ℕ) ≤ 2 * m := by have := j.isLt; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [modelAEigenvalues, modelS, diagonal_apply_eq]
    congr 3
    rw [fineIndex, modeAngle]
    push_cast
    field_simp
    ring
  · rw [modelAEigenvalues]
    have e : (((middleIndex m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
        Real.pi / 4 := by
      rw [middleIndex]
      push_cast
      field_simp
      ring
    rw [e, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
    ring
  · rw [modelAEigenvalues, modelC, diagonal_apply_eq]
    have e : (((aliasIndex j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
        Real.pi / 2 - modeAngle m j / 2 := by
      rw [aliasIndex, Fin.val_mk, Nat.cast_sub hj, modeAngle]
      push_cast
      field_simp
      ring
    rw [e, Real.sin_pi_div_two_sub]

/-- The fine grid point of the coarse point `j` (the book's even fine point `2j`, 0-based
`2j + 1`). -/
def evenIndex {m : ℕ} (j : Fin m) : Fin (2 * m + 1) := ⟨2 * j + 1, by omega⟩

/-- **(11.6.10).** The even rows of `Q^h` are scaled copies of `Q^{2h}`:
`Q^h(2:2:2m, :) = [Q^{2h} | 0 | −Q^{2h}ℰ_m]/√2`, entry by entry on the fine modes, the middle mode
and the aliases (the book's P11.6.1). -/
theorem equation_11_6_10 (m : ℕ) (q l : Fin m) :
    modelQ (2 * m + 1) (evenIndex q) (fineIndex l) = modelQ m q l / Real.sqrt 2 ∧
      modelQ (2 * m + 1) (evenIndex q) (middleIndex m) = 0 ∧
      modelQ (2 * m + 1) (evenIndex q) (aliasIndex l) = -modelQ m q l / Real.sqrt 2 := by
  have hfine : sineVec (2 * m + 1) (fineIndex l) (evenIndex q) = sineVec m l q := by
    rw [sineVec_fineIndex, sineVec_coarse, evenIndex]
    congr 1
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [modelQ, of_apply, modelq, Pi.smul_apply, smul_eq_mul, hfine, sqrt_fine]
    ring
  · simp only [modelQ, of_apply, modelq, Pi.smul_apply, smul_eq_mul, sineVec_middleIndex,
      evenIndex]
    have e : ((((2 * (q : ℕ) + 1 : ℕ) : ℕ) : ℝ) + 1) * (Real.pi / 2) =
        (((q : ℕ) + 1 : ℕ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [e, Real.sin_nat_mul_pi, mul_zero]
  · have hsign : (-1 : ℝ) ^ ((evenIndex q : Fin (2 * m + 1)) : ℕ) = -1 := by
      rw [evenIndex]
      dsimp only
      rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    simp only [modelQ, of_apply, modelq, Pi.smul_apply, smul_eq_mul, sineVec_aliasIndex, hsign,
      hfine, sqrt_fine]
    ring

/-! ### Weighted Jacobi as a smoother -/

/-- The diagonal of `A^h` is `(2/h²) I`. -/
private theorem diagPart_modelA (n : ℕ) :
    diagPart (modelA n) = (2 * ((n : ℝ) + 1) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  rw [diagPart_apply, Matrix.smul_apply, one_apply]
  split_ifs with h
  · subst h
    rw [modelA, Matrix.smul_apply, symmTridiagonalToeplitz_apply_self, smul_eq_mul, smul_eq_mul]
    ring
  · simp

/-- The diagonal of `A^h` is nonsingular. -/
theorem isUnit_diagPart_modelA (n : ℕ) : IsUnit (diagPart (modelA n)) := by
  rw [isUnit_diagPart_iff]
  intro i
  have := congrFun (congrFun (diagPart_modelA n) i) i
  rw [diagPart_apply, ite_eq_left rfl, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
    mul_one] at this
  rw [this]
  positivity

/-- `(c B)⁻¹ = c⁻¹ B⁻¹` for `c ≠ 0` and `B` nonsingular. -/
private theorem inv_smul_of_isUnit' {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : c ≠ 0)
    {B : Matrix ι ι ℝ} (hB : IsUnit B) : (c • B)⁻¹ = c⁻¹ • B⁻¹ :=
  inv_eq_left_inv (by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hB), one_smul])

/-- **(11.6.11).** The weighted Jacobi iteration `u⁽ᵏ⁾ = G u⁽ᵏ⁻¹⁾ + c`,
`G = (1 − ω)I − ωD⁻¹(L + U)`, `c = ωD⁻¹b`, is the iteration of the splitting `M = ω⁻¹D`
(`Matrix.jorSplitting`) for any `A` with nonsingular diagonal; and for the model matrix
`G^{h,ω} = I − (ωh²/2) A^h` (`h = 1/(n + 1)`). -/
theorem equation_11_6_11 {n : ℕ} {ω : ℝ} (hω : ω ≠ 0) :
    (∀ (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (diagPart A)) (b u : Fin n → ℝ),
      (jorSplitting A h hω).mulVecStep b u =
        ((1 - ω) • 1 - ω • ((diagPart A)⁻¹ * (strictLower A + strictUpper A))) *ᵥ u +
          (ω • (diagPart A)⁻¹) *ᵥ b) ∧
      (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator =
        1 - (ω * (1 / ((n : ℝ) + 1)) ^ 2 / 2) • modelA n := by
  refine ⟨fun A h b u => ?_, ?_⟩
  · have hm : (jorSplitting A h hω).m = ω⁻¹ • diagPart A := rfl
    rw [Stationary.Splitting.mulVecStep_eq_iterationOperator_mulVec_add,
      jorSplitting_iterationOperator, jacobiSplitting_iterationOperator, hm,
      inv_smul_of_isUnit' (inv_ne_zero hω) h, inv_inv]
    congr 2
    rw [neg_mul, smul_neg, ← sub_eq_add_neg]
  · rw [jorSplitting_iterationOperator_eq_one_sub, diagPart_modelA,
      inv_smul_of_isUnit' (by positivity) isUnit_one, inv_one, smul_mul, Matrix.one_mul, smul_smul]
    congr 2
    field_simp

/-- The eigenvalues `τ_j^{h,ω} = 1 − 2ω sin²(jπ/(2(n + 1)))` of `G^{h,ω}`, `j = 1:n` (0-based). -/
noncomputable def weightedJacobiTau (n : ℕ) (ω : ℝ) : Fin n → ℝ := fun j =>
  1 - 2 * ω * Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) ^ 2

/-- `G^{h,ω} Q^h = Q^h diag(τ^{h,ω})`. -/
private theorem weightedJacobi_mul_modelQ (n : ℕ) {ω : ℝ} (hω : ω ≠ 0) :
    (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator * modelQ n =
      modelQ n * diagonal (weightedJacobiTau n ω) := by
  rw [(equation_11_6_11 hω).2, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    modelA_mul_modelQ]
  have hd : diagonal (weightedJacobiTau n ω) =
      1 - (ω * (1 / ((n : ℝ) + 1)) ^ 2 / 2) • diagonal (modelAEigenvalues n) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [diagonal_apply_eq, Matrix.sub_apply, one_apply_eq, Matrix.smul_apply, smul_eq_mul,
        weightedJacobiTau, modelAEigenvalues]
      field_simp
      ring
    · simp [h, one_apply_ne h]
  rw [hd, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]

/-- `(G^{h,ω})^p Q^h = Q^h diag(τ^{h,ω})^p`. -/
private theorem weightedJacobi_pow_mul_modelQ (n : ℕ) {ω : ℝ} (hω : ω ≠ 0) (p : ℕ) :
    (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator ^ p * modelQ n =
      modelQ n * diagonal fun j => weightedJacobiTau n ω j ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, weightedJacobi_mul_modelQ n hω,
      Matrix.mul_assoc, diagonal_mul_diagonal]
    congr 2
    funext j
    ring

/-- `(G^{h,ω})^p (Q^h v) = Q^h (τ^p ⊙ v)`: weighted Jacobi damps the sine coefficient `j` by
`τ_j^{h,ω}` per step. -/
private theorem weightedJacobi_pow_mulVec_modelQ (n : ℕ) {ω : ℝ} (hω : ω ≠ 0) (p : ℕ)
    (v : Fin n → ℝ) :
    (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator ^ p *ᵥ
        (modelQ n *ᵥ v) = modelQ n *ᵥ fun j => weightedJacobiTau n ω j ^ p * v j := by
  rw [mulVec_mulVec, weightedJacobi_pow_mul_modelQ, ← mulVec_mulVec]
  congr 1
  funext j
  exact mulVec_diagonal _ _ j

/-- **(11.6.12).** `(Q^h)ᵀ G^{h,ω} Q^h = diag(τ^{h,ω})`, `τ_j^{h,ω} = 1 − 2ω sin²(jπ/(2(n + 1)))`;
hence the error expansion after (11.6.12): if `u₀ − u = ∑_j α_j q_j` then
`u_p − u = (G^{h,ω})^p (u₀ − u) = ∑_j α_j (τ_j^{h,ω})^p q_j`, for the iterates `u_p` of weighted
Jacobi applied to `A^h u = b`. -/
theorem equation_11_6_12 (n : ℕ) {ω : ℝ} (hω : ω ≠ 0) :
    (modelQ n)ᵀ * (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator *
        modelQ n = diagonal (weightedJacobiTau n ω) ∧
      ∀ (b u u₀ α : Fin n → ℝ), modelA n *ᵥ u = b → u₀ - u = modelQ n *ᵥ α → ∀ p : ℕ,
        ((jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).mulVecStep b)^[p] u₀ - u =
          modelQ n *ᵥ fun j => weightedJacobiTau n ω j ^ p * α j := by
  refine ⟨by rw [Matrix.mul_assoc, weightedJacobi_mul_modelQ n hω, ← Matrix.mul_assoc,
    modelQ_transpose_mul, Matrix.one_mul], fun b u u₀ α hu hα p => ?_⟩
  rw [equation_11_2_7 _ hu, hα, weightedJacobi_pow_mulVec_modelQ]

/-- `0 < jπ/(2(n + 1)) < π/2` for `j = 1:n`. -/
private theorem halfAngle_mem (n : ℕ) (j : Fin n) :
    0 < (((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1)) ∧
      (((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1)) < Real.pi / 2 := by
  have hj : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
  refine ⟨by positivity, ?_⟩
  rw [div_lt_div_iff₀ (by positivity) two_pos]
  nlinarith [Real.pi_pos]

/-- `0 < s < 1` for `s = sin(jπ/(2(n + 1)))`. -/
private theorem sin_halfAngle_mem (n : ℕ) (j : Fin n) :
    0 < Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) ∧
      Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) < 1 := by
  obtain ⟨h0, h1⟩ := halfAngle_mem n j
  refine ⟨Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos]), ?_⟩
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl h1
  rwa [Real.sin_pi_div_two] at h

/-- The spectral radius of a real diagonal matrix whose entries lie in `(−1, 1)` is below `1`. -/
private theorem complexSpectralRadius_diagonal_lt_one {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i, |d i| < 1) : (diagonal d).complexSpectralRadius < 1 := by
  rw [complexSpectralRadius_diagonal]
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · rw [iSup_of_empty]
    exact zero_lt_one
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖d i‖₊
    refine lt_of_le_of_lt (iSup_le fun i => ENNReal.coe_le_coe.2 (hi₀ i)) ?_
    rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    exact hd i₀

/-- **§11.6.2.** For `0 < ω ≤ 1`, `−1 < τ_n < ⋯ < τ_1 < 1` (the `τ_j^{h,ω}` strictly decrease in
`j`), hence `ρ(G^{h,ω}) < 1`. -/
theorem weightedJacobi_tau_mem (n : ℕ) {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) :
    StrictAnti (weightedJacobiTau n ω) ∧ (∀ j, -1 < weightedJacobiTau n ω j ∧
      weightedJacobiTau n ω j < 1) ∧
      Matrix.complexSpectralRadius
        (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω0.ne').iterationOperator < 1 := by
  have hmem : ∀ j, -1 < weightedJacobiTau n ω j ∧ weightedJacobiTau n ω j < 1 := fun j => by
    obtain ⟨h0, h1⟩ := sin_halfAngle_mem n j
    have hs0 := pow_pos h0 2
    have hs1 : Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) ^ 2 < 1 := by
      nlinarith
    simp only [weightedJacobiTau]
    constructor <;> nlinarith
  refine ⟨fun j k hjk => ?_, hmem, ?_⟩
  · simp only [weightedJacobiTau]
    have hs : Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) <
        Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) := by
      refine Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [(halfAngle_mem n j).1, Real.pi_pos])
        (halfAngle_mem n k).2.le ?_
      have hjk' : ((j : ℕ) : ℝ) < (k : ℕ) := by exact_mod_cast hjk
      exact div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) (by positivity)
    have := pow_lt_pow_left₀ hs (sin_halfAngle_mem n j).1.le two_ne_zero
    nlinarith
  · rw [← complexSpectralRadius_conj (isUnit_modelQ n), inv_modelQ,
      (equation_11_6_12 n hω0.ne').1]
    exact complexSpectralRadius_diagonal_lt_one _ fun j => abs_lt.2 (hmem j)

/-- The high-frequency part of a vector of sine coefficients: the components `j ≥ m + 1` of the book
(0-based `j ≥ m`). -/
def highPart {m : ℕ} (v : Fin (2 * m + 1) → ℝ) : Fin (2 * m + 1) → ℝ :=
  fun j => if m ≤ (j : ℕ) then v j else 0

/-- `‖Q v‖₂ = ‖v‖₂` for the orthogonal `Q^h`. -/
private theorem norm_modelQ_mulVec (n : ℕ) (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 (modelQ n *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  have h : ‖WithLp.toLp 2 (modelQ n *ᵥ v)‖ ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp,
      EuclideanSpace.inner_toLp_toLp, star_trivial, star_trivial, dotProduct_mulVec,
      ← mulVec_transpose, mulVec_mulVec, modelQ_transpose_mul, one_mulVec]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- On the high frequencies `j ≥ m + 1` (0-based `j ≥ m`) of the fine grid, `1/2 ≤ s² < 1` for
`s = sin(jπ/(2(n + 1)))`. -/
private theorem sin_sq_high_mem (m : ℕ) (j : Fin (2 * m + 1)) (hj : m ≤ (j : ℕ)) :
    1 / 2 ≤ Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2 ∧
      Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2 < 1 := by
  obtain ⟨h0, h1⟩ := sin_halfAngle_mem (2 * m + 1) j
  have hq : Real.pi / 4 ≤ (((j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) := by
    have hj' : (m : ℝ) ≤ (j : ℕ) := by exact_mod_cast hj
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    push_cast
    nlinarith [Real.pi_pos]
  have hs : Real.sqrt 2 / 2 ≤
      Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) := by
    rw [← Real.sin_pi_div_four]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (halfAngle_mem (2 * m + 1) j).2.le hq
  refine ⟨?_, by nlinarith⟩
  have := pow_le_pow_left₀ (by positivity) hs 2
  rw [div_pow, Real.sq_sqrt (by norm_num)] at this
  linarith

/-- `τ_{m+1}^{h,ω} = 1 − ω`: the middle mode has `s² = sin²(π/4) = 1/2`. -/
private theorem weightedJacobiTau_middleIndex (m : ℕ) (ω : ℝ) :
    weightedJacobiTau (2 * m + 1) ω (middleIndex m) = 1 - ω := by
  have e : (((middleIndex m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
      Real.pi / 4 := by
    rw [middleIndex]
    push_cast
    field_simp
    ring
  simp only [weightedJacobiTau]
  rw [e, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  ring

/-- **§11.6.2, the choice `ω = 2/3`.** The high-frequency damping factor is `1/3`:
`|τ_j^{h,2/3}| ≤ 1/3` for every high frequency `j ≥ m + 1`, with equality at `j = m + 1`; so the
high-frequency error components after `p` weighted Jacobi steps are at most `(1/3)^p` times the
initial ones, `‖P_high(u_p − u)‖₂ ≤ (1/3)^p ‖P_high(u₀ − u)‖₂`, where `u₀ − u = Q^h α`,
`u_p − u = Q^h(τ^p α)` (`equation_11_6_12`) and `P_high` keeps the components `j ≥ m + 1`. -/
theorem weightedJacobi_twoThirds (m : ℕ) :
    (∀ j : Fin (2 * m + 1), m ≤ (j : ℕ) → |weightedJacobiTau (2 * m + 1) (2 / 3) j| ≤ 1 / 3) ∧
      weightedJacobiTau (2 * m + 1) (2 / 3) (middleIndex m) = 1 / 3 ∧
      ∀ (p : ℕ) (α : Fin (2 * m + 1) → ℝ),
        ‖WithLp.toLp 2 (modelQ (2 * m + 1) *ᵥ
            highPart fun j => weightedJacobiTau (2 * m + 1) (2 / 3) j ^ p * α j)‖ ≤
          (1 / 3) ^ p * ‖WithLp.toLp 2 (modelQ (2 * m + 1) *ᵥ highPart α)‖ := by
  have hhigh : ∀ j : Fin (2 * m + 1), m ≤ (j : ℕ) →
      |weightedJacobiTau (2 * m + 1) (2 / 3) j| ≤ 1 / 3 := by
    intro j hj
    obtain ⟨hs2, hs1⟩ := sin_sq_high_mem m j hj
    simp only [weightedJacobiTau]
    rw [abs_le]
    constructor <;> nlinarith
  have hmid : weightedJacobiTau (2 * m + 1) (2 / 3) (middleIndex m) = 1 / 3 := by
    rw [weightedJacobiTau_middleIndex]
    norm_num
  refine ⟨hhigh, hmid, fun p α => ?_⟩
  rw [norm_modelQ_mulVec, norm_modelQ_mulVec]
  have hnorm : ∀ v : Fin (2 * m + 1) → ℝ, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i * v i := fun v => by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
    rfl
  have hsq : ‖WithLp.toLp 2 (highPart fun j => weightedJacobiTau (2 * m + 1) (2 / 3) j ^ p * α j)‖
      ^ 2 ≤ ((1 / 3) ^ p * ‖WithLp.toLp 2 (highPart α)‖) ^ 2 := by
    rw [mul_pow, hnorm, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [highPart]
    split_ifs with hj
    · set τ := weightedJacobiTau (2 * m + 1) (2 / 3) j
      have hτ : τ * τ ≤ 1 / 3 * (1 / 3) := by
        have := hhigh j hj
        rw [abs_le] at this
        nlinarith
      have hp : (τ * τ) ^ p ≤ (1 / 3 * (1 / 3)) ^ p :=
        pow_le_pow_left₀ (mul_self_nonneg τ) hτ p
      calc τ ^ p * α j * (τ ^ p * α j) = (τ * τ) ^ p * (α j * α j) := by rw [mul_pow]; ring
        _ ≤ (1 / 3 * (1 / 3)) ^ p * (α j * α j) :=
          mul_le_mul_of_nonneg_right hp (mul_self_nonneg _)
        _ = ((1 / 3) ^ p) ^ 2 * (α j * α j) := by rw [mul_pow, sq]
    · simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- The high-frequency damping factor `μ(ω) = max{|τ_{m+1}^{h,ω}|, …, |τ_n^{h,ω}|}` of §11.6.2
(0-based: the modes `j ≥ m`). -/
noncomputable def highFreqDamping (m : ℕ) (ω : ℝ) : ℝ :=
  (Finset.univ.filter fun j : Fin (2 * m + 1) => m ≤ (j : ℕ)).sup'
    ⟨middleIndex m, by simp [middleIndex]⟩ fun j => |weightedJacobiTau (2 * m + 1) ω j|

/-- The minimizer `ω* = 2/(1 + 2s_n²)` of the high-frequency damping factor,
`s_n = sin(nπ/(2(n+1)))`, `n = 2m + 1`. -/
noncomputable def optimalOmega (m : ℕ) : ℝ :=
  2 / (1 + 2 * Real.sin ((((2 * m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2)

/-- **§11.6.2, the rigorous version of "this is essentially solved by `ω_opt = 2/3`".** With
`a = s_n²`: for `0 < ω ≤ 1`, `μ(ω) = max(|1 − ω|, |1 − 2ωa|)` (`τ` decreases in `j`,
`τ_{m+1} = 1 − ω`, `τ_n = 1 − 2ωa`); the value `ω* = 2/(1 + 2a)` lies in `(0, 1]`, makes
`τ_{m+1} = −τ_n` (the book's equation), minimizes `μ` over `(0, 1]` with
`μ(ω*) = (2a − 1)/(2a + 1) < 1/3`; and `ω* → 2/3` as the grid is refined (`s_n → 1`). -/
theorem weightedJacobi_optimalOmega :
    (∀ m : ℕ,
      let a := Real.sin ((((2 * m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2
      (∀ ω, 0 < ω → ω ≤ 1 → highFreqDamping m ω = max |1 - ω| |1 - 2 * ω * a|) ∧
      (0 < optimalOmega m ∧ optimalOmega m ≤ 1) ∧
      weightedJacobiTau (2 * m + 1) (optimalOmega m) (middleIndex m) =
        -weightedJacobiTau (2 * m + 1) (optimalOmega m) ⟨2 * m, by omega⟩ ∧
      highFreqDamping m (optimalOmega m) = (2 * a - 1) / (2 * a + 1) ∧
      (∀ ω, 0 < ω → ω ≤ 1 → highFreqDamping m (optimalOmega m) ≤ highFreqDamping m ω) ∧
      (2 * a - 1) / (2 * a + 1) < 1 / 3) ∧
    Filter.Tendsto optimalOmega Filter.atTop (nhds (2 / 3)) := by
  refine ⟨fun m => ?_, ?_⟩
  · intro a
    obtain ⟨ha1, ha2⟩ : 1 / 2 ≤ a ∧ a < 1 := sin_sq_high_mem m ⟨2 * m, by omega⟩
      (by change m ≤ 2 * m; omega)
    have hlast : ∀ ω, weightedJacobiTau (2 * m + 1) ω ⟨2 * m, by omega⟩ = 1 - 2 * ω * a :=
      fun ω => rfl
    have hμ : ∀ ω, 0 < ω → ω ≤ 1 → highFreqDamping m ω = max |1 - ω| |1 - 2 * ω * a| := by
      intro ω hω0 hω1
      have hanti := (weightedJacobi_tau_mem (2 * m + 1) hω0 hω1).1.antitone
      have hmem : ∀ j ∈ (Finset.univ.filter fun j : Fin (2 * m + 1) => m ≤ (j : ℕ)),
          |weightedJacobiTau (2 * m + 1) ω j| ≤ max |1 - ω| |1 - 2 * ω * a| := by
        intro j hj
        have hj' : m ≤ (j : ℕ) := (Finset.mem_filter.1 hj).2
        have hup : weightedJacobiTau (2 * m + 1) ω j ≤ 1 - ω := by
          rw [← weightedJacobiTau_middleIndex m ω]
          exact hanti (show middleIndex m ≤ j from hj')
        have hlo : 1 - 2 * ω * a ≤ weightedJacobiTau (2 * m + 1) ω j := by
          rw [← hlast ω]
          exact hanti (show j ≤ ⟨2 * m, by omega⟩ from by
            change (j : ℕ) ≤ 2 * m
            have := j.isLt
            omega)
        rw [abs_le]
        constructor
        · have := neg_abs_le (1 - 2 * ω * a)
          have := le_max_right |1 - ω| |1 - 2 * ω * a|
          linarith
        · have := le_abs_self (1 - ω)
          have := le_max_left |1 - ω| |1 - 2 * ω * a|
          linarith
      refine le_antisymm (Finset.sup'_le _ _ hmem) (max_le ?_ ?_)
      · rw [← weightedJacobiTau_middleIndex m ω]
        exact Finset.le_sup' (fun j => |weightedJacobiTau (2 * m + 1) ω j|)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [middleIndex]⟩)
      · rw [← hlast ω]
        exact Finset.le_sup' (fun j => |weightedJacobiTau (2 * m + 1) ω j|)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, by change m ≤ 2 * m; omega⟩)
    have hω : optimalOmega m = 2 / (1 + 2 * a) := rfl
    have hpos : 0 < 1 + 2 * a := by linarith
    have hω0 : 0 < optimalOmega m := by rw [hω]; positivity
    have hω1 : optimalOmega m ≤ 1 := by rw [hω, div_le_one hpos]; linarith
    have e1 : 1 - optimalOmega m = (2 * a - 1) / (2 * a + 1) := by
      rw [hω]; field_simp; ring
    have e2 : 1 - 2 * optimalOmega m * a = -((2 * a - 1) / (2 * a + 1)) := by
      rw [hω]; field_simp; ring
    have hnn : 0 ≤ (2 * a - 1) / (2 * a + 1) := div_nonneg (by linarith) (by linarith)
    have hval : highFreqDamping m (optimalOmega m) = (2 * a - 1) / (2 * a + 1) := by
      rw [hμ _ hω0 hω1, e1, e2, abs_neg, abs_of_nonneg hnn, max_self]
    refine ⟨hμ, ⟨hω0, hω1⟩, ?_, hval, fun ω h0 h1 => ?_, ?_⟩
    · rw [weightedJacobiTau_middleIndex, hlast, e1, e2, neg_neg]
    · rw [hval, hμ ω h0 h1]
      by_cases hle : ω ≤ optimalOmega m
      · refine le_trans ?_ (le_max_left _ _)
        rw [← e1]
        exact le_trans (by linarith) (le_abs_self _)
      · refine le_trans ?_ (le_max_right _ _)
        have hωa : optimalOmega m * a ≤ ω * a :=
          mul_le_mul_of_nonneg_right (le_of_not_ge hle) (by linarith)
        have : -(1 - 2 * optimalOmega m * a) ≤ -(1 - 2 * ω * a) := by linarith
        rw [e2, neg_neg] at this
        exact this.trans (neg_le_abs _)
    · rw [div_lt_iff₀ (by linarith)]
      linarith
  · have hang : ∀ m : ℕ, (((2 * m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
        Real.pi / 2 - Real.pi / 4 * (1 / ((m : ℝ) + 1)) := fun m => by
      push_cast
      field_simp
      ring
    have h1 : Filter.Tendsto (fun m : ℕ => Real.pi / 2 - Real.pi / 4 * (1 / ((m : ℝ) + 1)))
        Filter.atTop (nhds (Real.pi / 2 - Real.pi / 4 * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [mul_zero, sub_zero] at h1
    have h2 := ((Real.continuous_sin.pow 2).tendsto (Real.pi / 2)).comp h1
    simp only [Pi.pow_apply, Real.sin_pi_div_two, one_pow] at h2
    have h3 := (tendsto_const_nhds (x := (2 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := (2 : ℝ))).mul h2))
      (by norm_num)
    rw [show (2 : ℝ) / (1 + 2 * 1) = 2 / 3 by norm_num] at h3
    refine h3.congr fun m => ?_
    simp only [optimalOmega, Function.comp_apply, Pi.pow_apply, Pi.div_apply, hang]

/-! ### Restriction and prolongation -/

/-- **(11.6.15).** `B^h = 4I_n − h²A^h` (`= tridiag(1, 2, 1)`), `h = 1/(n + 1)`. -/
noncomputable def modelB (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (4 : ℝ) • 1 - (1 / ((n : ℝ) + 1)) ^ 2 • modelA n

/-- `B^h = tridiag(1, 2, 1)`. -/
private theorem modelB_eq (n : ℕ) : modelB n = symmTridiagonalToeplitz n 1 2 := by
  ext i j
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [modelB, modelA, Matrix.sub_apply, Matrix.smul_apply, one_apply, smul_eq_mul,
    symmTridiagonalToeplitz_apply]
  split_ifs <;> field_simp <;> ring

/-- **(11.6.14), the restriction** `R^{2h}_h = ¼ B^h(2:2:2m, :)`. It is the backbone's full
weighting (`restrictionMatrix_eq`). -/
noncomputable def restrictionMatrix (m : ℕ) : Matrix (Fin m) (Fin (2 * m + 1)) ℝ :=
  (1 / 4 : ℝ) • (modelB (2 * m + 1)).submatrix evenIndex id

/-- **(11.6.14), the prolongation** `P^h_{2h} = ½ B^h(:, 2:2:2m)`, the twin of `restrictionMatrix`.
It is the backbone's linear interpolation (`prolongationMatrix_eq`). -/
noncomputable def prolongationMatrix (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin m) ℝ :=
  (1 / 2 : ℝ) • (modelB (2 * m + 1)).submatrix id evenIndex

/-- The restriction of (11.6.14) is full weighting. -/
theorem restrictionMatrix_eq (m : ℕ) : restrictionMatrix m = fullWeighting m := by
  ext q i
  rw [restrictionMatrix, Matrix.smul_apply, submatrix_apply, modelB_eq,
    symmTridiagonalToeplitz_apply',
    fullWeighting_apply, evenIndex, id, smul_eq_mul]
  dsimp only
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- The prolongation of (11.6.14) is linear interpolation. -/
theorem prolongationMatrix_eq (m : ℕ) : prolongationMatrix m = linearInterpolation m := by
  ext i q
  rw [prolongationMatrix, Matrix.smul_apply, submatrix_apply, modelB_eq,
    symmTridiagonalToeplitz_apply',
    linearInterpolation_apply, evenIndex, id, smul_eq_mul]
  dsimp only
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- `R = ½ Pᵀ`. -/
theorem restrictionMatrix_eq_half_transpose (m : ℕ) :
    restrictionMatrix m = (1 / 2 : ℝ) • (prolongationMatrix m)ᵀ := by
  rw [restrictionMatrix_eq, prolongationMatrix_eq]
  rfl

/-- **§11.6.3, the action of the transfer operators.** Restriction is the weighted average
`(R u)_i = (u_{2i−1} + 2u_{2i} + u_{2i+1})/4` around each even fine point (0-based: the fine points
`2i, 2i + 1, 2i + 2` around `evenIndex i`); prolongation copies the coarse values at the even fine
points, `(P v)_{2i} = v_i`, and averages them in between, `(P v)_{2i+1} = (v_i + v_{i+1})/2` with
the boundary values `v_0 = v_{m+1} = 0` (0-based: the fine point `2q` gets the average of the coarse
values `q − 1` and `q`, a missing one counting as `0`); and `R = ½ Pᵀ`. -/
theorem restriction_prolongation_apply (m : ℕ) :
    (∀ (u : Fin (2 * m + 1) → ℝ) (i : Fin m), (restrictionMatrix m *ᵥ u) i =
      (u ⟨2 * i, by omega⟩ + 2 * u (evenIndex i) + u ⟨2 * i + 2, by omega⟩) / 4) ∧
    (∀ (v : Fin m → ℝ) (i : Fin m), (prolongationMatrix m *ᵥ v) (evenIndex i) = v i) ∧
    (∀ (v : Fin m → ℝ) (q : ℕ) (hq : q ≤ m), (prolongationMatrix m *ᵥ v) ⟨2 * q, by omega⟩ =
      ((if h : 0 < q then v ⟨q - 1, by omega⟩ else 0) + (if h : q < m then v ⟨q, h⟩ else 0)) / 2) ∧
    restrictionMatrix m = (1 / 2 : ℝ) • (prolongationMatrix m)ᵀ := by
  refine ⟨fun u i => ?_, fun v i => ?_, fun v q hq => ?_, restrictionMatrix_eq_half_transpose m⟩
  · rw [restrictionMatrix_eq, fullWeighting_mulVec_apply]
    rfl
  · rw [prolongationMatrix_eq, mulVec, dotProduct, Finset.sum_eq_single i]
    · rw [linearInterpolation_apply, evenIndex, ite_eq_left rfl, one_mul]
    · intro j _ hji
      rw [linearInterpolation_apply, evenIndex]
      dsimp only
      have : (i : ℕ) ≠ j := fun h => hji (Fin.ext h.symm)
      split_ifs <;> first | (exfalso; omega) | simp
    · simp
  · simp only [prolongationMatrix_eq, mulVec, dotProduct]
    have hL : ∀ j : Fin m, linearInterpolation m ⟨2 * q, by omega⟩ j * v j =
        (if (j : ℕ) + 1 = q then v j / 2 else 0) + (if (j : ℕ) = q then v j / 2 else 0) := by
      intro j
      rw [linearInterpolation_apply]
      dsimp only
      split_ifs <;> first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl fun (j : Fin m) (_ : j ∈ Finset.univ) => hL j,
      Finset.sum_add_distrib, add_div]
    congr 1
    · split_ifs with h
      · rw [Finset.sum_eq_single ⟨q - 1, by omega⟩]
        · simp only [show q - 1 + 1 = q by omega, ite_true]
        · intro j _ hj
          refine ite_eq_right fun h' => hj (Fin.ext ?_)
          dsimp only
          omega
        · simp
      · rw [zero_div]
        refine Finset.sum_eq_zero fun j _ => ite_eq_right fun h' => ?_
        omega
    · split_ifs with h
      · rw [Finset.sum_eq_single ⟨q, h⟩]
        · simp
        · intro j _ hj
          exact ite_eq_right fun h' => hj (Fin.ext h')
        · simp
      · rw [zero_div]
        refine Finset.sum_eq_zero fun j _ => ite_eq_right fun h' => ?_
        have := j.isLt
        omega

/-- **The coarse matrix is the Galerkin product of the fine one**, `R^{2h}_h A^h P^h_{2h} = A^{2h}`
(not stated by the book, but it is what makes `E^h` a projector and connects §11.6 to the backbone).
-/
theorem galerkin_coarse_eq (m : ℕ) :
    restrictionMatrix m * modelA (2 * m + 1) * prolongationMatrix m = modelA m := by
  rw [restrictionMatrix_eq, prolongationMatrix_eq, modelA, modelA, Matrix.mul_smul,
    Matrix.smul_mul, fullWeighting_mul_mul_linearInterpolation, smul_smul]
  congr 1
  push_cast
  ring

/-! ### The two-grid cycle -/

/-- **(11.6.18).** The two-grid error operator `E^h = I_n − P^h_{2h} (A^{2h})⁻¹ R^{2h}_h A^h`. -/
noncomputable def twoGridErrorOperator (m : ℕ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  1 - prolongationMatrix m * (modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)

/-- The book's `E^h` is the backbone's exact coarse-grid correction of the model problem. -/
private theorem twoGridErrorOperator_eq (m : ℕ) :
    twoGridErrorOperator m = modelCoarseCorrection m := by
  have hT : IsUnit (symmTridiagonalToeplitz m (-1) 2) :=
    (posDef_symmTridiagonalToeplitz_neg_one_two m).isUnit
  rw [twoGridErrorOperator, modelCoarseCorrection, restrictionMatrix_eq, prolongationMatrix_eq,
    modelA, modelA, inv_smul_of_isUnit' (by positivity) hT]
  congr 1
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  push_cast
  field_simp
  ring

/-- `u ← u + z` entrywise, one rounded sum per entry (Step 5 of (11.6.16)). -/
def vecAdd {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n : ℕ} (u z : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun w i => do pure (Function.update w i (← rnd (u i + z i)))) u

/-- Steps 1–5 of the two-grid cycle (11.6.16), from the pre-smoothed `u_{p₁}`: the fine-grid
residual `r^h = b^h − A^h u_{p₁}`, the restriction `r^{2h} = R r^h`, the coarse-grid correction
`A^{2h} z^{2h} = r^{2h}` (a routine argument `coarseSolve`, exact semantics `(A^{2h})⁻¹`), the
prolongation `z^h = P z^{2h}` and the update `u₊ = u_{p₁} + z^h`. The book prints `u₊ = u_c + z^h`,
updating the pre-smoothing input instead of `u_{p₁}`; the program (and the book's own next display)
uses `u_{p₁}`. -/
noncomputable def coarseGridCorrection {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m : ℕ}
    (coarseSolve : (Fin m → ℝ) → M (Fin m → ℝ)) (b u : Fin (2 * m + 1) → ℝ) :
    M (Fin (2 * m + 1) → ℝ) := do
  let Au ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd (modelA (2 * m + 1)) u 0
  let r ← vecSub rnd b Au
  let r₂ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd (restrictionMatrix m) r 0
  let z₂ ← coarseSolve r₂
  let z ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd (prolongationMatrix m) z₂ 0
  vecAdd rnd u z

/-- **(11.6.16), the two-grid cycle.** Pre-smooth `u_{p₁} = WJ(p₁, u_c)`, correct on the coarse grid
(`coarseGridCorrection`), post-smooth `u₊₊ = WJ(p₂, u₊)`. The smoothing step is a routine argument
`smooth` (exact semantics: one weighted Jacobi step (11.6.11) with `ω = 2/3`). -/
noncomputable def twoGridCycle {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m : ℕ}
    (smooth : (Fin (2 * m + 1) → ℝ) → M (Fin (2 * m + 1) → ℝ))
    (coarseSolve : (Fin m → ℝ) → M (Fin m → ℝ)) (b uc : Fin (2 * m + 1) → ℝ) (p₁ p₂ : ℕ) :
    M (Fin (2 * m + 1) → ℝ) := do
  let u₁ ← (List.range p₁).foldlM (fun v _ => smooth v) uc
  let uplus ← coarseGridCorrection rnd coarseSolve b u₁
  (List.range p₂).foldlM (fun v _ => smooth v) uplus

/-- An in-place loop writing a fixed value into each entry of `List.finRange n`. -/
private theorem foldl_update_const {n : ℕ} (g u : Fin n → ℝ) :
    (List.finRange n).foldl (fun w i => Function.update w i (g i)) u = g :=
  (List.foldl_update_eq_ite g _ u).trans (funext fun j => ite_eq_left (List.mem_finRange j))

/-- An exact loop applying the same map `p` times is the `p`-th iterate. -/
private theorem idRun_foldlM_range_const {α : Type} (f : α → α) (p : ℕ) (x : α) :
    Id.run ((List.range p).foldlM (fun v _ => pure (f v)) x) = f^[p] x := by
  simp only [List.foldlM_pure, List.foldl_const, List.length_range, Id.run_pure]

/-- The exact coarse-grid correction step. -/
private theorem coarseGridCorrection_id (m : ℕ) (b v : Fin (2 * m + 1) → ℝ) :
    Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b v) =
      v + prolongationMatrix m *ᵥ ((modelA m)⁻¹ *ᵥ
        (restrictionMatrix m *ᵥ (b - modelA (2 * m + 1) *ᵥ v))) := by
  have hsub : ∀ u w : Fin (2 * m + 1) → ℝ, Id.run (vecSub pure u w) = u - w := fun u w =>
    (List.idRun_foldlM).trans (foldl_update_const (u - w) u)
  have hadd : ∀ u w : Fin (2 * m + 1) → ℝ, Id.run (vecAdd pure u w) = u + w := fun u w =>
    (List.idRun_foldlM).trans (foldl_update_const (u + w) u)
  change Id.run (vecAdd pure v (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure
    (prolongationMatrix m) ((modelA m)⁻¹ *ᵥ Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure
      (restrictionMatrix m) (Id.run (vecSub pure b (Id.run
        (GolubVanLoan.Chapter01.algorithm_1_1_3 pure (modelA (2 * m + 1)) v 0)))) 0)) 0))) = _
  simp only [GolubVanLoan.Chapter01.algorithm_1_1_3_spec, hsub, hadd, zero_add]

/-- **(11.6.17)** and the display before it: for the exact two-grid correction with `A^h u = b^h`,
`u₊ = u_{p₁} + P (A^{2h})⁻¹ R A^h (u − u_{p₁})` and `u₊ − u = E^h (u_{p₁} − u)`. -/
theorem equation_11_6_17 (m : ℕ) {b u : Fin (2 * m + 1) → ℝ} (hu : modelA (2 * m + 1) *ᵥ u = b)
    (v : Fin (2 * m + 1) → ℝ) :
    Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b v) =
        v + (prolongationMatrix m * (modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)) *ᵥ
          (u - v) ∧
      Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b v) - u =
        twoGridErrorOperator m *ᵥ (v - u) := by
  have h1 : Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b v) =
      v + (prolongationMatrix m * (modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)) *ᵥ
        (u - v) := by
    rw [coarseGridCorrection_id, ← hu, ← mulVec_sub]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨h1, ?_⟩
  rw [h1, twoGridErrorOperator, sub_mulVec, one_mulVec, ← neg_sub u v, mulVec_neg]
  abel

/-- The weighted Jacobi iteration matrix `G^h = G^{h,2/3}` of the model problem. -/
noncomputable abbrev twoThirdsJacobi (n : ℕ) : Stationary.Splitting (modelA n) :=
  jorSplitting (modelA n) (isUnit_diagPart_modelA n) (by norm_num : (2 / 3 : ℝ) ≠ 0)

/-- **(11.6.19).** With the exact smoother `WJ` (weighted Jacobi, `ω = 2/3`) and the exact coarse
solve, the two-grid cycle has `u₊₊ − u = (G^h)^{p₂} E^h (G^h)^{p₁} (u_c − u)`, `G^h = G^{h,2/3}`. -/
theorem equation_11_6_19 (m : ℕ) {b u : Fin (2 * m + 1) → ℝ} (hu : modelA (2 * m + 1) *ᵥ u = b)
    (uc : Fin (2 * m + 1) → ℝ) (p₁ p₂ : ℕ) :
    Id.run (twoGridCycle pure (fun v => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v))
        (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b uc p₁ p₂) - u =
      ((twoThirdsJacobi (2 * m + 1)).iterationOperator ^ p₂ * twoGridErrorOperator m *
        (twoThirdsJacobi (2 * m + 1)).iterationOperator ^ p₁) *ᵥ (uc - u) := by
  have hrun : Id.run (twoGridCycle pure
      (fun v => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v))
      (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b uc p₁ p₂) =
      ((twoThirdsJacobi (2 * m + 1)).mulVecStep b)^[p₂]
        (Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b
          (((twoThirdsJacobi (2 * m + 1)).mulVecStep b)^[p₁] uc))) := by
    change Id.run ((List.range p₂).foldlM
      (fun v _ => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v))
      (Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b
        (Id.run ((List.range p₁).foldlM
          (fun v _ => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v)) uc))))) = _
    rw [idRun_foldlM_range_const, idRun_foldlM_range_const]
  rw [hrun, equation_11_2_7 _ hu, (equation_11_6_17 m hu _).2, equation_11_2_7 _ hu,
    mulVec_mulVec, mulVec_mulVec]

/-! ### The two-grid error operator in the sine basis -/

/-- **(11.6.22).** `E^h q_j = s_j²(q_j + q_{n−j+1})`, `E^h q_{m+1} = q_{m+1}`,
`E^h q_{n−j+1} = c_j²(q_j + q_{n−j+1})`, `j = 1:m` (0-based: the fine mode `j`, the middle mode `m`
and the alias `2m − j`, with `s_j = sin(θ_j/2)`, `c_j = cos(θ_j/2)`,
`θ_j = Multigrid.modeAngle m j`). The columns of (11.6.21), and verbatim the mode identities of the
backbone's exact coarse-grid correction. -/
theorem equation_11_6_22 (m : ℕ) (j : Fin m) :
    twoGridErrorOperator m *ᵥ modelq (2 * m + 1) (fineIndex j) =
        Real.sin (modeAngle m j / 2) ^ 2 •
          (modelq (2 * m + 1) (fineIndex j) + modelq (2 * m + 1) (aliasIndex j)) ∧
      twoGridErrorOperator m *ᵥ modelq (2 * m + 1) (middleIndex m) =
        modelq (2 * m + 1) (middleIndex m) ∧
      twoGridErrorOperator m *ᵥ modelq (2 * m + 1) (aliasIndex j) =
        Real.cos (modeAngle m j / 2) ^ 2 •
          (modelq (2 * m + 1) (fineIndex j) + modelq (2 * m + 1) (aliasIndex j)) := by
  simp only [twoGridErrorOperator_eq, modelq, mulVec_smul, coarseCorrection_mulVec_sineVec,
    coarseCorrection_mulVec_sineVec_middleIndex, coarseCorrection_mulVec_sineVec_aliasIndex,
    ← smul_add, smul_comm (Real.sqrt _) (_ ^ 2 : ℝ), and_self]

/-- The weights of (11.6.21) indexed by the fine mode: `σ_k = sin²((k + 1)π/(2(n + 1)))`, which is
`s_j²` at the fine mode `j` (`sigma_fineIndex`), `c_j²` at its alias `2m − j` (`sigma_aliasIndex`)
and `1/2` at the middle mode (`sigma_middleIndex`) — (11.6.9) read the other way. -/
noncomputable def twoGridSigma (m : ℕ) (k : Fin (2 * m + 1)) : ℝ :=
  Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2

/-- The fine mode's partner is its alias: `rev j = 2m − j`. -/
private theorem rev_fineIndex {m : ℕ} (j : Fin m) : Fin.rev (fineIndex j) = aliasIndex j :=
  Fin.ext (by simp only [Fin.val_rev, fineIndex, aliasIndex]; omega)

/-- The alias's partner is the fine mode. -/
private theorem rev_aliasIndex {m : ℕ} (j : Fin m) : Fin.rev (aliasIndex j) = fineIndex j := by
  rw [← rev_fineIndex, Fin.rev_rev]

/-- The middle mode is its own partner. -/
private theorem rev_middleIndex (m : ℕ) : Fin.rev (middleIndex m) = middleIndex m :=
  Fin.ext (by simp only [Fin.val_rev, middleIndex]; omega)

/-- `σ` at the fine mode `j` is `s_j²`. -/
private theorem sigma_fineIndex {m : ℕ} (j : Fin m) :
    twoGridSigma m (fineIndex j) = Real.sin (modeAngle m j / 2) ^ 2 := by
  rw [twoGridSigma]
  congr 2
  rw [fineIndex, modeAngle]
  push_cast
  field_simp
  ring

/-- `σ` at the alias `2m − j` is `c_j²`. -/
private theorem sigma_aliasIndex {m : ℕ} (j : Fin m) :
    twoGridSigma m (aliasIndex j) = Real.cos (modeAngle m j / 2) ^ 2 := by
  have hj : (j : ℕ) ≤ 2 * m := by have := j.isLt; omega
  have e : (((aliasIndex j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
      Real.pi / 2 - modeAngle m j / 2 := by
    rw [aliasIndex, Fin.val_mk, Nat.cast_sub hj, modeAngle]
    push_cast
    field_simp
    ring
  rw [twoGridSigma, e, Real.sin_pi_div_two_sub]

/-- `σ` at the middle mode is `1/2`. -/
private theorem sigma_middleIndex (m : ℕ) : twoGridSigma m (middleIndex m) = 1 / 2 := by
  have e : (((middleIndex m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
      Real.pi / 4 := by
    rw [middleIndex]
    push_cast
    field_simp
    ring
  rw [twoGridSigma, e, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- **(11.6.22), uniformly.** `E^h q_k = σ_k (q_k + q_{rev k})` for every fine mode `k`,
`rev k = 2m − k` (at the middle mode `rev m = m` and `σ_m = 1/2`, which is
`E^h q_{m+1} = q_{m+1}`). -/
private theorem twoGridErrorOperator_mulVec_modelq (m : ℕ) (k : Fin (2 * m + 1)) :
    twoGridErrorOperator m *ᵥ modelq (2 * m + 1) k =
      twoGridSigma m k • (modelq (2 * m + 1) k + modelq (2 * m + 1) (Fin.rev k)) := by
  by_cases hk : (k : ℕ) < m
  · obtain ⟨j, rfl⟩ : ∃ j : Fin m, k = fineIndex j := ⟨⟨k, hk⟩, Fin.ext rfl⟩
    rw [rev_fineIndex, sigma_fineIndex]
    exact (equation_11_6_22 m j).1
  · by_cases hk' : m < (k : ℕ)
    · have hk2 := k.isLt
      obtain ⟨j, rfl⟩ : ∃ j : Fin m, k = aliasIndex j :=
        ⟨⟨2 * m - k, by omega⟩, Fin.ext (by simp only [aliasIndex, Fin.val_mk]; omega)⟩
      rw [rev_aliasIndex, sigma_aliasIndex, add_comm (modelq _ (aliasIndex j))]
      exact (equation_11_6_22 m j).2.2
    · obtain rfl : k = middleIndex m := Fin.ext (by simp only [middleIndex]; omega)
      rw [rev_middleIndex, sigma_middleIndex, twoGridErrorOperator_eq, modelq, mulVec_smul,
        coarseCorrection_mulVec_sineVec_middleIndex, ← two_smul ℝ, smul_smul]
      norm_num

/-- The block matrix of (11.6.21), `[S^h 0 C^hℰ_m; 0 1 0; ℰ_mS^h 0 ℰ_mC^hℰ_m]`, column by column:
the column of the fine mode `k` carries `σ_k` in the rows `k` and `2m − k` (so the column of the
fine mode `j < m` carries `s_j²` in the rows `j` and `2m − j`, the column of its alias carries
`c_j²` in the same two rows, and the middle column is the unit vector, `2σ_m = 1`). -/
noncomputable def twoGridBlock (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  Matrix.of fun i k =>
    twoGridSigma m k * ((if i = k then 1 else 0) + (if i = Fin.rev k then 1 else 0))

/-- Column `k` of `Q^h B` is `∑_i B_ik q_i`, read off `Q^h`'s columns. -/
private theorem modelQ_mul_apply {n : ℕ} {p : Type*} (B : Matrix (Fin n) p ℝ)
    (i : Fin n) (k : p) : (modelQ n * B) i k = ∑ j, modelq n j i * B j k := by
  rw [mul_apply]
  rfl

/-- **Theorem 11.6.2** ((11.6.21)). `E^h Q^h = Q^h [S^h 0 C^hℰ_m; 0 1 0; ℰ_mS^h 0 ℰ_mC^hℰ_m]`. The
proof's printed value `(Q^{2h})ᵀA^{2h}Q^{2h} = (1/(2h²))(I_m − √C^h)` is wrong — the coarse
eigenvalues are `(4/h²) S^hC^h` — but the theorem is right; it is the backbone's exact coarse-grid
correction acting on the sine modes (`equation_11_6_22`), assembled column by column (the book's
P11.6.2). -/
theorem theorem_11_6_2 (m : ℕ) :
    twoGridErrorOperator m * modelQ (2 * m + 1) = modelQ (2 * m + 1) * twoGridBlock m := by
  ext i k
  rw [modelQ_mul_apply]
  change (twoGridErrorOperator m *ᵥ modelq (2 * m + 1) k) i = _
  rw [twoGridErrorOperator_mulVec_modelq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  simp only [twoGridBlock, of_apply, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The block `[C^h; 0; −ℰ_m S^h]` of Lemma 11.6.1, column by column: the column of the coarse mode
`l` carries `c_l²` in the row of the fine mode `l` and `−s_l²` in the row of its alias `2m − l`. -/
noncomputable def transferBlock (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin m) ℝ :=
  Matrix.of fun i l =>
    Real.cos (modeAngle m l / 2) ^ 2 * (if i = fineIndex l then 1 else 0) -
      Real.sin (modeAngle m l / 2) ^ 2 * (if i = aliasIndex l then 1 else 0)

/-- `P^h_{2h} Q^{2h} = √2 Q^h [C^h; 0; −ℰ_m S^h]`. -/
private theorem prolongation_mul_modelQ (m : ℕ) :
    prolongationMatrix m * modelQ m = modelQ (2 * m + 1) * (Real.sqrt 2 • transferBlock m) := by
  ext i l
  rw [Matrix.mul_smul, Matrix.smul_apply, modelQ_mul_apply]
  change (prolongationMatrix m *ᵥ modelq m l) i = _
  simp only [transferBlock, of_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [prolongationMatrix_eq, modelq, mulVec_smul, linearInterpolation_mulVec_sineVec]
  simp only [modelq, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sqrt_fine]
  field_simp

/-- **Lemma 11.6.1** ((11.6.20)). For `n = 2m + 1`, `(Q^h)ᵀ P^h_{2h} Q^{2h} = √2 [C^h; 0; −ℰ_m S^h]`
and `(Q^{2h})ᵀ R^{2h}_h Q^h = √(1/2) [C^h; 0; −ℰ_m S^h]ᵀ` (the block matrix is `transferBlock m`).
The book's proof goes through `(Q^h)ᵀ B^h Q^h` and (11.6.10); the proof here reads the columns off
the backbone's interpolation of a coarse sine mode. -/
theorem lemma_11_6_1 (m : ℕ) :
    (modelQ (2 * m + 1))ᵀ * prolongationMatrix m * modelQ m = Real.sqrt 2 • transferBlock m ∧
      (modelQ m)ᵀ * restrictionMatrix m * modelQ (2 * m + 1) =
        Real.sqrt (1 / 2) • (transferBlock m)ᵀ := by
  have h1 : (modelQ (2 * m + 1))ᵀ * prolongationMatrix m * modelQ m =
      Real.sqrt 2 • transferBlock m := by
    rw [Matrix.mul_assoc, prolongation_mul_modelQ, ← Matrix.mul_assoc, modelQ_transpose_mul,
      Matrix.one_mul]
  refine ⟨h1, ?_⟩
  have h2 : (modelQ m)ᵀ * restrictionMatrix m * modelQ (2 * m + 1) =
      (1 / 2 : ℝ) • ((modelQ (2 * m + 1))ᵀ * prolongationMatrix m * modelQ m)ᵀ := by
    rw [restrictionMatrix_eq_half_transpose, transpose_mul, transpose_mul, transpose_transpose,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [h2, h1, transpose_smul, smul_smul]
  congr 1
  have h2' : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

/-- **Bridge to the backbone.** The book's `E^h` is the backbone's coarse-grid correction
`Multigrid.coarseCorrection` of `A^h` and the prolongation `P^h_{2h}` (the `A^h`-orthogonal
projector complement onto `ran P`), and the error operator of (11.6.19) is
`Multigrid.twoGridOperator` with the weighted Jacobi smoother `G^h`. Consequently `E^h` is
idempotent and `A^h`-self-adjoint. -/
theorem twoGridError_eq_coarseCorrection (m : ℕ) (p₁ p₂ : ℕ) :
    let hA : (toEuclideanLin (modelA (2 * m + 1))).IsSymmetricCoercive :=
      ((posDef_symmTridiagonalToeplitz_neg_one_two (2 * m + 1)).smul (by positivity :
        (0 : ℝ) < (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2)).isSymmetricCoercive_toEuclideanLin
    toEuclideanLin (twoGridErrorOperator m) =
        coarseCorrection (toEuclideanLin (modelA (2 * m + 1))) hA
          (toEuclideanLin (prolongationMatrix m)) ∧
      toEuclideanLin ((twoThirdsJacobi (2 * m + 1)).iterationOperator ^ p₂ *
          twoGridErrorOperator m * (twoThirdsJacobi (2 * m + 1)).iterationOperator ^ p₁) =
        twoGridOperator (toEuclideanLin (modelA (2 * m + 1))) hA
          (toEuclideanLin (prolongationMatrix m))
          (toEuclideanLin (twoThirdsJacobi (2 * m + 1)).iterationOperator) p₁ p₂ := by
  intro hA
  have hPT : (prolongationMatrix m)ᵀ = (2 : ℝ) • restrictionMatrix m := by
    rw [restrictionMatrix_eq_half_transpose, smul_smul]
    norm_num
  have hAm : IsUnit (modelA m).det := by
    rw [← isUnit_iff_isUnit_det]
    exact ((posDef_symmTridiagonalToeplitz_neg_one_two m).smul
      (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ 2)).isUnit
  have key : (2 : ℝ) • restrictionMatrix m * (modelA (2 * m + 1) * (prolongationMatrix m *
      ((modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)))) =
      (2 : ℝ) • restrictionMatrix m * modelA (2 * m + 1) := by
    simp only [Matrix.smul_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, galerkin_coarse_eq, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, mul_nonsing_inv _ hAm, Matrix.one_mul]
  have hE : toEuclideanLin (twoGridErrorOperator m) = coarseCorrection
      (toEuclideanLin (modelA (2 * m + 1))) hA (toEuclideanLin (prolongationMatrix m)) := by
    ext1 x
    rw [coarseCorrection_apply]
    have hy : galerkinCoarse (toEuclideanLin (modelA (2 * m + 1)))
        (toEuclideanLin (prolongationMatrix m))
        (toEuclideanLin ((modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)) x) =
        LinearMap.adjoint (toEuclideanLin (prolongationMatrix m))
          (toEuclideanLin (modelA (2 * m + 1)) x) := by
      rw [galerkinCoarse_apply, ← toEuclideanLin_conjTranspose,
        conjTranspose_eq_transpose_of_trivial, hPT]
      simp only [← toEuclideanLin_mul_apply]
      rw [key]
    rw [coarseProjection_apply_eq _ hA _ hy, ← toEuclideanLin_mul_apply, twoGridErrorOperator,
      map_sub, toEuclideanLin_one, LinearMap.sub_apply, LinearMap.id_apply]
    simp only [Matrix.mul_assoc]
  refine ⟨hE, ?_⟩
  ext1 x
  rw [twoGridOperator_apply, ← hE]
  simp only [toEuclideanLin_mul_apply, toEuclideanLin_pow]

/-! ### The error of one cycle, mode by mode -/

/-- `(B γ)_i = σ_i γ_i + σ_{rev i} γ_{rev i}` for the block matrix of (11.6.21). -/
private theorem twoGridBlock_mulVec (m : ℕ) (γ : Fin (2 * m + 1) → ℝ) (i : Fin (2 * m + 1)) :
    (twoGridBlock m *ᵥ γ) i =
      twoGridSigma m i * γ i + twoGridSigma m (Fin.rev i) * γ (Fin.rev i) := by
  have hrev : ∀ k : Fin (2 * m + 1), (i = Fin.rev k) = (k = Fin.rev i) := fun k =>
    propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  simp only [mulVec, dotProduct, twoGridBlock, of_apply, hrev, mul_add, add_mul, mul_ite, ite_mul,
    mul_one, mul_zero, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- **§11.6.3, the error of one cycle, mode by mode.** If `u_c − u = ∑_j α_j q_j`, then after the
exact two-grid cycle `u₊₊ − u = ∑_j α̃_j q_j` with, for `j = 1:m`,
`α̃_j = (α_jτ_j^{p₁}s_j² + α_{n−j+1}τ_{n−j+1}^{p₁}c_j²)τ_j^{p₂}`,
`α̃_{m+1} = α_{m+1}τ_{m+1}^{p₁+p₂}`,
`α̃_{n−j+1} = (α_jτ_j^{p₁}s_j² + α_{n−j+1}τ_{n−j+1}^{p₁}c_j²)τ_{n−j+1}^{p₂}` (`τ = τ^{h,2/3}`;
0-based: the fine mode `j`, the middle mode `m`, the alias `2m − j`). -/
theorem twoGrid_error_coeffs (m : ℕ) {b u : Fin (2 * m + 1) → ℝ}
    (hu : modelA (2 * m + 1) *ᵥ u = b) (uc α : Fin (2 * m + 1) → ℝ)
    (hα : uc - u = modelQ (2 * m + 1) *ᵥ α) (p₁ p₂ : ℕ) :
    ∃ α' : Fin (2 * m + 1) → ℝ,
      Id.run (twoGridCycle pure (fun v => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v))
        (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b uc p₁ p₂) - u = modelQ (2 * m + 1) *ᵥ α' ∧
      (∀ j : Fin m,
        α' (fineIndex j) = (α (fineIndex j) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (fineIndex j) ^ p₁ *
            Real.sin (modeAngle m j / 2) ^ 2 + α (aliasIndex j) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (aliasIndex j) ^ p₁ *
            Real.cos (modeAngle m j / 2) ^ 2) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (fineIndex j) ^ p₂ ∧
        α' (aliasIndex j) = (α (fineIndex j) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (fineIndex j) ^ p₁ *
            Real.sin (modeAngle m j / 2) ^ 2 + α (aliasIndex j) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (aliasIndex j) ^ p₁ *
            Real.cos (modeAngle m j / 2) ^ 2) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (aliasIndex j) ^ p₂) ∧
      α' (middleIndex m) =
        α (middleIndex m) * weightedJacobiTau (2 * m + 1) (2 / 3) (middleIndex m) ^ (p₁ + p₂) := by
  set τ := weightedJacobiTau (2 * m + 1) (2 / 3)
  set β : Fin (2 * m + 1) → ℝ := fun k => τ k ^ p₁ * α k
  refine ⟨fun k => τ k ^ p₂ * (twoGridBlock m *ᵥ β) k, ?_, fun j => ⟨?_, ?_⟩, ?_⟩
  · have h2 : twoGridErrorOperator m *ᵥ (modelQ (2 * m + 1) *ᵥ β) =
        modelQ (2 * m + 1) *ᵥ (twoGridBlock m *ᵥ β) := by
      rw [mulVec_mulVec, theorem_11_6_2, ← mulVec_mulVec]
    rw [equation_11_6_19 m hu, hα, ← mulVec_mulVec, ← mulVec_mulVec,
      weightedJacobi_pow_mulVec_modelQ, h2, weightedJacobi_pow_mulVec_modelQ]
  · simp only [twoGridBlock_mulVec, rev_fineIndex, sigma_fineIndex, sigma_aliasIndex, β]
    ring
  · simp only [twoGridBlock_mulVec, rev_aliasIndex, sigma_fineIndex, sigma_aliasIndex, β]
    ring
  · simp only [twoGridBlock_mulVec, rev_middleIndex, sigma_middleIndex, β]
    ring

/-- **§11.6.3, the bounds the conclusion rests on.** `|τ_{n−j+1}^{h,2/3}| ≤ 1/3` and `s_j² ≤ 1/2`
for `j = 1:m`, both independent of `n`: the high-frequency coefficients are damped by the smoother,
the low-frequency ones by the coarse grid (in `twoGrid_error_coeffs` every `α̃` carries a factor
`τ_{n−j+1}^{p}` or `s_j²`). -/
theorem twoGrid_damping_bounds (m : ℕ) (j : Fin m) :
    |weightedJacobiTau (2 * m + 1) (2 / 3) (aliasIndex j)| ≤ 1 / 3 ∧
      Real.sin (modeAngle m j / 2) ^ 2 ≤ 1 / 2 := by
  refine ⟨(weightedJacobi_twoThirds m).1 _ (by simp only [aliasIndex, Fin.val_mk]; omega), ?_⟩
  have h0 := modeAngle_pos j
  have h1 := modeAngle_lt_pi_div_two j
  have hs : Real.sin (modeAngle m j / 2) ≤ Real.sqrt 2 / 2 := by
    rw [← Real.sin_pi_div_four]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by linarith)
  have hs0 : 0 ≤ Real.sin (modeAngle m j / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have := pow_le_pow_left₀ hs0 hs 2
  rw [div_pow, Real.sq_sqrt (by norm_num)] at this
  linarith

end GolubVanLoan.Chapter11
