import NumlibSurface.GolubVanLoan.Chapter05.Section05

/-!
# Golub–Van Loan §5.6: square and underdetermined systems

Surface file for [golub2013matrix] §5.6: solving a square system through a QR factorization of
`(HA)ᵀ` without back substitution (§5.6.1); the solution set of an underdetermined system and
its minimal-norm solution through the SVD (§5.6.2).

## Conventions

As in §5.5: SVDs are `Matrix.IsSVD`, the pseudoinverse is `Matrix.pinv`, indices are 0-based and
the book's `e_n` is `Pi.single (Fin.last k) 1` for `n = k + 1`.

## Not formalized

The flop table (Figure 5.6.1) and the three bullet arguments for orthogonal methods (prose).
-/

open Matrix WithLp

namespace GolubVanLoan.Chapter05

variable {m n : ℕ}

/-! ### §5.6.1 Square systems -/

/-- **§5.6.1, preprocessing `b`**: for nonsingular `A ∈ ℝ^{n×n}`, a Householder matrix `H` with
`H b = β e_n`, and a QR factorization `(HA)ᵀ = QR`, the solution of `Ax = b` is
`x = (β / r_nn) Q(:, n)`: `A = Hᵀ Rᵀ Qᵀ`, and `Rᵀ y = β e_n` with `y = Qᵀ x` is solved by
`y = (β / r_nn) e_n` because `Rᵀ` is lower triangular. -/
theorem solve_householderPreprocess {k : ℕ} {A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (hA : IsUnit A) (v : Fin (k + 1) → ℝ) {b : Fin (k + 1) → ℝ} {β : ℝ}
    (hb : householderMatrix v *ᵥ b = β • Pi.single (Fin.last k) 1)
    {Q R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hQR : IsQR (householderMatrix v * A)ᵀ Q R) :
    A *ᵥ ((β / R (Fin.last k) (Fin.last k)) • Q.col (Fin.last k)) = b := by
  set H := householderMatrix v with hH
  have hHH : H * H = 1 := by rw [hH, householderMatrix_eq_reflector, reflector_mul_self]
  have hHs : Hᵀ = H := householderMatrix_isSymm v
  have hQ : Qᵀ * Q = 1 := by
    have := hQR.mem_unitaryGroup
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      at this
    exact this
  -- `H A = Rᵀ Qᵀ`
  have hHA : H * A = Rᵀ * Qᵀ := by
    have := congrArg transpose hQR.mul_eq
    rw [transpose_transpose, transpose_mul] at this
    exact this.symm
  have hA' : A = H * (Rᵀ * Qᵀ) := by
    rw [← hHA, ← Matrix.mul_assoc, hHH, Matrix.one_mul]
  -- the last diagonal entry of `R` is nonzero
  have hR : R (Fin.last k) (Fin.last k) ≠ 0 := by
    have hdet : (Rᵀ * Qᵀ).det ≠ 0 := by
      rw [← hHA, det_mul]
      refine mul_ne_zero ?_ ((isUnit_iff_isUnit_det A).1 hA).ne_zero
      intro h0
      have := congrArg det hHH
      rw [det_mul, h0, zero_mul, det_one] at this
      exact zero_ne_one this
    rw [det_mul, det_transpose] at hdet
    have hRt : R.IsUpperTriangular := fun i j hij => hQR.apply_eq_zero i j hij
    rw [det_of_isUpperTriangular hRt] at hdet
    exact fun h0 => (left_ne_zero_of_mul hdet) (Finset.prod_eq_zero (Finset.mem_univ _) h0)
  -- `Qᵀ q_n = e_n` and `Rᵀ e_n = r_nn e_n`
  have hQe : Qᵀ *ᵥ Q.col (Fin.last k) = Pi.single (Fin.last k) 1 := by
    rw [show Q.col (Fin.last k) = Q *ᵥ Pi.single (Fin.last k) 1 by
      ext i; simp, mulVec_mulVec, hQ, one_mulVec]
  have hRe : Rᵀ *ᵥ Pi.single (Fin.last k) 1 =
      R (Fin.last k) (Fin.last k) • Pi.single (Fin.last k) 1 := by
    ext i
    rw [mulVec_single_one, col_apply, transpose_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = Fin.last k
    · subst hi; simp
    · rw [hQR.apply_eq_zero _ _ (lt_of_le_of_ne (Fin.le_last i) (fun e => hi (Fin.ext e))),
        Pi.single_eq_of_ne hi, mul_zero]
  have hHb : H *ᵥ (β • Pi.single (Fin.last k) 1) = b := by
    rw [← hb, mulVec_mulVec, hHH, one_mulVec]
  rw [hA', ← mulVec_mulVec, ← mulVec_mulVec, mulVec_smul, hQe, mulVec_smul, hRe, smul_smul,
    div_mul_cancel₀ _ hR, hHb]

/-! ### §5.6.2 Underdetermined systems -/

/-- **§5.6.2**: an underdetermined system `Ax = b`, `A ∈ ℝ^{m×n}` with `m < n`, "either has no
solution or has an infinity of solutions". -/
theorem underdetermined_solutions (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hmn : m < n) :
    {x | A *ᵥ x = b} = ∅ ∨ {x | A *ᵥ x = b}.Infinite := by
  rcases Set.eq_empty_or_nonempty {x | A *ᵥ x = b} with h | ⟨x₀, hx₀⟩
  · exact Or.inl h
  · right
    have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hmn)
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker, mulVecLin_apply] at hz
    refine Set.infinite_of_injective_forall_mem (f := fun t : ℝ => x₀ + t • z) ?_ fun t => ?_
    · intro s t hst
      have : (s - t) • z = 0 := by
        simp only at hst
        rw [sub_smul, sub_eq_zero]
        exact add_left_cancel hst
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hz0)
    · change A *ᵥ (x₀ + t • z) = b
      rw [mulVec_add, mulVec_smul, hz, smul_zero, add_zero]
      exact hx₀

/-- **§5.6.2, the minimum norm solution from the SVD**: if `A = ∑_{i=1}^{r} σ_i u_i v_iᵀ` (an SVD,
`r = rank(A)`) and `Ax = b` is solvable, then `x = ∑_{i=1}^{r} (u_iᵀ b / σ_i) v_i` solves it and
has the smallest 2-norm of all solutions. -/
theorem minNorm_svd_underdetermined {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {b : Fin m → ℝ}
    (hb : ∃ x, A *ᵥ x = b) :
    A *ᵥ (∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
        V.col (Fin.castLE (rank_le_width A) i)) = b ∧
      ∀ y, A *ᵥ y = b →
        ‖(toLp 2 (∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
          V.col (Fin.castLE (rank_le_width A) i)) : EuclideanSpace ℝ (Fin n))‖ ≤
          ‖(toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
  obtain ⟨-, hmin⟩ := equation_5_5_1 h b
  obtain ⟨x, hx⟩ := hb
  -- a solution attains residual `0`, so every least-squares solution is a solution
  have hres : ∀ y, IsLeastSquaresSolution A (toLp 2 b) (toLp 2 y) ↔ A *ᵥ y = b := by
    intro y
    constructor
    · intro hy
      have := hy (toLp 2 x)
      rw [toEuclideanLin_toLp, toEuclideanLin_toLp, hx, sub_self, norm_zero,
        norm_le_zero_iff] at this
      exact WithLp.toLp_injective 2 (sub_eq_zero.1 this)
    · intro hy z
      rw [toEuclideanLin_toLp, hy, sub_self, norm_zero]
      exact norm_nonneg _
  refine ⟨(hres _).1 hmin.1, fun y hy => hmin.2 _ ((hres y).2 hy)⟩

end GolubVanLoan.Chapter05
