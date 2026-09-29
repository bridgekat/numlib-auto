import NumlibSurface.GolubVanLoan.Chapter05.Section05

/-!
# Golub–Van Loan §5.6: square and underdetermined systems

Surface file for [golub2013matrix] §5.6: solving a square system through a QR factorization of
`(HA)ᵀ` without back substitution (§5.6.1); the solution set of an underdetermined system and
its minimal-norm solution through the SVD and Algorithms 5.6.1–5.6.2 (§5.6.2); the perturbation
of the minimum norm solution (Theorem 5.6.1, rigorous and first-order, and the derivative (5.6.2),
§5.6.3). Algorithm 5.6.1 runs Algorithm 5.4.1 (written for `m ≥ n`) on `A` padded with zero rows
(`padRows`).

## Conventions

As in §5.5: SVDs are `Matrix.IsSVD`, the pseudoinverse is `Matrix.pinv`, indices are 0-based and
the book's `e_n` is `Pi.single (Fin.last k) 1` for `n = k + 1`.

## Not formalized

The flop table (Figure 5.6.1) and the three bullet arguments for orthogonal methods (prose).
-/

open FloatingPoint Matrix WithLp

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

/-! ### §5.6.2 Algorithms 5.6.1 and 5.6.2 -/

section Underdetermined

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 5.6.2**: "Given `A ∈ ℝ^{m×n}` with `rank(A) = m` and `b ∈ ℝ^m`, the following
algorithm finds the minimum 2-norm solution to `Ax = b`":
```
Compute the QR factorization Aᵀ = QR.
Solve R(1:m, 1:m)ᵀ z = b.
Set x = Q(:, 1:m) z.
```
The QR factorization is Algorithm 5.2.1 on `Aᵀ` (`m ≤ n`), the lower triangular solve is
Algorithm 3.1.1, `Q(:, 1:m)` is accumulated by (5.1.5) (`factoredQFirstColumns`, which recomputes
the `β` as the book prints) and the product is the gaxpy Algorithm 1.1.3. -/
noncomputable def algorithm_5_6_2 (hmn : m ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    M (Fin n → ℝ) := do
  let QR ← algorithm_5_2_1 rnd Aᵀ
  let z ← Chapter03.algorithm_3_1_1 rnd ((upperPart QR.1).firstRows hmn)ᵀ b
  let Q₁ ← factoredQFirstColumns rnd QR.1 m
  Chapter01.algorithm_1_1_3 rnd Q₁ z 0

/-- **Algorithm 5.6.1**: "Given `A ∈ ℝ^{m×n}` with `rank(A) = m` and `b ∈ ℝ^m`, the following
algorithm finds an `x ∈ ℝⁿ` such that `Ax = b`":
```
Compute QR-with-column-pivoting factorization: QᵀAΠ = R.
Solve R(1:m, 1:m) z₁ = Qᵀb.
Set x = Π [z₁; 0].
```
Algorithm 5.4.1 is run on `A` padded with zero rows (`padRows`; it is written for `m ≥ n`), `Qᵀb`
is formed from the stored reflectors with the returned `β` (`storedQTransposeMulVec`,
convention 13), the solve is Algorithm 3.1.2, and `Π [z₁; 0]` is a permutation of coordinates. -/
noncomputable def algorithm_5_6_1 (hmn : m ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : M (Fin n → ℝ) := do
  let st ← algorithm_5_4_1 rnd le_rfl (padRows A)
  let c ← storedQTransposeMulVec rnd st.A st.β fun i =>
    if hi : (i : ℕ) < m then b ⟨i, hi⟩ else 0
  let z ← Chapter03.algorithm_3_1_2 rnd
    ((upperPart st.A).submatrix (Fin.castLE hmn) (Fin.castLE hmn)) fun i => c (Fin.castLE hmn i)
  pure (blockVec hmn z 0 ∘ (pivotPerm st.piv).symm)

end Programs

/-- **Algorithm 5.6.1 solves `Ax = b`** (exact arithmetic): for `A` of full row rank `m`, the
output solves `Ax = b` and has at most `m` nonzero entries ("the minimum norm solution is not
guaranteed"). `algorithm_5_4_1_spec` on the padded array gives the pivoted factorization with
`r = m` and `R₁₁` nonsingular, the output is its basic solution
(`Matrix.IsPivotedQR.IsRankRevealing.isLeastSquaresSolution_basic`), and a least-squares solution
of a consistent system solves it. -/
theorem algorithm_5_6_1_spec (hmn : m ≤ n) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ A) (b : Fin m → ℝ) :
    A *ᵥ Id.run (algorithm_5_6_1 pure hmn A b) = b ∧
      (Finset.univ.filter fun j => Id.run (algorithm_5_6_1 pure hmn A b) j ≠ 0).card ≤ m := by
  obtain ⟨h1, hrank, -⟩ := algorithm_5_4_1_spec le_rfl (padRows A)
  -- the padded array has rank `m`
  set E : Matrix (Fin n) (Fin m) ℝ := of fun i k => if (i : ℕ) = k then 1 else 0 with hE
  set F : Matrix (Fin m) (Fin n) ℝ := of fun k i => if (i : ℕ) = k then 1 else 0 with hF
  have hEA : padRows A = E * A := by
    ext i j
    simp only [padRows, hE, of_apply, mul_apply, ite_mul, one_mul, zero_mul]
    split_ifs with hi
    · rw [Finset.sum_eq_single ⟨i, hi⟩ (fun k _ hk => by
        rw [ite_eq_right_iff.2 (fun e => absurd (Fin.ext e.symm) hk)]) (by simp)]
      simp
    · refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rw [ite_eq_right_iff.2 (fun (e : (i : ℕ) = k) => absurd (by rw [e]; exact k.isLt) hi)]
  have hFA : F * padRows A = A := by
    ext k j
    simp only [padRows, hF, of_apply, mul_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (Fin.castLE hmn k) (fun i _ hi => by
      have : ¬ ((i : ℕ) = k) := fun e => hi (Fin.ext (by simpa using e))
      simp [this]) (by simp)]
    simp
  have hrA : A.rank = m := by simpa using hA.rank_matrix
  have hr : (Id.run (algorithm_5_4_1 pure le_rfl (padRows A))).r = m := by
    rw [hrank]
    refine le_antisymm ?_ ?_
    · rw [hEA]; exact (rank_mul_le_right E A).trans hrA.le
    · calc m = A.rank := hrA.symm
        _ = (F * padRows A).rank := by rw [hFA]
        _ ≤ _ := rank_mul_le_right F _
  set out := Id.run (algorithm_5_4_1 pure le_rfl (padRows A)) with hout
  set bp : Fin n → ℝ := fun i => if hi : (i : ℕ) < m then b ⟨i, hi⟩ else 0 with hbp
  set Q := factoredQ out.β out.A with hQ
  set R := upperPart out.A with hR
  set σ := pivotPerm out.piv with hσ
  have h1' := h1
  rw [hr] at h1'
  set R₁₁ := R.submatrix (Fin.castLE hmn) (Fin.castLE hmn) with hR₁₁
  have hup : R₁₁.IsUpperTriangular := fun i j hij => by
    simp only [hR₁₁, hR, submatrix_apply, upperPart, of_apply, Fin.val_castLE]
    rw [ite_eq_right_iff]
    intro h
    exact absurd (Fin.lt_def.1 hij) (not_lt.2 h)
  have hdiag : ∀ i, R₁₁ i i ≠ 0 :=
    (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hup).1 h1'.isUnit_block
  set z := Id.run (Chapter03.algorithm_3_1_2 pure R₁₁ fun i => (Qᵀ *ᵥ bp) (Fin.castLE hmn i))
    with hzdef
  have hz : R₁₁ *ᵥ z = fun i => (Qᵀ *ᵥ bp) (Fin.castLE hmn i) :=
    Chapter03.algorithm_3_1_2_spec hup hdiag _
  have hrun : Id.run (algorithm_5_6_1 pure hmn A b) = blockVec hmn z 0 ∘ σ.symm := by
    simp only [algorithm_5_6_1, Id.run_bind, Id.run_pure, storedQTransposeMulVec_pure]
    rfl
  -- the output is a least-squares solution of the padded system
  have hLS : IsLeastSquaresSolution (padRows A) (toLp 2 bp)
      (toLp 2 (Id.run (algorithm_5_6_1 pure hmn A b))) := by
    rw [hrun]
    refine h1'.isLeastSquaresSolution_iff.2 fun i => ?_
    have e : ofLp (toLp 2 (blockVec hmn z 0 ∘ σ.symm)) ∘ σ = blockVec hmn z 0 := by
      funext k
      simp
    rw [e, mulVec_blockVec_castLE, mulVec_zero, Pi.zero_apply, add_zero,
      conjTranspose_eq_transpose_of_trivial]
    exact congrFun hz i
  -- the padded system is consistent
  have hpad : ∀ x, padRows A *ᵥ x =
      fun i : Fin n => if hi : (i : ℕ) < m then (A *ᵥ x) ⟨i, hi⟩ else 0 := by
    intro x
    funext i
    simp only [mulVec, dotProduct, padRows, of_apply]
    split_ifs <;> simp
  have hG := (posDef_self_mul_conjTranspose_of_linearIndependent hA).isUnit
  rw [conjTranspose_eq_transpose_of_trivial] at hG
  have hAy : A *ᵥ ((Aᵀ * (A * Aᵀ)⁻¹) *ᵥ b) = b := by
    rw [mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hG),
      one_mulVec]
  have hy0 : padRows A *ᵥ ((Aᵀ * (A * Aᵀ)⁻¹) *ᵥ b) = bp := by
    rw [hpad, hAy]
  have h0 := hLS (toLp 2 ((Aᵀ * (A * Aᵀ)⁻¹) *ᵥ b))
  rw [toEuclideanLin_toLp, toEuclideanLin_toLp, hy0, sub_self, norm_zero, norm_le_zero_iff,
    sub_eq_zero] at h0
  have hx := (toLp_injective 2).eq_iff.1 h0
  have hAx : A *ᵥ Id.run (algorithm_5_6_1 pure hmn A b) = b := by
    funext i
    have := congrFun hx (Fin.castLE hmn i)
    rw [hpad] at this
    simpa [hbp] using this
  refine ⟨hAx, ?_⟩
  rw [hrun]
  calc (Finset.univ.filter fun j => (blockVec hmn z 0 ∘ σ.symm) j ≠ 0).card
      ≤ (Finset.univ.filter fun j : Fin n => (σ.symm j : ℕ) < m).card := by
        refine Finset.card_le_card fun j hj => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hj ⊢
        by_contra h
        exact hj (by simp [blockVec, h])
    _ = (Finset.univ.filter fun k : Fin n => (k : ℕ) < m).card :=
        Finset.card_equiv σ.symm (by simp)
    _ = m := by rw [Fin.card_filter_val_lt, min_eq_right hmn]

/-- **Algorithm 5.6.2 computes the minimum norm solution** (exact arithmetic): for `A` of full row
rank and no degenerate Householder step of Algorithm 5.2.1 on `Aᵀ` (every returned `β_j ≠ 0`, so
that the recomputed `β` of (5.1.5) are the actual ones, `equation_5_1_4_beta`), the output `x`
solves `Ax = b` and is the minimum norm solution `x = A⁺ b`: from the thin factorization
`Aᵀ = Q₁ R₁`, `A⁺ = Q₁ R₁⁻ᵀ` (`Matrix.pinv_eq_of_isThinQR_conjTranspose`). -/
theorem algorithm_5_6_2_spec (hmn : m ≤ n) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ A) (hβ : ∀ j, (Id.run (algorithm_5_2_1 pure Aᵀ)).2 j ≠ 0)
    (b : Fin m → ℝ) :
    A *ᵥ Id.run (algorithm_5_6_2 pure hmn A b) = b ∧
      toLp 2 (Id.run (algorithm_5_6_2 pure hmn A b)) = toEuclideanLin A.pinv (toLp 2 b) := by
  obtain ⟨hQR, -⟩ := algorithm_5_2_1_spec hmn Aᵀ
  have hQeq := (equation_5_1_4_beta hmn Aᵀ).2 hβ
  set st := Id.run (algorithm_5_2_1 pure Aᵀ) with hst
  set R₁ := (upperPart st.1).firstRows hmn with hR₁
  set Q₁ := (factoredQ st.2 st.1).firstColumns hmn with hQ₁
  have hAt : LinearIndependent ℝ Aᵀᵀ := by rwa [transpose_transpose]
  have hRu : IsUnit R₁ := hQR.isUnit_firstRows_of_linearIndependent hmn hAt
  have hup := hQR.isUpperTriangular_firstRows hmn
  have hdiag := hQR.firstRows_diag_ne_zero_of_linearIndependent hmn hAt
  have hthin := hQR.isThinQR hmn
  have hpinv : A.pinv = Q₁ * (R₁ᵀ)⁻¹ := by
    have := pinv_eq_of_isThinQR_conjTranspose (A := A)
      (by rwa [conjTranspose_eq_transpose_of_trivial]) hRu
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hQ₁ : Id.run (factoredQFirstColumns pure st.1 m) = Q₁ := by
    have e := equation_5_1_5 (k := m) hmn hmn st.1
    rw [e, ← hQeq]
    rfl
  set z := Id.run (Chapter03.algorithm_3_1_1 pure R₁ᵀ b) with hz
  have hzs : R₁ᵀ *ᵥ z = b := Chapter03.algorithm_3_1_1_spec
    (fun i j hij => hup hij) (fun i => hdiag i) b
  have hRt : IsUnit R₁ᵀ := (isUnit_transpose _).2 hRu
  have hz' : z = (R₁ᵀ)⁻¹ *ᵥ b := by
    rw [← hzs, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hRt), one_mulVec]
  have hrun : Id.run (algorithm_5_6_2 pure hmn A b) = Q₁ *ᵥ z := by
    simp only [algorithm_5_6_2, Id.run_bind]
    rw [← hst, hQ₁, Chapter01.algorithm_1_1_3_spec, zero_add]
  have hx : Id.run (algorithm_5_6_2 pure hmn A b) = A.pinv *ᵥ b := by
    rw [hrun, hz', hpinv, mulVec_mulVec]
  refine ⟨?_, by rw [hx, toEuclideanLin_toLp]⟩
  have hQQ : Q₁ᵀ * Q₁ = 1 := by
    have := hthin.conjTranspose_mul_self
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hAQ : A * Q₁ = R₁ᵀ := by
    have e : A = R₁ᵀ * Q₁ᵀ := by rw [← transpose_mul, hthin.mul_eq, transpose_transpose]
    rw [e, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  rw [hrun, mulVec_mulVec, hAQ, hzs]

end Underdetermined

/-! ### §5.6.3 Perturbed underdetermined systems -/

section Perturbation

open scoped Matrix.Norms.L2Operator

/-- **Theorem 5.6.1, rigorous form**: for `A ∈ ℝ^{m×n}` with `rank A = m ≤ n` (independent rows),
`‖δA‖₂ < σ_m(A)`, `b ≠ 0`, and `x`, `x̂` the minimum norm solutions of `Ax = b`,
`(A + δA)x̂ = b + δb`: with `ε_A = ‖δA‖₂/‖A‖₂`, `ε_b = ‖δb‖₂/‖b‖₂`,
`‖x̂ - x‖₂/‖x‖₂ ≤ ‖A‖₂/(σ_m(A) - ‖δA‖₂) (ε_A + ε_b) + [m < n] κ₂(A) ε_A` — the book's
`κ₂(A)(ε_A min{2, n - m + 1} + ε_b)` with `σ_m(A)` replaced by `σ_m(A) - ‖δA‖₂` in the first
term and no `O(ε²)` (`theorem_5_6_1_firstOrder` is the printed form). `σ_m(A)` is
`⨅ i, Aᵀ.colSingularValues i`. -/
theorem theorem_5_6_1 {A δA : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A)
    {b δb : EuclideanSpace ℝ (Fin m)} {x x' : EuclideanSpace ℝ (Fin n)}
    (hδA : ‖δA‖ < ⨅ i, Aᵀ.colSingularValues i) (hb : b ≠ 0) (hx : x = toEuclideanLin A.pinv b)
    (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb)) :
    ‖x' - x‖ / ‖x‖ ≤ ‖A‖ / ((⨅ i, Aᵀ.colSingularValues i) - ‖δA‖) * (‖δA‖ / ‖A‖ + ‖δb‖ / ‖b‖) +
      if m < n then kappa2 A * (‖δA‖ / ‖A‖) else 0 := by
  have h := (norm_minNorm_sub_le hA (by rwa [conjTranspose_eq_transpose_of_trivial]) hb hx hx').2
  simp only [kappa2]
  simpa only [conjTranspose_eq_transpose_of_trivial, Fintype.card_fin] using h

/-- For independent rows, `κ₂(A) = ‖A‖₂/σ_m(A)`. -/
private theorem kappa2_eq_div_of_rows [NeZero m] {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ A) : kappa2 A = ‖A‖ / ⨅ i, Aᵀ.colSingularValues i := by
  have hAt : LinearIndependent ℝ Aᵀᵀ := by rwa [transpose_transpose]
  have hp : A.pinv = (Aᵀ.pinv)ᵀ := by
    have := pinv_conjTranspose (A := Aᵀ)
    rw [conjTranspose_eq_transpose_of_trivial, conjTranspose_eq_transpose_of_trivial,
      transpose_transpose] at this
    rw [this]
  rw [kappa2, pinvCondNumberLp, lpOpNorm_two, lpOpNorm_two, hp,
    ← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose,
    l2_opNorm_pinv_eq_inv_iInf_colSingularValues hAt, div_eq_mul_inv]

/-- **Theorem 5.6.1** as printed, the `+ O(ε²)` reading: for `A` with `rank A = m ≤ n` and
`b ≠ 0` there are `K` and `ε₀ > 0` such that for all perturbations with
`ε = max(ε_A, ε_b) ≤ ε₀`,
`‖x̂ - x‖₂/‖x‖₂ ≤ κ₂(A)(ε_A min{2, n - m + 1} + ε_b) + K ε²`. -/
theorem theorem_5_6_1_firstOrder {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A)
    {b : EuclideanSpace ℝ (Fin m)} (hb : b ≠ 0) :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ (δA : Matrix (Fin m) (Fin n) ℝ) (δb : EuclideanSpace ℝ (Fin m)),
      max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) ≤ ε₀ →
      ‖toEuclideanLin (A + δA).pinv (b + δb) - toEuclideanLin A.pinv b‖ /
          ‖toEuclideanLin A.pinv b‖ ≤
        kappa2 A * (‖δA‖ / ‖A‖ * (min 2 (n - m + 1) : ℕ) + ‖δb‖ / ‖b‖) +
          K * max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) ^ 2 := by
  have hm : NeZero m := ⟨fun hm => hb (by subst hm; ext i; exact i.elim0)⟩
  have hAt : LinearIndependent ℝ Aᵀᵀ := by rwa [transpose_transpose]
  have hσ : 0 < ⨅ i, Aᵀ.colSingularValues i := iInf_colSingularValues_pos_of_linearIndependent hAt
  have hAn : 0 < ‖A‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    have := hA.ne_zero (0 : Fin m)
    rw [h0] at this
    exact this rfl
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hκ := kappa2_eq_div_of_rows hA
  have hmn : m ≤ n := by
    have := hA.fintype_card_le_finrank
    simpa using this
  set σ := ⨅ i, Aᵀ.colSingularValues i with hσdef
  set a := ‖A‖ with ha
  refine ⟨4 * a ^ 2 / σ ^ 2, σ / (2 * a), by positivity, fun δA δb hε => ?_⟩
  set ε := max (‖δA‖ / a) (‖δb‖ / ‖b‖) with hεdef
  obtain ⟨hεA, hεb, hε0⟩ := le_max_div_mul (δA := δA) (δb := δb) hAn hbn
  have ht : 2 * (ε * a) ≤ σ := by
    rw [le_div_iff₀ (by positivity)] at hε
    linarith
  have hδA : ‖δA‖ < σ := by nlinarith
  have h := theorem_5_6_1 (δb := δb) hA hδA hb rfl rfl
  obtain ⟨hu, -⟩ := one_div_le_add_of_sub_le hσ (by positivity) ht
    (show σ - ε * a ≤ σ - ‖δA‖ by linarith)
  set εA := ‖δA‖ / a with hεA'
  set εb := ‖δb‖ / ‖b‖ with hεb'
  have hεA0 : 0 ≤ εA := div_nonneg (norm_nonneg _) hAn.le
  have hεb0 : 0 ≤ εb := div_nonneg (norm_nonneg _) hbn.le
  have hεAε : εA ≤ ε := le_max_left _ _
  have hεbε : εb ≤ ε := le_max_right _ _
  have hfirst : a / (σ - ‖δA‖) * (εA + εb) ≤ kappa2 A * (εA + εb) + 4 * a ^ 2 / σ ^ 2 * ε ^ 2 := by
    have h1 : a / (σ - ‖δA‖) ≤ a / σ + 2 * (ε * a) / σ ^ 2 * a := by
      rw [div_eq_mul_one_div a (σ - ‖δA‖), div_eq_mul_one_div a σ]
      calc a * (1 / (σ - ‖δA‖)) ≤ a * (1 / σ + 2 * (ε * a) / σ ^ 2) :=
            mul_le_mul_of_nonneg_left hu hAn.le
        _ = a * (1 / σ) + 2 * (ε * a) / σ ^ 2 * a := by ring
    calc a / (σ - ‖δA‖) * (εA + εb) ≤ (a / σ + 2 * (ε * a) / σ ^ 2 * a) * (εA + εb) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = kappa2 A * (εA + εb) + 2 * a ^ 2 / σ ^ 2 * ε * (εA + εb) := by
          rw [hκ]
          ring
      _ ≤ kappa2 A * (εA + εb) + 2 * a ^ 2 / σ ^ 2 * ε * (2 * ε) := by
          gcongr
          linarith
      _ = kappa2 A * (εA + εb) + 4 * a ^ 2 / σ ^ 2 * ε ^ 2 := by ring
  refine h.trans ?_
  rcases lt_or_eq_of_le hmn with hlt | heq
  · have hmin : ((min 2 (n - m + 1) : ℕ) : ℝ) = 2 := by
      rw [min_eq_left (by omega)]
      norm_num
    rw [ite_eq_left hlt, hmin]
    linarith
  · subst heq
    have hmin : ((min 2 (m - m + 1) : ℕ) : ℝ) = 1 := by simp
    rw [ite_eq_right (lt_irrefl _), hmin]
    linarith

end Perturbation

/-- **(5.6.2)**: with `x(t) = (A + tE)ᵀ((A + tE)(A + tE)ᵀ)⁻¹(b + tf)`, the minimum norm solution
of `(A + tE) x = b + tf` for `A` of full row rank and small `t`,
`ẋ(0) = (I - Aᵀ(AAᵀ)⁻¹A) Eᵀ (AAᵀ)⁻¹ b + Aᵀ(AAᵀ)⁻¹ (f - E x)`, `x = x(0)`. -/
theorem equation_5_6_2 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A)
    (E : Matrix (Fin m) (Fin n) ℝ) (b f : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ =>
        toEuclideanLin ((A + t • E)ᵀ * ((A + t • E) * (A + t • E)ᵀ)⁻¹) (b + t • f))
      (toEuclideanLin ((1 - Aᵀ * (A * Aᵀ)⁻¹ * A) * Eᵀ * (A * Aᵀ)⁻¹) b +
        toEuclideanLin (Aᵀ * (A * Aᵀ)⁻¹)
          (f - toEuclideanLin E (toEuclideanLin (Aᵀ * (A * Aᵀ)⁻¹) b))) 0 := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using hasDerivAt_minNorm_line hA E b f

end GolubVanLoan.Chapter05
