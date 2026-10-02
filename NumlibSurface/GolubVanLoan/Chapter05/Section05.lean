import NumlibSurface.GolubVanLoan.Chapter05.Section04

/-!
# Golub–Van Loan §5.5: the rank-deficient least-squares problem

Surface file for [golub2013matrix] §5.5: the convex solution set and its minimal-norm element,
also through a complete orthogonal decomposition (§5.5.1), the SVD solution (Theorem 5.5.1,
(5.5.1)–(5.5.2)), the pseudoinverse and its characterizations (§5.5.2, (5.5.3), the Moore–Penrose
conditions), its sensitivity (§5.5.3: Wedin's bound and the discontinuity example), the truncated
SVD solution (§5.5.4), basic solutions from QR with column pivoting (§5.5.5, (5.5.4)–(5.5.5)) and
SVD-based subset selection (§5.5.7, Theorem 5.5.2, Algorithm 5.5.1 and its specification) and the
residual comparison of §5.5.8 (Theorem 5.5.3).

## Conventions

The pseudoinverse is the backbone's `Matrix.pinv`; the book's definition `A⁺ = V Σ⁺ Uᵀ` is the
theorem `pseudoinverse_eq_svd`. An SVD is `Matrix.IsSVD A U σ V` (`Uᵀ A V = Σ`, `σ` sorted and
nonnegative), `u_i`, `v_i` are the columns of `U`, `V`, 0-based. Least-squares statements are on
`EuclideanSpace ℝ (Fin m)`. A QR factorization with column pivoting `A Π = QR`,
`R = [R₁₁ R₁₂; 0 0]` with `R₁₁` nonsingular, is the backbone's
`Matrix.IsPivotedQR.IsRankRevealing A Q R π r` (`A Π = A.submatrix id π`), a complete orthogonal
decomposition is `Matrix.IsCompleteOrthogonal`; `x_B` is `Matrix.pivotedBasicSolution`.

## Book slips carried

"`z ∈ hull(A)`" (§5.5.1) is `z ∈ null(A)`; (5.5.3)'s `X ∈ ℝ^{m×n}` is `ℝ^{n×m}`; the
discontinuity example's `(A + δA)⁺` has a spurious `1` in position `(2, 1)`.

## Not formalized

The second bound of §5.5.4 (its middle term cannot be right as printed and no derivation is given),
the flop table of §5.5.6, the `δ`-rank display of §5.5.4 (misprinted; the definition is (5.4.5)),
the unstable-subset example (numerical), and "column pivoting tends to produce a well-conditioned
`R₁₁`" (heuristic).
-/

open Matrix WithLp

namespace GolubVanLoan.Chapter05

variable {m n : ℕ}

/-! ### §5.5.1 The minimum norm solution -/

section MinNorm

/-- **§5.5.1**: the set `𝒳 = {x : ‖Ax - b‖₂ = min}` of least-squares minimizers is convex, and it
has a unique element of minimum 2-norm, `x_LS = A⁺ b`. -/
theorem minNorm_existsUnique (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    Convex ℝ {x | IsLeastSquaresSolution A b x} ∧
      IsMinNormLeastSquaresSolution A b (toEuclideanLin A.pinv b) ∧
      ∀ x, IsMinNormLeastSquaresSolution A b x → x = toEuclideanLin A.pinv b :=
  ⟨convex_setOf_isLeastSquaresSolution A b, isMinNormLeastSquaresSolution_pinv A b,
    fun _ hx => hx.unique (isMinNormLeastSquaresSolution_pinv A b)⟩

/-- **§5.5.1, least squares through a complete orthogonal decomposition**: if
`Qᵀ A Z = T = [T₁₁ 0; 0 0]` (`r = rank A`, `T₁₁` nonsingular) and `Qᵀb = [c; d]`, then
`x_LS = Z [T₁₁⁻¹ c; 0]` is the minimal-norm least-squares solution and `‖A x_LS - b‖₂ = ‖d‖₂`;
for every `x`, with `Zᵀ x = [w; y]`, `‖Ax - b‖₂² = ‖T₁₁ w - c‖₂² + ‖d‖₂²`. -/
theorem minNorm_of_completeOrthogonal {A : Matrix (Fin m) (Fin n) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {Z : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    (h : IsCompleteOrthogonal A Q Z r) (b : EuclideanSpace ℝ (Fin m)) :
    (∀ x : EuclideanSpace ℝ (Fin n), ‖toEuclideanLin A x - b‖ ^ 2 =
      ∑ i : Fin r, (((Qᵀ * A * Z).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols) *ᵥ
          fun k => (Zᵀ *ᵥ ofLp x) (Fin.castLE h.le_cols k)) i -
        (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) ^ 2 +
      ∑ j : Fin (m - r), (Qᵀ *ᵥ ofLp b) (tailIdx h.le_rows j) ^ 2) ∧
    IsMinNormLeastSquaresSolution A b (toLp 2 (Z *ᵥ blockVec h.le_cols
      (((Qᵀ * A * Z).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *ᵥ
        fun i => (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) 0)) ∧
    ‖toEuclideanLin A (toLp 2 (Z *ᵥ blockVec h.le_cols
      (((Qᵀ * A * Z).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *ᵥ
        fun i => (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) 0)) - b‖ =
      ‖(toLp 2 fun j => (Qᵀ *ᵥ ofLp b) (tailIdx h.le_rows j) :
        EuclideanSpace ℝ (Fin (m - r)))‖ := by
  have hmin := h.isMinNormLeastSquaresSolution b
  simp only [conjTranspose_eq_transpose_of_trivial] at hmin
  refine ⟨fun x => ?_, hmin⟩
  have hsplit := norm_toEuclideanLin_sub_sq_eq_of_eq_mul h.mem_unitaryGroup_left h.le_rows
    h.eq_mul (fun i j hi => h.apply_eq_zero i j (Or.inl hi)) b x
  simp only [conjTranspose_eq_transpose_of_trivial, Real.norm_eq_abs, sq_abs] at hsplit
  rw [hsplit]
  have hz : ∀ (i : Fin m) (j : Fin n), r ≤ (j : ℕ) → (Qᵀ * A * Z) i j = 0 := fun i j hj => by
    simpa only [conjTranspose_eq_transpose_of_trivial] using h.apply_eq_zero i j (Or.inr hj)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [mulVec, dotProduct, sum_eq_sum_castLE_add_sum_tailIdx h.le_cols]
  have htail : ∑ j : Fin (n - r), (Qᵀ * A * Z) (Fin.castLE h.le_rows i) (tailIdx h.le_cols j) *
      (Zᵀ *ᵥ ofLp x) (tailIdx h.le_cols j) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hz _ _ (by simp), zero_mul]
  rw [htail, add_zero]
  rfl

end MinNorm

/-! ### Theorem 5.5.1 and the pseudoinverse -/

section SVD

variable {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
  {V : Matrix (Fin n) (Fin n) ℝ}

/-- The pseudoinverse from an SVD applied to `b`, for any shape:
`A⁺ b = ∑_{j < min(m,n)} (u_jᵀ b / σ_j) v_j`. -/
private theorem pinv_mulVec_eq_sum_dite (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    A.pinv *ᵥ b = ∑ j : Fin n,
      (if hj : (j : ℕ) < m then (U.col ⟨j, hj⟩ ⬝ᵥ b) / σ j else 0) • V.col j := by
  rw [h.pinv_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [RCLike.ofReal_real_eq_id, id]
  have hD : ∀ j : Fin n, ((rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) *ᵥ
      (star U *ᵥ b)) j = if hj : (j : ℕ) < m then (U.col ⟨j, hj⟩ ⬝ᵥ b) / σ j else 0 := by
    intro j
    simp only [mulVec, dotProduct, rectDiagonal, of_apply, ite_mul, zero_mul]
    split_ifs with hj
    · rw [Finset.sum_eq_single ⟨j, hj⟩ (fun i _ hi => by
        rw [ite_eq_right (fun e => hi (Fin.ext e.symm))]) (by simp)]
      simp only [↓reduceIte, star_apply, star_trivial, col_apply]
      rw [div_eq_inv_mul]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [ite_eq_right (fun e => hj (by have := i.isLt; omega))]
  ext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col_apply]
  change ∑ j, V p j * _ = _
  simp only [hD, mul_comm]

/-- **(5.5.1)**: if `Uᵀ A V = Σ` is an SVD of `A ∈ ℝ^{m×n}` with `r = rank(A)`, then
`x_LS = ∑_{i=1}^{r} (u_iᵀ b / σ_i) v_i` minimizes `‖Ax - b‖₂` and has the smallest 2-norm of all
minimizers; it is `A⁺ b`. -/
theorem equation_5_5_1 (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    ∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
        V.col (Fin.castLE (rank_le_width A) i) = A.pinv *ᵥ b ∧
      IsMinNormLeastSquaresSolution A (toLp 2 b)
        (toLp 2 (∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
          V.col (Fin.castLE (rank_le_width A) i))) := by
  have hsum : ∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
      V.col (Fin.castLE (rank_le_width A) i) = A.pinv *ᵥ b := by
    rw [pinv_mulVec_eq_sum_dite h b]
    set g : Fin n → Fin n → ℝ := fun j =>
      (if hj : (j : ℕ) < m then (U.col ⟨j, hj⟩ ⬝ᵥ b) / σ j else 0) • V.col j with hg
    have h1 : ∀ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
        V.col (Fin.castLE (rank_le_width A) i) = g (Fin.castLE (rank_le_width A) i) := by
      intro i
      have hi : ((Fin.castLE (rank_le_width A) i : Fin n) : ℕ) < m :=
        lt_of_lt_of_le i.isLt (rank_le_height A)
      simp only [hg, hi, ↓reduceDIte]
      rfl
    rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_castLE_eq_sum_ite]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hjr
    · rfl
    · simp only [hg]
      split_ifs with hjm
      · rw [h.singularValues_eq hjm j.isLt,
          (sortedSingularValues_eq_zero_iff_rank_le (A := A) _).2 (not_lt.1 hjr), div_zero,
          zero_smul]
      · rw [zero_smul]
  refine ⟨hsum, ?_⟩
  rw [hsum, ← toEuclideanLin_toLp]
  exact isMinNormLeastSquaresSolution_pinv A (toLp 2 b)

/-- **(5.5.2)**: `ρ_LS² = ‖A x_LS - b‖₂² = ∑_{i=r+1}^{m} (u_iᵀ b)²`. -/
theorem equation_5_5_2 (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    ‖toEuclideanLin A (toLp 2 (A.pinv *ᵥ b)) - toLp 2 b‖ ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => A.rank ≤ (i : ℕ)), (U.col i ⬝ᵥ b) ^ 2 := by
  rw [← toEuclideanLin_toLp, norm_sub_sq_pinv_eq_sum_of_isSVD h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_toLp_toLp, Real.norm_eq_abs, sq_abs]
  simp only [star_trivial, dotProduct_comm]
  rfl

/-- **Theorem 5.5.1**: for an SVD `Uᵀ A V = Σ` of `A ∈ ℝ^{m×n}` with `r = rank(A)`,
`x_LS = ∑_{i=1}^{r} (u_iᵀ b / σ_i) v_i` minimizes `‖Ax - b‖₂` and has the smallest 2-norm of all
minimizers, and `ρ_LS² = ∑_{i=r+1}^{m} (u_iᵀ b)²`. -/
theorem theorem_5_5_1 (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    IsMinNormLeastSquaresSolution A (toLp 2 b)
        (toLp 2 (∑ i : Fin A.rank, ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
          V.col (Fin.castLE (rank_le_width A) i))) ∧
      ‖toEuclideanLin A (toLp 2 (∑ i : Fin A.rank,
          ((U.col (Fin.castLE (rank_le_height A) i) ⬝ᵥ b) / σ i) •
            V.col (Fin.castLE (rank_le_width A) i))) - toLp 2 b‖ ^ 2 =
        ∑ i ∈ Finset.univ.filter (fun i : Fin m => A.rank ≤ (i : ℕ)), (U.col i ⬝ᵥ b) ^ 2 := by
  obtain ⟨hsum, hmin⟩ := equation_5_5_1 h b
  exact ⟨hmin, by rw [hsum]; exact equation_5_5_2 h b⟩

/-- **§5.5.2, the pseudoinverse from the SVD**: `A⁺ = V Σ⁺ Uᵀ` with
`Σ⁺ = diag(1/σ₁, …, 1/σ_r, 0, …, 0) ∈ ℝ^{n×m}` (`1/0 = 0`); `x_LS = A⁺ b` and
`ρ_LS = ‖(I - AA⁺) b‖₂`; `A⁺ = (AᵀA)⁻¹Aᵀ` if `rank(A) = n`; `A⁺ = A⁻¹` if `A` is square and
nonsingular. -/
theorem pseudoinverse_eq_svd (h : IsSVD A U σ V) (b : Fin m → ℝ) :
    A.pinv = V * (rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ ∧
      IsMinNormLeastSquaresSolution A (toLp 2 b) (toLp 2 (A.pinv *ᵥ b)) ∧
      ‖toEuclideanLin A (toLp 2 (A.pinv *ᵥ b)) - toLp 2 b‖ =
        ‖(toLp 2 ((1 - A * A.pinv) *ᵥ b) : EuclideanSpace ℝ (Fin m))‖ ∧
      (LinearIndependent ℝ Aᵀ → A.pinv = (Aᵀ * A)⁻¹ * Aᵀ) := by
  refine ⟨?_, ?_, ?_, fun hA => ?_⟩
  · have := h.pinv_eq
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, id] using this
  · rw [← toEuclideanLin_toLp]; exact isMinNormLeastSquaresSolution_pinv A (toLp 2 b)
  · rw [toEuclideanLin_toLp, ← norm_neg, neg_sub, ← WithLp.toLp_sub, mulVec_mulVec,
      sub_mulVec, one_mulVec]
  · have := pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA
    rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **§5.5.2**: `A⁺ = A⁻¹` if `m = n = rank(A)`. -/
theorem pseudoinverse_eq_inv {B : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B) : B.pinv = B⁻¹ :=
  pinv_eq_inv hB

/-- **(5.5.3)**: `A⁺` is the unique minimal-Frobenius-norm solution of
`min_{X ∈ ℝ^{n×m}} ‖AX - I_m‖_F` (the book prints `X ∈ ℝ^{m×n}`). -/
theorem equation_5_5_3 (A : Matrix (Fin m) (Fin n) ℝ) :
    letI := Matrix.frobeniusNormedAddCommGroup (m := Fin m) (n := Fin m) (α := ℝ)
    letI := Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin m) (α := ℝ)
    (∀ X : Matrix (Fin n) (Fin m) ℝ, ‖A * A.pinv - 1‖ ≤ ‖A * X - 1‖) ∧
      ∀ X : Matrix (Fin n) (Fin m) ℝ,
        ‖A * X - 1‖ = ‖A * A.pinv - 1‖ → ‖A.pinv‖ ≤ ‖X‖ ∧ (‖X‖ = ‖A.pinv‖ → X = A.pinv) :=
  ⟨fun X => isMinOn_iff.1 (isMinOn_norm_mul_sub_one_pinv A).1 X (Set.mem_univ X),
    (isMinOn_norm_mul_sub_one_pinv A).2⟩

/-- **§5.5.2, the Moore–Penrose conditions**: `A⁺` is the unique `X ∈ ℝ^{n×m}` with
(i) `AXA = A`, (ii) `XAX = X`, (iii) `(AX)ᵀ = AX`, (iv) `(XA)ᵀ = XA`; and `AA⁺` is the orthogonal
projection onto `ran(A)`. -/
theorem moorePenrose (A : Matrix (Fin m) (Fin n) ℝ) :
    A * A.pinv * A = A ∧ A.pinv * A * A.pinv = A.pinv ∧ (A * A.pinv)ᵀ = A * A.pinv ∧
      (A.pinv * A)ᵀ = A.pinv * A ∧
      (∀ X : Matrix (Fin n) (Fin m) ℝ, A * X * A = A → X * A * X = X → (A * X)ᵀ = A * X →
        (X * A)ᵀ = X * A → X = A.pinv) ∧
      toEuclideanLin (A * A.pinv) = ((toEuclideanLin A).range.starProjection : _ →ₗ[ℝ] _) := by
  have h3 : (A * A.pinv)ᵀ = A * A.pinv := by
    have := (isHermitian_mul_pinv (A := A)).eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have h4 : (A.pinv * A)ᵀ = A.pinv * A := by
    have := (isHermitian_pinv_mul (A := A)).eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨mul_pinv_mul_self A, pinv_mul_self_mul_pinv A, h3, h4, fun X h1 h2 h3' h4' =>
    pinv_unique A h1 h2 ?_ ?_, mul_pinv_eq_starProjection A⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact h3'
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact h4'

end SVD

/-! ### §5.5.3 The perturbation of the pseudoinverse -/

section PinvPerturbation

open scoped Matrix.Norms.Frobenius

/-- **§5.5.3, the perturbation of the pseudoinverse** (Wedin 1973, Stewart 1975):
`‖(A + δA)⁺ - A⁺‖_F ≤ 2 ‖δA‖_F max{‖A⁺‖₂², ‖(A + δA)⁺‖₂²}`, the spectral norms written
`lpOpNorm 2`. -/
theorem pinv_perturbation (A δA : Matrix (Fin m) (Fin n) ℝ) :
    ‖(A + δA).pinv - A.pinv‖ ≤ 2 * ‖δA‖ *
      max (lpOpNorm 2 A.pinv ^ 2) (lpOpNorm 2 (A + δA).pinv ^ 2) :=
  frobenius_norm_pinv_sub_le A δA

end PinvPerturbation

/-- The matrix `A = [1 0; 0 0; 0 0]` of §5.5.3's example. -/
def pinvExampleA : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0]

/-- The perturbation `δA = [0 0; 0 ε; 0 0]` of §5.5.3's example. -/
def pinvExampleE (ε : ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, ε; 0, 0]

/-- The pseudoinverse of `A + δA` in §5.5.3's example, for `ε ≠ 0`. -/
theorem pinv_pinvExample {ε : ℝ} (hε : ε ≠ 0) :
    (pinvExampleA + pinvExampleE ε).pinv = !![1, 0, 0; 0, 1 / ε, 0] := by
  symm
  refine pinv_unique (A := pinvExampleA + pinvExampleE ε) ?_ ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinvExampleA, pinvExampleE, Matrix.mul_apply, Fin.sum_univ_succ, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinvExampleA, pinvExampleE, Matrix.mul_apply, Fin.sum_univ_succ, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinvExampleA, pinvExampleE, Matrix.mul_apply, Fin.sum_univ_succ, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pinvExampleA, pinvExampleE, Matrix.mul_apply, Fin.sum_univ_succ, hε]

/-- The pseudoinverse of `A` in §5.5.3's example. -/
theorem pinv_pinvExampleA : pinvExampleA.pinv = !![1, 0, 0; 0, 0, 0] := by
  symm
  refine pinv_unique (A := pinvExampleA) ?_ ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pinvExampleA, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pinvExampleA, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pinvExampleA, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pinvExampleA, Matrix.mul_apply, Fin.sum_univ_succ]

open scoped Matrix.Norms.L2Operator in
/-- **§5.5.3's example, "`x_LS` is not even a continuous function of the data"**: for
`A = [1 0; 0 0; 0 0]` and `δA = [0 0; 0 ε; 0 0]` (`ε > 0`), `A⁺ = [1 0 0; 0 0 0]`,
`(A + δA)⁺ = [1 0 0; 0 1/ε 0]` (the book prints a spurious `1` in position `(2,1)`) and
`‖A⁺ - (A + δA)⁺‖₂ = 1/ε`; so the pseudoinverse is not continuous at `A`. -/
theorem pinv_discontinuity {ε : ℝ} (hε : 0 < ε) :
    pinvExampleA.pinv = !![1, 0, 0; 0, 0, 0] ∧
      (pinvExampleA + pinvExampleE ε).pinv = !![1, 0, 0; 0, 1 / ε, 0] ∧
      ‖pinvExampleA.pinv - (pinvExampleA + pinvExampleE ε).pinv‖ = 1 / ε ∧
      ¬ ContinuousAt (fun B : Matrix (Fin 3) (Fin 2) ℝ => B.pinv) pinvExampleA := by
  refine ⟨pinv_pinvExampleA, pinv_pinvExample hε.ne', ?_, ?_⟩
  · rw [pinv_pinvExampleA, pinv_pinvExample hε.ne']
    have hD : (!![1, 0, 0; 0, 0, 0] - !![1, 0, 0; 0, 1 / ε, 0] : Matrix (Fin 2) (Fin 3) ℝ) =
        !![0, 0, 0; 0, -(1 / ε), 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hD]
    set M : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 0; 0, -(1 / ε), 0] with hM
    have hMM : Mᴴᴴ * Mᴴ = diagonal ![0, (1 / ε) ^ 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_succ, sq]
    have hsq : ‖M‖ * ‖M‖ = (1 / ε) ^ 2 := by
      rw [← l2_opNorm_conjTranspose M, ← l2_opNorm_conjTranspose_mul_self, hMM,
        l2_opNorm_diagonal]
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_) ?_
      · fin_cases i <;> simp [sq_nonneg]
      · have := norm_le_pi_norm (![0, (1 / ε) ^ 2] : Fin 2 → ℝ) 1
        simpa using this
    have h0 : 0 ≤ ‖M‖ := norm_nonneg _
    nlinarith [show 0 < 1 / ε by positivity]
  · intro hc
    have hE : ∀ t : ℝ, pinvExampleA + pinvExampleE t =
        pinvExampleA + t • (!![0, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ) := by
      intro t
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pinvExampleE]
    have hf : ContinuousAt (fun t : ℝ => (pinvExampleA + pinvExampleE t).pinv 1 1) 0 := by
      simp only [hE]
      have hg : Continuous fun t : ℝ =>
          pinvExampleA + t • (!![0, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ) := by fun_prop
      have hpt : pinvExampleA + (0 : ℝ) • (!![0, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ) =
          pinvExampleA := by rw [zero_smul, add_zero]
      have := ContinuousAt.comp_of_eq hc hg.continuousAt hpt
      exact ((continuous_apply 1).comp (continuous_apply 1)).continuousAt.comp this
    rw [Metric.continuousAt_iff] at hf
    obtain ⟨δ, hδ, hδf⟩ := hf 1 one_pos
    set t := min (δ / 2) (1 / 2) with ht
    have ht0 : 0 < t := by positivity
    have htδ : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have := hδf htδ
    have hE0 : pinvExampleE 0 = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pinvExampleE]
    simp only [hE0, add_zero, pinv_pinvExampleA, pinv_pinvExample ht0.ne'] at this
    simp only [of_apply, cons_val', cons_val_one, cons_val_zero, empty_val',
      cons_val_fin_one, Real.dist_eq, sub_zero] at this
    have ht2 : t ≤ 1 / 2 := min_le_right _ _
    rw [abs_of_pos (by positivity)] at this
    rw [div_lt_one ht0] at this
    linarith

/-! ### §5.5.4 The truncated SVD solution -/

section TruncatedSVD

/-- **§5.5.4, the truncated SVD solution**: for computed factors `Û`, `Σ̂ = diag(σ̂_i)`, `V̂` and an
accepted `δ`-rank `r̂`, "`x_r̂ = ∑_{i=1}^{r̂} (û_iᵀ b / σ̂_i) v̂_i`" (0-based: the indices `i < r̂`;
indices beyond `min(m, n)` carry no term). -/
noncomputable def truncatedSVDSolution (U : Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (b : Fin m → ℝ) : Fin n → ℝ :=
  ∑ i : Fin n, if h : (i : ℕ) < r ∧ (i : ℕ) < m then ((U.col ⟨i, h.2⟩ ⬝ᵥ b) / σ i) • V.col i
    else 0

/-- Cauchy–Schwarz for the real dot product, with Euclidean norms. -/
private theorem abs_dotProduct_le_norm {k : ℕ} (x y : Fin k → ℝ) :
    |x ⬝ᵥ y| ≤
      ‖(toLp 2 x : EuclideanSpace ℝ (Fin k))‖ * ‖(toLp 2 y : EuclideanSpace ℝ (Fin k))‖ := by
  have := abs_real_inner_le_norm (toLp 2 x : EuclideanSpace ℝ (Fin k)) (toLp 2 y)
  simpa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using this

/-- The columns of an orthogonal matrix are orthonormal. -/
private theorem col_dotProduct_col_of_mem {k : ℕ} {Q : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q ∈ unitaryGroup (Fin k) ℝ) (i j : Fin k) :
    Q.col i ⬝ᵥ Q.col j = (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
  have := congrFun (congrFun (mem_unitaryGroup_iff'.1 hQ) i) j
  rw [← this]
  simp [mul_apply, dotProduct, col_apply]

/-- The columns of an orthogonal matrix have unit Euclidean norm. -/
private theorem norm_col_of_mem {k : ℕ} {Q : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q ∈ unitaryGroup (Fin k) ℝ) (j : Fin k) :
    ‖(toLp 2 (Q.col j) : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  have h1 := col_dotProduct_col_of_mem hQ j j
  rw [one_apply_eq, dotProduct_self_eq_norm_sq] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1

/-- **§5.5.4, the error of the truncated SVD solution**: under the book's simplifying assumptions
(`r = n`, `ΔA = 0` in (5.4.4), so `Σ̂ = Σ = Wᵀ A Z` with `W`, `Z` orthogonal — here an SVD
`IsSVD A W σ Z` with `n ≤ m`), if the computed singular vectors satisfy `‖w_i - û_i‖₂ ≤ ε` and
`‖z_i - v̂_i‖₂ ≤ ε` for `i ≤ r̂` and `σ_r̂ > 0`, then
`‖x_r̂ - x_LS‖₂ ≤ (r̂ / σ_r̂) 2(1 + ε) ε ‖b‖₂ + √(∑_{i=r̂+1}^{n} (w_iᵀ b / σ_i)²)`. -/
theorem norm_truncatedSVDSolution_sub_le {A : Matrix (Fin m) (Fin n) ℝ}
    {W : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {Z : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A W σ Z) (hnm : n ≤ m) {r : ℕ} (hr : r ≤ n) (hσ : 0 < σ (r - 1))
    {Uh : Matrix (Fin m) (Fin m) ℝ} {Vh : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ i : Fin n, (i : ℕ) < r → ‖(toLp 2 (W.col (Fin.castLE hnm i) -
      Uh.col (Fin.castLE hnm i)) : EuclideanSpace ℝ (Fin m))‖ ≤ ε)
    (hV : ∀ i : Fin n, (i : ℕ) < r →
      ‖(toLp 2 (Z.col i - Vh.col i) : EuclideanSpace ℝ (Fin n))‖ ≤ ε)
    (b : Fin m → ℝ) :
    ‖(toLp 2 (truncatedSVDSolution Uh σ Vh r b - A.pinv *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
      r / σ (r - 1) * (2 * (1 + ε) * ε * ‖(toLp 2 b : EuclideanSpace ℝ (Fin m))‖) +
        √(∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ (i : ℕ)),
          ((W.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) ^ 2) := by
  set nb := ‖(toLp 2 b : EuclideanSpace ℝ (Fin m))‖ with hnb
  set K := 2 * (1 + ε) * ε * nb with hK
  -- the two sums of the book's decomposition
  set D : Fin n → Fin n → ℝ := fun j => if (j : ℕ) < r then
      ((Uh.col (Fin.castLE hnm j) ⬝ᵥ b) / σ j) • Vh.col j -
        ((W.col (Fin.castLE hnm j) ⬝ᵥ b) / σ j) • Z.col j else 0 with hD
  set a : Fin n → ℝ := fun j => if r ≤ (j : ℕ) then (W.col (Fin.castLE hnm j) ⬝ᵥ b) / σ j
    else 0 with ha
  have hZa : Z *ᵥ a = ∑ j, a j • Z.col j := by
    ext p
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col_apply,
      mul_comm]
  have hsplit : truncatedSVDSolution Uh σ Vh r b - A.pinv *ᵥ b = ∑ j, D j - Z *ᵥ a := by
    rw [pinv_mulVec_eq_sum_of_isSVD h hnm b, truncatedSVDSolution, hZa,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
    by_cases hj : (j : ℕ) < r
    · simp only [hD, ha, hj, hjm, and_self, ↓reduceDIte, ↓reduceIte, not_le.2 hj, zero_smul,
        sub_zero]
      rfl
    · simp only [hD, ha, hj, false_and, ↓reduceDIte, ↓reduceIte, not_lt.1 hj]
  have hWu := h.mem_unitaryGroup_left
  have hZu := h.mem_unitaryGroup_right
  -- each term of the first sum
  have hDj : ∀ j : Fin n, ‖(toLp 2 (D j) : EuclideanSpace ℝ (Fin n))‖ ≤
      if (j : ℕ) < r then K / σ (r - 1) else 0 := by
    intro j
    by_cases hj : (j : ℕ) < r
    · simp only [hD, hj, ↓reduceIte]
      set u := Uh.col (Fin.castLE hnm j)
      set w := W.col (Fin.castLE hnm j)
      set v := Vh.col j
      set z := Z.col j
      have hσj : σ (r - 1) ≤ σ j := h.antitone (by omega)
      have hσj0 : 0 < σ (j : ℕ) := lt_of_lt_of_le hσ hσj
      have hid : ((u ⬝ᵥ b) / σ j) • v - ((w ⬝ᵥ b) / σ j) • z =
          (σ j)⁻¹ • ((u ⬝ᵥ b) • (v - z) + ((u - w) ⬝ᵥ b) • z) := by
        rw [sub_dotProduct, smul_sub, sub_smul, div_eq_inv_mul, div_eq_inv_mul, mul_smul,
          mul_smul, smul_add, smul_sub, smul_sub]
        abel
      have hw : ‖(toLp 2 w : EuclideanSpace ℝ (Fin m))‖ = 1 := norm_col_of_mem hWu _
      have hz : ‖(toLp 2 z : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_col_of_mem hZu _
      have huw : ‖(toLp 2 (u - w) : EuclideanSpace ℝ (Fin m))‖ ≤ ε := by
        rw [← neg_sub, toLp_neg, norm_neg]
        exact hU j hj
      have hvz : ‖(toLp 2 (v - z) : EuclideanSpace ℝ (Fin n))‖ ≤ ε := by
        rw [← neg_sub, toLp_neg, norm_neg]
        exact hV j hj
      have hu : ‖(toLp 2 u : EuclideanSpace ℝ (Fin m))‖ ≤ 1 + ε := by
        have : u = w + (u - w) := by abel
        rw [this, toLp_add]
        exact (norm_add_le _ _).trans (by rw [hw]; linarith)
      have hub : |u ⬝ᵥ b| ≤ (1 + ε) * nb :=
        (abs_dotProduct_le_norm u b).trans
          (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
      have huwb : |(u - w) ⬝ᵥ b| ≤ ε * nb :=
        (abs_dotProduct_le_norm _ b).trans
          (mul_le_mul_of_nonneg_right huw (norm_nonneg _))
      rw [hid, toLp_smul, norm_smul, toLp_add, toLp_smul, toLp_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hσj0]
      have hsum : ‖(toLp 2 ((u ⬝ᵥ b) • (v - z)) : EuclideanSpace ℝ (Fin n)) +
          toLp 2 (((u - w) ⬝ᵥ b) • z)‖ ≤ K := by
        refine (norm_add_le _ _).trans ?_
        rw [toLp_smul, toLp_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hz,
          mul_one]
        have hnb0 : 0 ≤ nb := norm_nonneg _
        have h1 : |u ⬝ᵥ b| * ‖(toLp 2 (v - z) : EuclideanSpace ℝ (Fin n))‖ ≤ (1 + ε) * nb * ε :=
          mul_le_mul hub hvz (norm_nonneg _) (by positivity)
        have h2 : ε * nb ≤ (1 + ε) * ε * nb := by nlinarith [mul_nonneg hε hnb0]
        rw [hK]
        nlinarith
      have hK0 : 0 ≤ K := by positivity
      calc (σ j)⁻¹ * ‖(toLp 2 ((u ⬝ᵥ b) • (v - z)) : EuclideanSpace ℝ (Fin n)) +
            toLp 2 (((u - w) ⬝ᵥ b) • z)‖ ≤ (σ j)⁻¹ * K :=
            mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hσj0.le)
        _ ≤ (σ (r - 1))⁻¹ * K :=
            mul_le_mul_of_nonneg_right ((inv_le_inv₀ hσj0 hσ).2 hσj) hK0
        _ = K / σ (r - 1) := by rw [div_eq_inv_mul]
    · simp [hD, hj]
  -- the first sum
  have hfirst : ‖(toLp 2 (∑ j, D j) : EuclideanSpace ℝ (Fin n))‖ ≤ r / σ (r - 1) * K := by
    rw [toLp_sum]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => hDj j).trans (le_of_eq ?_))
    rw [← Fin.sum_castLE_eq_sum_ite hr (fun _ => K / σ (r - 1))]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- the tail
  have hZZ : Zᵀ * Z = 1 := by
    have := mem_unitaryGroup_iff'.1 hZu
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have htail : ‖(toLp 2 (Z *ᵥ a) : EuclideanSpace ℝ (Fin n))‖ =
      √(∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ (i : ℕ)),
        ((W.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) ^ 2) := by
    have h1 : (Z *ᵥ a) ⬝ᵥ (Z *ᵥ a) = a ⬝ᵥ a := by
      rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hZZ, vecMul_one]
    have h2 : a ⬝ᵥ a = ∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ (i : ℕ)),
        ((W.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) ^ 2 := by
      rw [Finset.sum_filter, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ha]
      split_ifs <;> ring
    rw [← h2, ← h1, dotProduct_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hsplit, toLp_sub, ← htail]
  exact (norm_sub_le _ _).trans (add_le_add hfirst le_rfl)

end TruncatedSVD

/-! ### §5.5.5 Basic solutions via QR with column pivoting -/

section Basic

open scoped Matrix.Norms.L2Operator

variable {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
  {R : Matrix (Fin m) (Fin n) ℝ} {π : Equiv.Perm (Fin n)} {r : ℕ}

/-- **§5.5.5, basic solutions via QR with column pivoting**: if `A Π = QR` with
`R = [R₁₁ R₁₂; 0 0]`, `R₁₁` nonsingular of order `r = rank A` (the factorization (5.4.6)) and
`Qᵀb = [c; d]`, then for every `x`, with `Πᵀx = [y; z]`,
`‖Ax - b‖₂² = ‖R₁₁ y + R₁₂ z - c‖₂² + ‖d‖₂²`; `x` is a least-squares minimizer iff
`R₁₁ y + R₁₂ z = c`, i.e. `x = Π [R₁₁⁻¹(c - R₁₂ z); z]`; and the basic solution
`x_B = Π [R₁₁⁻¹ c; 0]` (`Matrix.pivotedBasicSolution`) is a minimizer with at most `r` nonzero
components. -/
theorem basicSolution (h : IsPivotedQR.IsRankRevealing A Q R π r)
    (b : EuclideanSpace ℝ (Fin m)) :
    (∀ x : EuclideanSpace ℝ (Fin n), ‖toEuclideanLin A x - b‖ ^ 2 =
      ∑ i : Fin r, ((R *ᵥ (ofLp x ∘ π)) (Fin.castLE h.le_rows i) -
        (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) ^ 2 +
      ∑ j : Fin (m - r), (Qᵀ *ᵥ ofLp b) (tailIdx h.le_rows j) ^ 2) ∧
    (∀ x : EuclideanSpace ℝ (Fin n), IsLeastSquaresSolution A b x ↔ ∀ i : Fin r,
      (R *ᵥ (ofLp x ∘ π)) (Fin.castLE h.le_rows i) = (Qᵀ *ᵥ ofLp b) (Fin.castLE h.le_rows i)) ∧
    IsLeastSquaresSolution A b (pivotedBasicSolution Q R π h.le_rows h.le_cols b) ∧
    ∀ j : Fin (n - r), pivotedBasicSolution Q R π h.le_rows h.le_cols b (π (tailIdx h.le_cols j)) =
      0 := by
  refine ⟨fun x => ?_, fun x => ?_, (h.isLeastSquaresSolution_basic b).1,
    (h.isLeastSquaresSolution_basic b).2⟩
  · have hsplit := norm_toEuclideanLin_sub_sq_eq_of_eq_mul h.isQR.mem_unitaryGroup h.le_rows
      h.eq_mul h.apply_eq_zero b x
    simpa only [one_submatrix_mulVec, conjTranspose_eq_transpose_of_trivial, Real.norm_eq_abs,
      sq_abs] using hsplit
  · have := h.isLeastSquaresSolution_iff (b := b) (x := x)
    simpa only [conjTranspose_eq_transpose_of_trivial] using this

/-- **(5.5.4)**: `‖x_LS‖₂ = min_{z ∈ ℝ^{n-r}} ‖x_B - Π [R₁₁⁻¹R₁₂; -I_{n-r}] z‖₂` (printed
`z ∈ ℝ^{n-2}`), over the factorization of `basicSolution`. -/
theorem equation_5_5_4 (h : IsPivotedQR.IsRankRevealing A Q R π r)
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖toEuclideanLin A.pinv b‖ = ⨅ z : Fin (n - r) → ℝ,
      ‖pivotedBasicSolution Q R π h.le_rows h.le_cols b - toLp 2 (blockVec h.le_cols
        (((R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *
          R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols)) *ᵥ z) (-z) ∘ π.symm)‖ :=
  h.norm_minNorm_eq_iInf b

/-- **§5.5.5**, "the basic solution is not the minimal 2-norm solution unless the submatrix `R₁₂`
is zero" — its converse half: when `R₁₂ = 0`, `x_B = x_LS` for every `b`. -/
theorem basicSolution_eq_pinv_of_eq_zero (h : IsPivotedQR.IsRankRevealing A Q R π r)
    (hR : R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols) = 0)
    (b : EuclideanSpace ℝ (Fin m)) :
    pivotedBasicSolution Q R π h.le_rows h.le_cols b = toEuclideanLin A.pinv b := by
  obtain ⟨-, hle⟩ := h.norm_basic_le b
  rw [hR, Matrix.mul_zero, norm_zero, sq, mul_zero, add_zero, Real.sqrt_one, one_mul] at hle
  refine IsMinNormLeastSquaresSolution.eq_pinv ⟨(h.isLeastSquaresSolution_basic b).1,
    fun y hy => hle.trans ?_⟩
  exact (isMinNormLeastSquaresSolution_pinv A b).2 y hy

/-- **(5.5.5)** (Golub–Pereyra): for `x_LS ≠ 0`,
`1 ≤ ‖x_B‖₂/‖x_LS‖₂ ≤ √(1 + ‖R₁₁⁻¹R₁₂‖₂²)`. -/
theorem equation_5_5_5 (h : IsPivotedQR.IsRankRevealing A Q R π r)
    (b : EuclideanSpace ℝ (Fin m)) (hx : toEuclideanLin A.pinv b ≠ 0) :
    1 ≤ ‖pivotedBasicSolution Q R π h.le_rows h.le_cols b‖ / ‖toEuclideanLin A.pinv b‖ ∧
      ‖pivotedBasicSolution Q R π h.le_rows h.le_cols b‖ / ‖toEuclideanLin A.pinv b‖ ≤
        √(1 + ‖(R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols))⁻¹ *
          R.submatrix (Fin.castLE h.le_rows) (tailIdx h.le_cols)‖ ^ 2) := by
  have hpos : 0 < ‖toEuclideanLin A.pinv b‖ := norm_pos_iff.2 hx
  obtain ⟨h1, h2⟩ := h.norm_basic_le b
  exact ⟨(one_le_div hpos).2 h1, (div_le_iff₀ hpos).2 h2⟩

end Basic

/-! ### §5.5.7 SVD-based subset selection -/

section SubsetSelection

open scoped Matrix.Norms.L2Operator

/-- **Theorem 5.5.2**: let `Uᵀ A V = Σ` be an SVD, `P` a permutation (`A P = A.submatrix id π`),
`B₁` the first `r̃` columns of `A P` (`1 ≤ r̃ ≤ rank A`), and `Ṽ₁₁` the leading `r̃ × r̃` block of
`PᵀV` ((5.5.6)), assumed nonsingular. Then `σ_r̃(A)/‖Ṽ₁₁⁻¹‖₂ ≤ σ_r̃(B₁) ≤ σ_r̃(A)` (1-based
`σ_r̃` is `sortedSingularValues (r̃ - 1)`). The upper bound is Corollary 2.4.5 iterated (the book
cites Corollary 2.4.4). -/
theorem theorem_5_5_2 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (π : Equiv.Perm (Fin n)) {r : ℕ}
    (hr0 : 0 < r) (hrA : r ≤ A.rank)
    (hV : IsUnit ((V.submatrix π id).submatrix (Fin.castLE (hrA.trans A.rank_le_width))
      (Fin.castLE (hrA.trans A.rank_le_width)))) :
    A.sortedSingularValues (r - 1) /
        ‖((V.submatrix π id).submatrix (Fin.castLE (hrA.trans A.rank_le_width))
          (Fin.castLE (hrA.trans A.rank_le_width)))⁻¹‖ ≤
      ((A.submatrix id π).submatrix id
        (Fin.castLE (hrA.trans A.rank_le_width))).sortedSingularValues (r - 1) ∧
    ((A.submatrix id π).submatrix id
        (Fin.castLE (hrA.trans A.rank_le_width))).sortedSingularValues (r - 1) ≤
      A.sortedSingularValues (r - 1) := by
  have hrN : r ≤ n := hrA.trans A.rank_le_width
  have hrM : r ≤ m := hrA.trans A.rank_le_height
  have hlow := h.sortedSingularValues_le_mul_submatrix π hr0 hrM hrN hV
  have hne : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  have hinv : 0 < ‖((V.submatrix π id).submatrix (Fin.castLE hrN) (Fin.castLE hrN))⁻¹‖ :=
    norm_pos_iff.2 ((isUnit_nonsing_inv_iff.2 hV).ne_zero)
  refine ⟨(div_le_iff₀ hinv).2 (by rwa [mul_comm]), ?_⟩
  have := sortedSingularValues_submatrix_le A Function.injective_id
    ((Fin.castLEEmb hrN).trans π.toEmbedding).injective (r - 1)
  exact this

/-- The leading `r` columns of an orthogonal `V` have orthonormal columns, so
`V(:, 1:r)ᵀ` has rank `r`. -/
private theorem rank_transpose_leadingCols {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {r : ℕ} (hr : r ≤ n) :
    ((V.submatrix id (Fin.castLE hr))ᵀ).rank = r := by
  set W := (V.submatrix id (Fin.castLE hr))ᵀ with hW
  have hVV : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' _ _).1 hV
  have hWW : W * Wᵀ = 1 := by
    ext i j
    have := congrFun (congrFun hVV (Fin.castLE hr i)) (Fin.castLE hr j)
    simpa [hW, mul_apply, one_apply, Fin.castLE_inj] using this
  refine le_antisymm (rank_le_height W) ?_
  have := rank_mul_le_left W Wᵀ
  rwa [hWW, rank_one, Fintype.card_fin] at this

/-- **§5.5.7, QR with column pivoting of `V(:, 1:r̃)ᵀ`**: for `V` orthogonal and `r̃ ≤ n`, let
`Qᵀ [V₁₁ᵀ V₂₁ᵀ] P = [R₁₁ R₁₂]` be a QR factorization with column pivoting of the `r̃ × n` matrix
`W = V(:, 1:r̃)ᵀ` (`W P = Q R`, rows of `R` from the `r`-th on zero and its leading `r × r` block
nonsingular, as (5.4.6) provides). Then `r = r̃` (the rows of `W` are orthonormal),
`[Ṽ₁₁; Ṽ₂₁] = Pᵀ [V₁₁; V₂₁] = [R₁₁ᵀQᵀ; R₁₂ᵀQᵀ]`, "`R₁₁` is nonsingular", and
`‖Ṽ₁₁⁻¹‖₂ = ‖R₁₁⁻¹‖₂`. -/
theorem qrcp_V11 {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ orthogonalGroup (Fin n) ℝ) {r' r : ℕ}
    (hr : r ≤ n) {Q : Matrix (Fin r) (Fin r) ℝ} {R : Matrix (Fin r) (Fin n) ℝ}
    {π : Equiv.Perm (Fin n)}
    (h : IsPivotedQR.IsRankRevealing (V.submatrix id (Fin.castLE hr))ᵀ Q R π r') :
    r' = r ∧ (V.submatrix π id).submatrix id (Fin.castLE hr) = Rᵀ * Qᵀ ∧
      IsUnit (R.submatrix id (Fin.castLE hr)) ∧
      ‖((V.submatrix π id).submatrix (Fin.castLE hr) (Fin.castLE hr))⁻¹‖ =
        ‖(R.submatrix id (Fin.castLE hr))⁻¹‖ := by
  set W := (V.submatrix id (Fin.castLE hr))ᵀ with hW
  -- the rows of `W` are orthonormal, so `rank W = r`
  have hrank : W.rank = r := rank_transpose_leadingCols hV hr
  have hr' : r' = r := h.rank_eq.symm.trans hrank
  subst hr'
  have hQO : Q ∈ orthogonalGroup (Fin r') ℝ := h.isQR.mem_unitaryGroup
  have hT : (V.submatrix π id).submatrix id (Fin.castLE hr) = Rᵀ * Qᵀ := by
    rw [← transpose_mul, h.isQR.mul_eq]
    ext i j
    rfl
  have hB : R.submatrix id (Fin.castLE hr) =
      R.submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols) := by
    ext i j
    rfl
  have hu : IsUnit (R.submatrix id (Fin.castLE hr)) := hB ▸ h.isUnit_block
  refine ⟨rfl, hT, hu, ?_⟩
  set B := R.submatrix id (Fin.castLE hr) with hBdef
  have hV11 : (V.submatrix π id).submatrix (Fin.castLE hr) (Fin.castLE hr) = Bᵀ * Qᵀ := by
    ext i j
    have h2 := congrFun (congrFun hT (Fin.castLE hr i)) j
    simp only [submatrix_apply, id] at h2 ⊢
    rw [h2]
    simp [mul_apply, hBdef]
  have hQinv : (Qᵀ)⁻¹ = Q := inv_eq_left_inv ((mem_orthogonalGroup_iff _ _).1 hQO)
  rw [hV11, Matrix.mul_inv_rev, hQinv, ← transpose_nonsing_inv, l2_opNorm_unitary_mul hQO,
    ← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]

/-! ### §5.5.8 Column independence versus residual size -/

/-- **Theorem 5.5.3**: "Assume that `UᵀAV = Σ` is the SVD of `A ∈ ℝ^{m×n}` and that `r_y` and
`r_{x_r̃}` are defined as above. If `Ṽ₁₁` is the leading `r̃`-by-`r̃` principal submatrix of `PᵀV`,
then `‖r_{x_r̃} - r_y‖₂ ≤ (σ_{r̃+1}(A)/σ_r̃(A)) ‖Ṽ₁₁⁻¹‖₂ ‖b‖₂`" (printed "`r`-by-`r`"), where
`r_{x_r̃} = b - A x_r̃ = (I - U₁U₁ᵀ) b` (`x_r̃` solving the nearest rank-`r̃` problem, `U₁` the
first `r̃` columns of `U`) and `r_y = b - B₁ z = (I - B₁B₁⁺) b` (`B₁` the first `r̃` columns of
`AP = A.submatrix id π`); 0-based, `σ_{r̃+1}(A)/σ_r̃(A)` is
`A.sortedSingularValues r̃ / A.sortedSingularValues (r̃ - 1)`. With it, the remark after the proof:
`r_{x_r̃} - r_y = B₁ z - ∑_{i=1}^{r̃} (u_iᵀ b) u_i` (`z = B₁⁺ b`). As in Theorem 5.5.2,
`1 ≤ r̃ ≤ rank A` and `Ṽ₁₁` nonsingular; the book leaves `r̃ ≤ rank A` implicit, and it is needed
(for `A = 0` the left side need not vanish). Backbone `Matrix.norm_residual_subset_sub_le`. -/
theorem theorem_5_5_3 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (π : Equiv.Perm (Fin n)) {r : ℕ}
    (hr0 : 0 < r) (hrA : r ≤ A.rank)
    (hV : IsUnit ((V.submatrix π id).submatrix (Fin.castLE (hrA.trans A.rank_le_width))
      (Fin.castLE (hrA.trans A.rank_le_width))))
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖(b - toEuclideanLin (U.submatrix id (Fin.castLE (hrA.trans A.rank_le_height)) *
          (U.submatrix id (Fin.castLE (hrA.trans A.rank_le_height)))ᵀ) b) -
        (b - toEuclideanLin ((A.submatrix id π).submatrix id
            (Fin.castLE (hrA.trans A.rank_le_width)) *
          ((A.submatrix id π).submatrix id (Fin.castLE (hrA.trans A.rank_le_width))).pinv) b)‖ ≤
      A.sortedSingularValues r / A.sortedSingularValues (r - 1) *
        ‖((V.submatrix π id).submatrix (Fin.castLE (hrA.trans A.rank_le_width))
          (Fin.castLE (hrA.trans A.rank_le_width)))⁻¹‖ * ‖b‖ ∧
    (b - toEuclideanLin (U.submatrix id (Fin.castLE (hrA.trans A.rank_le_height)) *
          (U.submatrix id (Fin.castLE (hrA.trans A.rank_le_height)))ᵀ) b) -
        (b - toEuclideanLin ((A.submatrix id π).submatrix id
            (Fin.castLE (hrA.trans A.rank_le_width)) *
          ((A.submatrix id π).submatrix id (Fin.castLE (hrA.trans A.rank_le_width))).pinv) b) =
      toEuclideanLin ((A.submatrix id π).submatrix id (Fin.castLE (hrA.trans A.rank_le_width)))
          (toEuclideanLin ((A.submatrix id π).submatrix id
            (Fin.castLE (hrA.trans A.rank_le_width))).pinv b) -
        toLp 2 (∑ i : Fin r, (U.col (Fin.castLE (hrA.trans A.rank_le_height) i) ⬝ᵥ ofLp b) •
          U.col (Fin.castLE (hrA.trans A.rank_le_height) i)) := by
  have hle := norm_residual_subset_sub_le h π hr0 (hrA.trans A.rank_le_height)
    (hrA.trans A.rank_le_width) hrA hV b
  simp only [conjTranspose_eq_transpose_of_trivial] at hle
  refine ⟨hle, ?_⟩
  rw [sub_sub_sub_cancel_left, toEuclideanLin_mul_apply]
  congr 1
  ext p
  simp only [toEuclideanLin_apply, PiLp.toLp_apply, mulVec, dotProduct, mul_apply,
    submatrix_apply, id_eq, transpose_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    col_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end SubsetSelection

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 5.5.1** (SVD-based subset selection): "Given `A ∈ ℝ^{m×n}` and `b ∈ ℝ^m` the
following algorithm computes a permutation `P`, a rank estimate `r̃`, and a vector `z ∈ ℝ^r̃` such
that the first `r̃` columns of `B = AP` are independent and `‖B(:, 1:r̃) z - b‖₂` is minimized":
```
Compute the SVD UᵀAV = diag(σ₁, …, σ_n) and save V.
Determine r̃ ≤ rank(A).
Apply QR with column pivoting: QᵀV(:, 1:r̃)ᵀP = [R₁₁ | R₁₂] and set AP = [B₁ | B₂].
Determine z ∈ ℝ^r̃ such that ‖b - B₁z‖₂ = min.
```
The SVD (a Chapter 8 algorithm) and the rank decision are inputs: `V` and `r̃` are arguments
(convention 5). QR with column pivoting is Algorithm 5.4.1 on `V(:, 1:r̃)ᵀ` padded with zero rows
(`Matrix.padRows`), and the least-squares step is the Householder LS solution of §5.3.3 on `B₁`
with the returned `β` (`householderLS`; the as-printed Algorithm 5.3.2 recomputes `β` and fails,
e.g. for `B₁ = I₂`, `algorithm_5_3_2_counterexample`). Returns `(P, z)`. -/
noncomputable def algorithm_5_5_1 {r : ℕ} (hrn : r ≤ n) (hrm : r ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) :
    M (Equiv.Perm (Fin n) × (Fin r → ℝ)) := do
  let st ← algorithm_5_4_1 rnd le_rfl (Matrix.padRows (V.submatrix id (Fin.castLE hrn))ᵀ hrn)
  let z ← householderLS rnd hrm ((A.submatrix id (pivotPerm st.piv)).submatrix id
    (Fin.castLE hrn)) b
  pure (pivotPerm st.piv, z)

end Programs

section Spec

open scoped Matrix.Norms.L2Operator

/-- **Algorithm 5.5.1 selects independent columns and solves the subset problem** (exact
arithmetic): if `V` is the right-singular-vector matrix of an SVD `UᵀAV = Σ` and
`1 ≤ r̃ ≤ rank A`, then for the output `(P, z)`, with `B₁` the first `r̃` columns of `AP` and `Ṽ₁₁`
the leading `r̃ × r̃` block of `PᵀV`: `Ṽ₁₁` is nonsingular (QR with column pivoting of
`V(:, 1:r̃)ᵀ` has rank `r̃`, the rows being orthonormal, so its pivots pick an invertible
`Ṽ₁₁ᵀ`), `σ_r̃(B₁) ≥ σ_r̃(A)/‖Ṽ₁₁⁻¹‖₂ > 0` (Theorem 5.5.2), hence "the first `r̃` columns of
`B = AP` are independent"; and "`‖B(:, 1:r̃) z - b‖₂` is minimized" (`householderLS_spec`).
Algorithm 5.4.1 runs on `V(:, 1:r̃)ᵀ` padded with zero rows (`Matrix.padRows`); the padding changes
neither the rank nor the rows of `R` that matter. -/
theorem algorithm_5_5_1_spec {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {r : ℕ} (hrn : r ≤ n)
    (hrm : r ≤ m) (hr0 : 0 < r) (hrA : r ≤ A.rank) (b : Fin m → ℝ)
    {P : Equiv.Perm (Fin n)} {z : Fin r → ℝ}
    (hout : Id.run (algorithm_5_5_1 pure hrn hrm A V b) = (P, z)) :
    IsUnit ((V.submatrix P id).submatrix (Fin.castLE hrn) (Fin.castLE hrn)) ∧
      A.sortedSingularValues (r - 1) /
          ‖((V.submatrix P id).submatrix (Fin.castLE hrn) (Fin.castLE hrn))⁻¹‖ ≤
        ((A.submatrix id P).submatrix id (Fin.castLE hrn)).sortedSingularValues (r - 1) ∧
      LinearIndependent ℝ ((A.submatrix id P).submatrix id (Fin.castLE hrn))ᵀ ∧
      IsLeastSquaresSolution ((A.submatrix id P).submatrix id (Fin.castLE hrn)) (toLp 2 b)
        (toLp 2 z) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  set W : Matrix (Fin r) (Fin n) ℝ := (V.submatrix id (Fin.castLE hrn))ᵀ with hW
  obtain ⟨hRR, hrank, -⟩ := algorithm_5_4_1_spec le_rfl (Matrix.padRows W hrn)
  have hP : P = pivotPerm (Id.run (algorithm_5_4_1 pure le_rfl (Matrix.padRows W hrn))).piv :=
    (congrArg Prod.fst hout).symm
  have hz : z = Id.run (householderLS pure hrm ((A.submatrix id
      (pivotPerm (Id.run (algorithm_5_4_1 pure le_rfl (Matrix.padRows W hrn))).piv)).submatrix id
        (Fin.castLE hrn)) b) :=
    (congrArg Prod.snd hout).symm
  subst hP hz
  set st := Id.run (algorithm_5_4_1 pure le_rfl (Matrix.padRows W hrn)) with hst
  -- the rows of `W` are orthonormal, so `rank W = r̃`, and the run has `r = r̃`
  have hrankW : W.rank = r := rank_transpose_leadingCols h.mem_unitaryGroup_right hrn
  have hr : st.r = r := by
    rw [hrank, Matrix.padRows_eq_mul W hrn, rank_submatrix_one_mul (Fin.castLE_injective hrn),
      hrankW]
  have hRR' := hRR
  rw [hr] at hRR'
  -- `[Ṽ₁₁ᵀ; 0] = Q [R₁₁; 0]`, of rank `r̃`
  set Vt := (V.submatrix (pivotPerm st.piv) id).submatrix (Fin.castLE hrn) (Fin.castLE hrn)
    with hVt
  have hkey : (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id (Fin.castLE hrn) * Vtᵀ =
      factoredQ st.β st.A * (upperPart st.A).submatrix id (Fin.castLE hrn) := by
    have h1 : ((Matrix.padRows W hrn).submatrix id (pivotPerm st.piv)).submatrix id
        (Fin.castLE hrn) =
        (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id (Fin.castLE hrn) * Vtᵀ := by
      rw [Matrix.padRows_eq_mul W hrn]
      rfl
    rw [← h1, ← hRR'.isQR.mul_eq]
    rfl
  have hrankT : ((upperPart st.A).submatrix id (Fin.castLE hrn)).rank = r :=
    HasRevealingBlock.rank_eq ⟨hRR'.le_rows, le_rfl,
      fun i j hi => hRR'.apply_eq_zero i _ hi, hRR'.isUnit_block⟩
  have hQdet : IsUnit (factoredQ st.β st.A).det :=
    (isUnit_iff_isUnit_det _).1 (isUnit_of_mem_unitaryGroup hRR'.isQR.mem_unitaryGroup)
  have hVtu : IsUnit Vt := by
    have hrk : Vtᵀ.rank = r := by
      rw [← rank_submatrix_one_mul (Fin.castLE_injective hrn), hkey,
        rank_mul_eq_right_of_isUnit_det _ _ hQdet, hrankT]
    exact (isUnit_transpose _).1 (isUnit_of_rank_eq_card (by rw [hrk, Fintype.card_fin]))
  -- Theorem 5.5.2
  have hbound := (theorem_5_5_2 h (pivotPerm st.piv) hr0 hrA hVtu).1
  have hsA0 : 0 < A.sortedSingularValues (r - 1) :=
    lt_of_le_of_ne (A.sortedSingularValues_nonneg _)
      (Ne.symm ((A.sortedSingularValues_eq_zero_iff_rank_le _).not.2 (by omega)))
  have hinv : 0 < ‖Vt⁻¹‖ := norm_pos_iff.2 (isUnit_nonsing_inv_iff.2 hVtu).ne_zero
  have hB0 := lt_of_lt_of_le (div_pos hsA0 hinv) hbound
  have hlin : LinearIndependent ℝ
      ((A.submatrix id (pivotPerm st.piv)).submatrix id (Fin.castLE hrn))ᵀ := by
    refine linearIndependent_transpose_of_iInf_colSingularValues_pos ?_
    rw [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin]
    exact hB0
  exact ⟨hVtu, hbound, hlin, householderLS_spec hrm hlin b⟩

end Spec


end GolubVanLoan.Chapter05
