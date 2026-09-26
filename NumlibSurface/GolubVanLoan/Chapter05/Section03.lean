import Mathlib.LinearAlgebra.CrossProduct
import Numlib.Conditioning.LeastSquares
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter04.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section02

/-!
# Golub–Van Loan §5.3: the full-rank least-squares problem

Surface file for [golub2013matrix] §5.3: the normal equations and the gradient (§5.3.1), the
method of normal equations (Algorithm 5.3.1) and its accuracy (5.3.4), the SVD expansion
(5.3.2)–(5.3.3), the QR solution (5.3.5) and the Householder LS solution (Algorithm 5.3.2), the
sensitivity of the LS problem (Theorem 5.3.1 with (5.3.9), (5.3.15), (5.3.16)), the augmented
system, its QR solution and iterative improvement (§5.3.8, (5.3.20)), and the cross-product
nearness problems of §5.3.9 ((5.3.21)–(5.3.29)).

## Conventions

Least-squares statements are on `EuclideanSpace ℝ (Fin m)` (the backbone's
`Matrix.IsLeastSquaresSolution A b x`: `x` minimizes `‖A x - b‖₂`), vectors of algorithms are
`Fin m → ℝ` and are converted with `WithLp.toLp 2`. Matrix norms are the operator 2-norms
(`Matrix.Norms.L2Operator`), `κ₂(A)` is `kappa2 A` ((5.2.4)) and `σ_n(A)` is the least singular
value `⨅ i, A.singularValues i`. Theorem 5.3.1 and (5.3.4) are proved in rigorous form (no
`O(ε²)`), the printed first-order form following from them. Programs follow the conventions of
`NumlibSurface/GolubVanLoan`: Algorithm 5.3.1 calls Algorithms 1.1.1, 4.2.1, 3.1.1 and 3.1.2,
Algorithm 5.3.2 calls Algorithms 5.2.1 and 3.1.2. The book's `u_i`, `v_i` are the columns of
the SVD factors (`Matrix.IsSVD A U σ V`), `u_iᵀ b` is `U.col i ⬝ᵥ b`. Indices are 0-based. The
cross-product matrix of `v ∈ ℝ³` is `crossMatrix v` (Mathlib has the cross product `⨯₃` but no
matrix form).

## Book slips carried

(5.3.3)'s upper summation limit is printed `2` (read `m`); Algorithm 5.3.2 recomputes
`β = 2/vᵀv`, which is wrong when `house` returned `β = 0` (`algorithm_5_3_2_counterexample`);
(5.3.26)–(5.3.29) need non-parallel lines (`r ≠ 0`) and non-collinear points (`v ≠ 0`), which the
book omits.

## Not formalized

The `p`-norm example of the introduction, the numerical examples of §5.3.1 and §5.3.2
(`fl(AᵀA)` singular), the heuristic readings (5.3.18)–(5.3.19), the comparison of §5.3.7 (prose),
Björck's digit-gain claim (§5.3.8), the first-order expansion (5.3.17) inside the proof of
Theorem 5.3.1, the Problems.
-/

open FloatingPoint Matrix WithLp

namespace GolubVanLoan.Chapter05

variable {m n : ℕ}

/-! ### §5.3.1 Implications of full rank -/

section FullRank

/-- **§5.3.1, the normal equations**: `x` minimizes `‖Ax - b‖₂` iff `Aᵀ(Ax - b) = 0`, i.e.
`AᵀA x = Aᵀb`; if `x` and `x + z` are both minimizers then `Az = 0`; and for full column rank the
minimizer `x_LS` is unique and `AᵀA` is positive definite. -/
theorem isLeastSquaresSolution_iff_normalEquations {A : Matrix (Fin m) (Fin n) ℝ}
    (b : EuclideanSpace ℝ (Fin m)) :
    (∀ x, IsLeastSquaresSolution A b x ↔ toEuclideanLin (Aᵀ * A) x = toEuclideanLin Aᵀ b) ∧
      (∀ x y, IsLeastSquaresSolution A b x → IsLeastSquaresSolution A b y →
        toEuclideanLin A (y - x) = 0) ∧
      (LinearIndependent ℝ Aᵀ → (∃! x, IsLeastSquaresSolution A b x) ∧ (Aᵀ * A).PosDef) := by
  refine ⟨fun x => ?_, fun x y hx hy => hx.toEuclideanLin_sub_eq_zero hy, fun hA => ?_⟩
  · rw [Matrix.isLeastSquaresSolution_iff_normalEquations, conjTranspose_eq_transpose_of_trivial]
  · refine ⟨existsUnique_isLeastSquaresSolution hA b, ?_⟩
    have := posDef_conjTranspose_mul_self_of_linearIndependent hA
    rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **§5.3.1, the gradient**: `φ(x) = ½ ‖Ax - b‖₂²` has `∇φ(x) = Aᵀ(Ax - b)`, "so solving the
normal equations is tantamount to solving the gradient equation `∇φ = 0`". -/
theorem gradient_leastSquaresObjective (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (fun y => ‖toEuclideanLin A y - b‖ ^ 2 / 2)
      (toEuclideanLin Aᵀ (toEuclideanLin A x - b)) x :=
  hasGradientAt_leastSquaresObjective A b x

end FullRank

/-! ### §5.3.2 The method of normal equations -/

section NormalEquations

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The first step of Algorithm 5.3.1, "compute the lower triangular portion of `C = AᵀA`": row by
row, each `c_ij = A(:, i)ᵀ A(:, j)` for `j ≤ i` by Algorithm 1.1.1; the strict upper triangle is
left `0`. -/
noncomputable def gramLower (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
    let r ← ((List.finRange n).filter (· ≤ i)).foldlM (fun (r : Fin n → ℝ) j => do
      let c ← Chapter01.algorithm_1_1_1 rnd (fun k => A k i) (fun k => A k j)
      pure (Function.update r j c)) 0
    pure (L.updateRow i r)) 0

/-- The second step of Algorithm 5.3.1, "form the matrix-vector product `d = Aᵀb`": each
`d_i = A(:, i)ᵀ b` by Algorithm 1.1.1. -/
noncomputable def transposeMulVec (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (d : Fin n → ℝ) i => do
    let c ← Chapter01.algorithm_1_1_1 rnd (fun k => A k i) b
    pure (Function.update d i c)) 0

/-- **Algorithm 5.3.1 (Normal Equations)**: "Given `A ∈ ℝ^{m×n}` with the property that
`rank(A) = n` and `b ∈ ℝ^m`, this algorithm computes a vector `x_LS` that minimizes `‖Ax - b‖₂`":
```
Compute the lower triangular portion of C = AᵀA.
Form the matrix-vector product d = Aᵀb.
Compute the Cholesky factorization C = GGᵀ.
Solve Gy = d and Gᵀx_LS = y.
```
The lower triangle is `gramLower` and `d` is `transposeMulVec`; the upper triangle of `C` is filled
by symmetry (an assignment). The Cholesky factorization is Algorithm 4.2.1, whose output holds `G`
in its lower triangle (read off, an assignment), and the triangular solves are Algorithms 3.1.1 and
3.1.2. -/
noncomputable def algorithm_5_3_1 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    M (Fin n → ℝ) := do
  let L ← gramLower rnd A
  let C : Matrix (Fin n) (Fin n) ℝ := of fun i j => if j ≤ i then L i j else L j i
  let d ← transposeMulVec rnd A b
  let F ← Chapter04.algorithm_4_2_1 rnd C
  let G : Matrix (Fin n) (Fin n) ℝ := of fun i j => if j ≤ i then F i j else 0
  let y ← Chapter03.algorithm_3_1_1 rnd G d
  Chapter03.algorithm_3_1_2 rnd Gᵀ y

end Programs

/-- A loop writing each listed row of a matrix from a value independent of the state. -/
private theorem foldl_updateRow_eq {k l : ℕ} (g : Fin k → Fin l → ℝ) (L : List (Fin k))
    (L₀ : Matrix (Fin k) (Fin l) ℝ) :
    L.foldl (fun (N : Matrix (Fin k) (Fin l) ℝ) i => N.updateRow i (g i)) L₀ =
      of fun i => if i ∈ L then g i else L₀ i :=
  foldl_update_eq g L L₀

/-- In exact arithmetic `gramLower` computes the lower triangle of `AᵀA`. -/
theorem gramLower_pure (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (gramLower pure A) = of fun i j => if j ≤ i then (Aᵀ * A) i j else 0 := by
  simp only [gramLower, List.idRun_foldlM, Id.run_bind, Chapter01.algorithm_1_1_1_spec,
    Id.run_pure]
  rw [foldl_updateRow_eq]
  ext i j
  simp only [of_apply, List.mem_finRange, ↓reduceIte, foldl_update_eq, List.mem_filter,
    decide_eq_true_eq, true_and]
  split_ifs
  · simp [mul_apply, dotProduct]
  · rfl

/-- In exact arithmetic `transposeMulVec` computes `Aᵀb`. -/
theorem transposeMulVec_pure (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Id.run (transposeMulVec pure A b) = Aᵀ *ᵥ b := by
  simp only [transposeMulVec, List.idRun_foldlM, Id.run_bind, Chapter01.algorithm_1_1_1_spec,
    Id.run_pure]
  rw [foldl_update_eq]
  ext i
  simp [mulVec, dotProduct]

/-- **Algorithm 5.3.1 solves the least-squares problem** (exact arithmetic): for `A` of full
column rank, the output minimizes `‖Ax - b‖₂`. `AᵀA` is positive definite, Algorithm 4.2.1 returns
its Cholesky factor `G` (`AᵀA = GGᵀ`), and the two triangular solves give `GGᵀx = Aᵀb`, the normal
equations. -/
theorem algorithm_5_3_1_spec {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (b : Fin m → ℝ) :
    IsLeastSquaresSolution A (toLp 2 b) (toLp 2 (Id.run (algorithm_5_3_1 pure A b))) := by
  have hPD : (Aᵀ * A).PosDef := ((isLeastSquaresSolution_iff_normalEquations (toLp 2 b)).2.2 hA).2
  have hC : (of fun i j => if j ≤ i then Id.run (gramLower pure A) i j
      else Id.run (gramLower pure A) j i : Matrix (Fin n) (Fin n) ℝ) = Aᵀ * A := by
    rw [gramLower_pure]
    ext i j
    simp only [of_apply]
    split_ifs with h1 h2
    · rfl
    · rw [← transpose_apply (Aᵀ * A), transpose_mul, transpose_transpose]
    · exact absurd (le_of_lt (not_le.1 h1)) h2
  set F := Id.run (Chapter04.algorithm_4_2_1 pure (Aᵀ * A)) with hF
  set G : Matrix (Fin n) (Fin n) ℝ := of fun i j => if j ≤ i then F i j else 0 with hG
  have hGc : G = cholesky (Aᵀ * A) := by
    rw [← (Chapter04.algorithm_4_2_1_spec hPD).1, hG, ← hF]
    ext i j
    simp only [of_apply, Matrix.sub_apply, strictUpper_apply]
    rcases le_or_gt j i with h | h
    · simp [h, not_lt.2 h]
    · simp [h, not_le.2 h]
  have hGl : G.IsLowerTriangular := hGc ▸ isLowerTriangular_cholesky _
  have hGd : ∀ i, G i i ≠ 0 := fun i => hGc ▸ (Chapter04.cholesky_diag_pos hPD i).ne'
  have hGG : G * Gᵀ = Aᵀ * A := by rw [hGc]; exact Chapter04.cholesky_mul_transpose hPD
  have hrun : Id.run (algorithm_5_3_1 pure A b) = Id.run (Chapter03.algorithm_3_1_2 pure Gᵀ
      (Id.run (Chapter03.algorithm_3_1_1 pure G (Aᵀ *ᵥ b)))) := by
    simp only [algorithm_5_3_1, Id.run_bind, transposeMulVec_pure]
    rw [hC]
  rw [hrun]
  set y := Id.run (Chapter03.algorithm_3_1_1 pure G (Aᵀ *ᵥ b)) with hy
  set x := Id.run (Chapter03.algorithm_3_1_2 pure Gᵀ y) with hx
  have h1 : G *ᵥ y = Aᵀ *ᵥ b := Chapter03.algorithm_3_1_1_spec hGl hGd _
  have h2 : Gᵀ *ᵥ x = y := Chapter03.algorithm_3_1_2_spec hGl.transpose_isUpperTriangular
    (fun i => by rw [transpose_apply]; exact hGd i) _
  rw [(isLeastSquaresSolution_iff_normalEquations (toLp 2 b)).1, toEuclideanLin_toLp,
    toEuclideanLin_toLp, ← hGG, ← mulVec_mulVec, h2, h1]

/-- A nonzero vector of `ℝⁿ` forces `n ≥ 1`. -/
private theorem neZero_of_ne_zero {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    NeZero n := by
  refine ⟨fun hn => hx ?_⟩
  subst hn
  ext i
  exact i.elim0

open scoped Matrix.Norms.L2Operator in
/-- **(5.3.4)**, rigorous in the form the book derives it: if the computed `x̂_LS` solves the
perturbed normal equations `(AᵀA + E) x̂_LS = Aᵀb` with `‖E‖₂ ≤ η ‖AᵀA‖₂` ("from what we know
about the roundoff properties of the Cholesky factorization", `η = c u`) and `η κ₂(A)² < 1`, then
`‖x̂_LS - x_LS‖₂/‖x_LS‖₂ ≤ η κ₂(A)²/(1 - η κ₂(A)²)`, since `κ₂(AᵀA) = κ₂(A)²` (the second clause).
The book's "`≈ u κ₂(A)²`" is the first-order reading. -/
theorem equation_5_3_4 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {b : EuclideanSpace ℝ (Fin m)} {E : Matrix (Fin n) (Fin n) ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin (Aᵀ * A + E) x = toEuclideanLin Aᵀ b) {η : ℝ}
    (hE : ‖E‖ ≤ η * ‖Aᵀ * A‖) (hη : η * kappa2 A ^ 2 < 1)
    (hx0 : toEuclideanLin A.pinv b ≠ 0) :
    ‖x - toEuclideanLin A.pinv b‖ / ‖toEuclideanLin A.pinv b‖ ≤
        η * kappa2 A ^ 2 / (1 - η * kappa2 A ^ 2) ∧
      kappa2 (Aᵀ * A) = kappa2 A ^ 2 := by
  have := neZero_of_ne_zero hx0
  refine ⟨norm_normalEquations_sub_le hA rfl
    (by rwa [conjTranspose_eq_transpose_of_trivial])
    (by rwa [conjTranspose_eq_transpose_of_trivial]) hη hx0, ?_⟩
  have h := pinvCondNumberLp_two_conjTranspose_mul_self hA
  rwa [conjTranspose_eq_transpose_of_trivial] at h

end NormalEquations

/-! ### The SVD expansion (5.3.2)–(5.3.3) -/

section SVD

variable {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
  {V : Matrix (Fin n) (Fin n) ℝ}

/-- The pseudoinverse from an SVD applied to `b`: `A⁺ b = ∑_i (u_iᵀ b / σ_i) v_i` (`n ≤ m`). -/
theorem pinv_mulVec_eq_sum_of_isSVD (h : IsSVD A U σ V) (hnm : n ≤ m) (b : Fin m → ℝ) :
    A.pinv *ᵥ b = ∑ i : Fin n, ((U.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) • V.col i := by
  rw [h.pinv_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [RCLike.ofReal_real_eq_id, id]
  have hD : ∀ i : Fin n, ((rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) *ᵥ
      (star U *ᵥ b)) i = (U.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i := by
    intro i
    simp only [mulVec, dotProduct, rectDiagonal, of_apply, ite_mul, zero_mul]
    rw [Finset.sum_eq_single (Fin.castLE hnm i) (fun j _ hj => by
      rw [ite_eq_right (fun e => hj (Fin.ext (by simp [e])))]) (by simp)]
    simp only [Fin.val_castLE, ↓reduceIte, star_apply, star_trivial, col_apply]
    rw [div_eq_inv_mul]
  ext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col_apply]
  change ∑ i, V p i * _ = _
  simp only [hD, mul_comm]

/-- **(5.3.2)**: if `Uᵀ A V = Σ` is an SVD of a full-column-rank `A ∈ ℝ^{m×n}` (`m ≥ n`), then
`x_LS = ∑_{i=1}^{n} (u_iᵀ b / σ_i) v_i` minimizes `‖Ax - b‖₂`. -/
theorem equation_5_3_2 (h : IsSVD A U σ V) (hA : LinearIndependent ℝ Aᵀ) (hnm : n ≤ m)
    (b : Fin m → ℝ) :
    IsLeastSquaresSolution A (toLp 2 b)
      (toLp 2 (∑ i : Fin n, ((U.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) • V.col i)) := by
  rw [isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent hA, toEuclideanLin_toLp,
    pinv_mulVec_eq_sum_of_isSVD h hnm]

/-- **(5.3.3)**: `ρ_LS² = ‖A x_LS - b‖₂² = ∑_{i=n+1}^{m} (u_iᵀ b)²` (the book prints the upper
limit as `2`). -/
theorem equation_5_3_3 (h : IsSVD A U σ V) (hA : LinearIndependent ℝ Aᵀ) (hnm : n ≤ m)
    (b : Fin m → ℝ) :
    ‖toEuclideanLin A (toLp 2 (∑ i : Fin n, ((U.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) • V.col i)) -
        toLp 2 b‖ ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), (U.col i ⬝ᵥ b) ^ 2 := by
  have hr : A.rank = n := by
    rw [← rank_transpose]
    simpa using LinearIndependent.rank_matrix (M := Aᵀ) hA
  rw [← pinv_mulVec_eq_sum_of_isSVD h hnm, ← toEuclideanLin_toLp,
    norm_sub_sq_pinv_eq_sum_of_isSVD h, hr]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_toLp_toLp, Real.norm_eq_abs, sq_abs]
  simp only [star_trivial, dotProduct_comm]
  rfl

end SVD

/-! ### §5.3.3 LS solution via QR factorization -/

section QR

/-- **(5.3.5) and §5.3.3**: if `Q` is orthogonal with `QᵀA = R = [R₁; 0]` (`n ≤ m`) and
`Qᵀb = [c; d]`, then `‖Ax - b‖₂² = ‖R₁x - c‖₂² + ‖d‖₂²` for every `x`; for full column rank,
`x_LS = R₁⁻¹ c` solves the LS problem and `ρ_LS² = ‖d‖₂²`. -/
theorem equation_5_3_5 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (hnm : n ≤ m) (b : EuclideanSpace ℝ (Fin m)) :
    (∀ x, ‖toEuclideanLin A x - b‖ ^ 2 =
      ‖toEuclideanLin (R.firstRows hnm) x - toEuclideanLin (Q.firstColumns hnm)ᵀ b‖ ^ 2 +
        ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)),
          ‖(toEuclideanLin Qᵀ b) i‖ ^ 2) ∧
      (LinearIndependent ℝ Aᵀ →
        IsLeastSquaresSolution A b
          (toEuclideanLin ((R.firstRows hnm)⁻¹ * (Q.firstColumns hnm)ᵀ) b) ∧
        ∀ x, IsLeastSquaresSolution A b x → ‖toEuclideanLin A x - b‖ ^ 2 =
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)),
            ‖(toEuclideanLin Qᵀ b) i‖ ^ 2) := by
  refine ⟨fun x => ?_, fun hA => ⟨?_, fun x hx => ?_⟩⟩
  · have := norm_sub_sq_eq_of_isQR h hnm b x
    simpa only [conjTranspose_eq_transpose_of_trivial] using this
  · have := h.isLeastSquaresSolution hnm hA b
    simpa only [conjTranspose_eq_transpose_of_trivial] using this
  · have := norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution h hnm hA hx
    simpa only [conjTranspose_eq_transpose_of_trivial] using this

/-! #### §5.3.5 LS solution via MGS -/

/-- The augmented matrix `A₊ = [A | b]` of §5.3.5. -/
def augmentCol (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Matrix (Fin m) (Fin (n + 1)) ℝ :=
  of fun i => Fin.snoc (α := fun _ => ℝ) (A i) (b i)

/-- **§5.3.5, least squares by MGS on the augmented matrix**: if MGS applied to `A₊ = [A | b]`
(full column rank `n + 1`) gives `A₊ = [Q₁ | q_{n+1}] [R₁ z; 0 ρ]`, then `z = Q₁ᵀ b`, the solutions
of `R₁ x = z` are exactly the least-squares solutions (`x_LS`), and `|ρ| = ρ_LS`. -/
theorem mgs_augmented {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (hA : LinearIndependent ℝ (augmentCol A b)ᵀ) :
    (fun j => (Id.run (algorithm_5_2_6 pure (augmentCol A b))).2 j.castSucc (Fin.last n)) =
        ((Id.run (algorithm_5_2_6 pure (augmentCol A b))).1.submatrix id Fin.castSucc)ᵀ *ᵥ b ∧
      (∀ x : Fin n → ℝ,
        IsLeastSquaresSolution A (toLp 2 b) (toLp 2 x) ↔
          (Id.run (algorithm_5_2_6 pure (augmentCol A b))).2.submatrix Fin.castSucc Fin.castSucc
            *ᵥ x = fun j => (Id.run (algorithm_5_2_6 pure (augmentCol A b))).2 j.castSucc
              (Fin.last n)) ∧
      ∀ x : Fin n → ℝ, IsLeastSquaresSolution A (toLp 2 b) (toLp 2 x) →
        |(Id.run (algorithm_5_2_6 pure (augmentCol A b))).2 (Fin.last n) (Fin.last n)| =
          ‖toEuclideanLin A (toLp 2 x) - toLp 2 b‖ := by
  obtain ⟨hQR, hpos⟩ := algorithm_5_2_6_spec _ hA
  set Q := (Id.run (algorithm_5_2_6 pure (augmentCol A b))).1 with hQdef
  set R := (Id.run (algorithm_5_2_6 pure (augmentCol A b))).2 with hRdef
  set Q₁ : Matrix (Fin m) (Fin n) ℝ := Q.submatrix id Fin.castSucc with hQ₁
  set R₁ : Matrix (Fin n) (Fin n) ℝ := R.submatrix Fin.castSucc Fin.castSucc with hR₁
  set z : Fin n → ℝ := fun j => R j.castSucc (Fin.last n) with hz
  set ρ := R (Fin.last n) (Fin.last n) with hρ
  set q := Q.col (Fin.last n) with hq
  have hon := isThinQR_col_dotProduct_col hQR
  have hup : ∀ j : Fin n, R (Fin.last n) j.castSucc = 0 := fun j =>
    hQR.isUpperTriangular (Fin.castSucc_lt_last j)
  -- the column split `A = Q₁ R₁`, `b = Q₁ z + ρ q`
  have hAe : A = Q₁ * R₁ := by
    ext p j
    have := congrFun (congrFun hQR.mul_eq p) j.castSucc
    rw [mul_apply, Fin.sum_univ_castSucc, hup, mul_zero, add_zero] at this
    have h2 : augmentCol A b p j.castSucc = A p j := by simp [augmentCol]
    exact (this.trans h2).symm
  have hbe : b = Q₁ *ᵥ z + ρ • q := by
    ext p
    have := congrFun (congrFun hQR.mul_eq p) (Fin.last n)
    rw [mul_apply, Fin.sum_univ_castSucc] at this
    simp only [augmentCol, of_apply, Fin.snoc_last] at this
    rw [← this]
    simp [mulVec, dotProduct, hQ₁, hz, hq, hρ, mul_comm]
  have hQ₁Q₁ : Q₁ᵀ * Q₁ = 1 := by
    ext i j
    have := hon i.castSucc j.castSucc
    simp only [Fin.castSucc_inj] at this
    simpa [mul_apply, one_apply, hQ₁, dotProduct] using this
  have hQ₁q : Q₁ᵀ *ᵥ q = 0 := by
    ext i
    have := hon i.castSucc (Fin.last n)
    rw [ite_eq_right (fun e => absurd e (Fin.castSucc_lt_last i).ne)] at this
    simpa [mulVec, hQ₁, hq, dotProduct] using this
  have hqq : q ⬝ᵥ q = 1 := by simpa using hon (Fin.last n) (Fin.last n)
  -- `R₁` is nonsingular
  have hR₁up : R₁.IsUpperTriangular := fun i j hij =>
    hQR.isUpperTriangular (Fin.castSucc_lt_castSucc_iff.2 hij)
  have hdet : R₁ᵀ.det ≠ 0 := by
    rw [det_transpose, det_of_isUpperTriangular hR₁up]
    exact (Finset.prod_pos fun i _ => hpos i.castSucc).ne'
  have hz' : z = Q₁ᵀ *ᵥ b := by
    rw [hbe, mulVec_add, mulVec_mulVec, hQ₁Q₁, one_mulVec, mulVec_smul, hQ₁q, smul_zero,
      add_zero]
  have hres : ∀ x, A *ᵥ x - b = Q₁ *ᵥ (R₁ *ᵥ x - z) - ρ • q := by
    intro x
    rw [hbe, hAe, ← mulVec_mulVec, mulVec_sub]
    abel
  have hnormal : ∀ x, Aᵀ *ᵥ (A *ᵥ x - b) = R₁ᵀ *ᵥ (R₁ *ᵥ x - z) := by
    intro x
    rw [hres, hAe, transpose_mul, ← mulVec_mulVec, mulVec_sub, mulVec_smul,
      mulVec_mulVec, hQ₁Q₁, one_mulVec, hQ₁q, smul_zero, sub_zero]
  have hLS : ∀ x : Fin n → ℝ,
      IsLeastSquaresSolution A (toLp 2 b) (toLp 2 x) ↔ R₁ *ᵥ x = z := by
    intro x
    rw [(isLeastSquaresSolution_iff_normalEquations (toLp 2 b)).1, toEuclideanLin_toLp,
      toEuclideanLin_toLp, (toLp_injective 2).eq_iff, ← mulVec_mulVec, ← sub_eq_zero,
      ← mulVec_sub, hnormal]
    constructor
    · intro h
      exact sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero hdet h)
    · intro h
      rw [h, sub_self, mulVec_zero]
  refine ⟨hz', hLS, fun x hx => ?_⟩
  rw [toEuclideanLin_toLp, ← toLp_sub, hres, (hLS x).1 hx, sub_self, mulVec_zero, zero_sub]
  have h1 := dotProduct_self_eq_norm_sq (-(ρ • q))
  rw [neg_dotProduct, dotProduct_neg, neg_neg, smul_dotProduct, dotProduct_smul, hqq,
    smul_eq_mul, smul_eq_mul, mul_one] at h1
  have h2 : ‖(toLp 2 (-(ρ • q)) : EuclideanSpace ℝ (Fin m))‖ = |ρ| := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← h1, ← sq, Real.sqrt_sq_eq_abs]
  exact h2.symm

end QR

/-! ### §5.3.3 Algorithm 5.3.2: the Householder LS solution -/

section HouseholderLS

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One pass of the `b`-loop of Algorithm 5.3.2, as printed:
```
v = [1; A(j+1:m, j)]
β = 2/vᵀv
b(j:m) = b(j:m) - β(vᵀb(j:m))v
```
`vᵀv` and `vᵀb(j:m)` are Algorithm 1.1.1 over the rows `j:m`; `β`, `β(vᵀb)`, the products with
`v` and the differences are rounded, in the printed association. -/
noncomputable def householderLSStep (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) :
    M (Fin m → ℝ) := do
  let v := storedHouseholderVec A j
  let vv ← dotAccum rnd (indexFrom m j) v v 0
  let β ← rnd (2 / vv)
  let s ← dotAccum rnd (indexFrom m j) v b 0
  let t ← rnd (β * s)
  (indexFrom m j).foldlM (fun (b : Fin m → ℝ) i => do
    let p ← rnd (t * v i)
    let c ← rnd (b i - p)
    pure (Function.update b i c)) b

/-- **Algorithm 5.3.2 (Householder LS Solution)**: "If `A ∈ ℝ^{m×n}` has full column rank and
`b ∈ ℝ^m`, then the following algorithm computes a vector `x_LS ∈ ℝⁿ` such that `‖Ax_LS - b‖₂` is
minimum":
```
Use Algorithm 5.2.1 to overwrite A with its QR factorization.
for j = 1:n
    v = [1; A(j+1:m, j)];  β = 2/vᵀv;  b(j:m) = b(j:m) - β(vᵀb(j:m))v
end
Solve R(1:n, 1:n) · x_LS = b(1:n).
```
As printed, the `β_j` returned by Algorithm 5.2.1 are discarded and recomputed from the stored
vectors (`householderLSStep`), and the triangular solve is Algorithm 3.1.2 on the leading `n × n`
block of the upper triangle. The program takes `n ≤ m`. -/
noncomputable def algorithm_5_3_2 (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : M (Fin n → ℝ) := do
  let QR ← algorithm_5_2_1 rnd A
  let b ← (List.finRange n).foldlM (householderLSStep rnd QR.1) b
  Chapter03.algorithm_3_1_2 rnd ((upperPart QR.1).firstRows hnm) fun i => b (Fin.castLE hnm i)

end Programs

/-- Updating each index of a duplicate-free list once, from its current value. -/
theorem foldl_update_self_eq {ι : Type*} [DecidableEq ι] (g : ι → ℝ → ℝ) (l : List ι)
    (hl : l.Nodup) (y₀ : ι → ℝ) :
    l.foldl (fun y k => Function.update y k (g k (y k))) y₀ =
      fun k => if k ∈ l then g k (y₀ k) else y₀ k := by
  induction l generalizing y₀ with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.1 hl).2]
    funext k
    have ha : a ∉ l := (List.nodup_cons.1 hl).1
    by_cases hk : k ∈ l
    · have hka : k ≠ a := fun e => ha (e ▸ hk)
      simp [hk, hka]
    · by_cases hka : k = a
      · subst hka
        simp [hk]
      · simp [hk, hka]

/-- A dot product over `indexFrom m j` with a vector vanishing off it is the full dot product. -/
private theorem sum_indexFrom_eq_dotProduct (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n)
    (w : Fin m → ℝ) :
    ((indexFrom m j).map fun i => storedHouseholderVec A j i * w i).sum =
      storedHouseholderVec A j ⬝ᵥ w :=
  (sum_eq_sum_map_of_nodup (nodup_indexFrom m j) fun i hi => by
    rw [storedHouseholderVec_eq_zero A j hi, zero_mul]).symm

/-- In exact arithmetic one pass of the `b`-loop applies the reflector with the recomputed `β`. -/
theorem householderLSStep_pure (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) :
    Id.run (householderLSStep pure A b j) =
      (1 - recomputedBeta A j • vecMulVec (storedHouseholderVec A j)
        (storedHouseholderVec A j)) *ᵥ b := by
  simp only [householderLSStep, dotAccum_pure, Id.run_pure, List.idRun_foldlM,
    pure_bind, zero_add, sum_indexFrom_eq_dotProduct]
  rw [foldl_update_self_eq (fun i c => c - 2 / (storedHouseholderVec A j ⬝ᵥ
    storedHouseholderVec A j) * (storedHouseholderVec A j ⬝ᵥ b) * storedHouseholderVec A j i)
    _ (nodup_indexFrom m j)]
  funext i
  rw [one_sub_smul_vecMulVec_mulVec_apply, recomputedBeta]
  split_ifs with hi
  · ring
  · rw [storedHouseholderVec_eq_zero A j hi]
    ring

/-- A loop premultiplying a vector by symmetric matrices applies the transpose of their product. -/
private theorem foldl_mulVec_eq_transpose_prod_mulVec {α : Type} (P : α → Matrix (Fin m) (Fin m) ℝ)
    (hP : ∀ a, (P a)ᵀ = P a) (l : List α) (b : Fin m → ℝ) :
    l.foldl (fun b a => P a *ᵥ b) b = ((l.map P).prod)ᵀ *ᵥ b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, transpose_mul, hP, mulVec_mulVec]

/-- **Algorithm 5.3.2 solves the least-squares problem** (exact arithmetic) for `A` of full column
rank **when no Householder step of Algorithm 5.2.1 was degenerate** (every returned `β_j ≠ 0`): the
recomputed `β_j = 2/vᵀv` are then the actual ones (`equation_5_1_4_beta`), the `b`-loop computes
`Qᵀb` ((5.1.4)), and the back substitution solves `R₁ x = c`, `Qᵀb = [c; d]` ((5.3.5)). Without the
hypothesis the statement is false (`algorithm_5_3_2_counterexample`). -/
theorem algorithm_5_3_2_spec (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (hβ : ∀ j, (Id.run (algorithm_5_2_1 pure A)).2 j ≠ 0)
    (b : Fin m → ℝ) :
    IsLeastSquaresSolution A (toLp 2 b) (toLp 2 (Id.run (algorithm_5_3_2 pure hnm A b))) := by
  obtain ⟨hQR, -⟩ := algorithm_5_2_1_spec hnm A
  have hQeq := (equation_5_1_4_beta hnm A).2 hβ
  set st := Id.run (algorithm_5_2_1 pure A) with hst
  set Q := factoredQ st.2 st.1 with hQ
  set R := upperPart st.1 with hR
  have hloop : (List.finRange n).foldl (fun b j => Id.run (householderLSStep pure st.1 b j)) b =
      Qᵀ *ᵥ b := by
    simp only [householderLSStep_pure]
    rw [foldl_mulVec_eq_transpose_prod_mulVec _ (fun j => transpose_one_sub_smul_vecMulVec _ _),
      ← factoredQ_eq_prod, ← hQeq]
  have hrun : Id.run (algorithm_5_3_2 pure hnm A b) =
      Id.run (Chapter03.algorithm_3_1_2 pure (R.firstRows hnm)
        fun i => (Qᵀ *ᵥ b) (Fin.castLE hnm i)) := by
    simp only [algorithm_5_3_2, Id.run_bind, List.idRun_foldlM]
    rw [← hst, hloop]
  rw [hrun]
  set x := Id.run (Chapter03.algorithm_3_1_2 pure (R.firstRows hnm)
    fun i => (Qᵀ *ᵥ b) (Fin.castLE hnm i)) with hx
  have hsol : R.firstRows hnm *ᵥ x = fun i => (Qᵀ *ᵥ b) (Fin.castLE hnm i) :=
    Chapter03.algorithm_3_1_2_spec (hQR.isUpperTriangular_firstRows hnm)
      (hQR.firstRows_diag_ne_zero_of_linearIndependent hnm hA) _
  intro y
  have e1 := (equation_5_3_5 hQR hnm (toLp 2 b)).1 (toLp 2 x)
  have e2 := (equation_5_3_5 hQR hnm (toLp 2 b)).1 y
  have h0 : toEuclideanLin (R.firstRows hnm) (toLp 2 x) -
      toEuclideanLin (Q.firstColumns hnm)ᵀ (toLp 2 b) = 0 := by
    rw [toEuclideanLin_toLp, toEuclideanLin_toLp, hsol, sub_eq_zero]
    rfl
  rw [h0, norm_zero] at e1
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [e1, e2]
  nlinarith [sq_nonneg ‖toEuclideanLin (R.firstRows hnm) y -
    toEuclideanLin (Q.firstColumns hnm)ᵀ (toLp 2 b)‖]

/-- A step of Algorithm 5.2.1 on a column that is already `[x_j; 0]` with `x_j ≥ 0` below row `j`
changes nothing but records `β_j = 0` (`house` meets `σ = 0` and `x(1) ≥ 0`). -/
private theorem householderQRStep_of_col_zero (B : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ)
    (j : Fin n) (hjm : (j : ℕ) < m) (hzero : ∀ i : Fin m, (j : ℕ) < i → B i j = 0)
    (hpos : 0 ≤ B ⟨j, hjm⟩ j) :
    Id.run (householderQRStep pure (B, β) j) = (B, Function.update β j 0) := by
  obtain ⟨p, t, hpt⟩ := List.exists_cons_of_ne_nil (indexFrom_ne_nil (m := m) hjm)
  have hp : p = ⟨j, hjm⟩ := by
    have := congrArg List.head? hpt
    rw [List.head?_eq_some_head (indexFrom_ne_nil hjm), head_indexFrom hjm, List.head?_cons]
      at this
    exact (Option.some.inj this).symm
  have hnd := nodup_indexFrom m j
  rw [hpt] at hnd
  have hmem : ∀ i, i ∈ indexFrom m j ↔ i = p ∨ i ∈ t := fun i => by
    rw [hpt, List.mem_cons]
  have htail : ∀ i ∈ t, (j : ℕ) < i := by
    intro i hi
    have h1 : j ≤ (i : ℕ) := mem_indexFrom.1 ((hmem i).2 (Or.inr hi))
    have h2 : i ≠ p := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hi)
    rw [hp] at h2
    exact lt_of_le_of_ne h1 (fun e => h2 (Fin.ext e.symm))
  have hσ : (t.map fun i => B i j * B i j).sum = 0 :=
    List.sum_eq_zero fun y hy => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
      rw [hzero i (htail i hi), mul_zero]
  set v : Fin m → ℝ := fun i => if i = p then 1 else if i ∈ t then B i j else 0 with hv
  have hhouse : Id.run (houseOn pure (indexFrom m j) fun i => B i j) = (v, 0) := by
    rw [hpt]
    subst hp
    simp only [houseOn, dotAccum_pure, pure_bind, hσ, add_zero, hpos, and_true, ↓reduceIte]
    rfl
  have hvout : ∀ i, i ∉ indexFrom m j → v i = 0 := fun i hi => by
    rw [hmem, not_or] at hi
    simp [hv, hi.1, hi.2]
  simp only [householderQRStep, Id.run_bind, Id.run_pure, hhouse]
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom n j) hvout 0 B]
  simp only [zero_smul, sub_zero, Matrix.one_mul, ite_self]
  congr 1
  ext i q
  by_cases hq : q = j
  · subst hq
    rw [updateCol_self]
    split_ifs with hi
    · have hne : i ≠ p := by
        rw [hp]
        exact fun e => by rw [e] at hi; exact lt_irrefl _ hi
      have hit : i ∈ t := ((hmem i).1 (mem_indexFrom.2 hi.le)).resolve_left hne
      simp [hv, hne, hit]
    · rfl
  · rw [updateCol_ne hq]
    rfl

/-- Algorithm 5.2.1 leaves the identity unchanged, with every `β_j = 0`. -/
private theorem algorithm_5_2_1_one {k : ℕ} :
    Id.run (algorithm_5_2_1 pure (1 : Matrix (Fin k) (Fin k) ℝ)) = (1, 0) := by
  rw [algorithm_5_2_1, List.idRun_foldlM]
  refine List.foldl_fixed' (fun j => ?_) _
  rw [householderQRStep_of_col_zero _ _ j j.isLt (fun i hi => ?_) (by simp [one_apply])]
  · simp
  · exact one_apply_ne fun e => by rw [e] at hi; exact lt_irrefl _ hi

/-- **Algorithm 5.3.2 as printed is wrong when `house` returns `β = 0`**: for `A = I₂` and
`b = [1; 0]`, every Householder step of Algorithm 5.2.1 meets `σ = 0`, `x₁ = 1 ≥ 0`, so `A` is left
unchanged with `β = 0`; the printed recomputation `β = 2/vᵀv = 2` then flips `b(1)`, and the
output is `[-1; 0]`, which is not the least-squares (here the exact) solution `[1; 0]`. -/
theorem algorithm_5_3_2_counterexample :
    (Id.run (algorithm_5_2_1 pure (1 : Matrix (Fin 2) (Fin 2) ℝ))).2 = 0 ∧
      Id.run (algorithm_5_3_2 pure le_rfl (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0]) = ![-1, 0] ∧
      ¬ IsLeastSquaresSolution (1 : Matrix (Fin 2) (Fin 2) ℝ) (toLp 2 ![1, 0])
        (toLp 2 ![-1, 0]) := by
  refine ⟨by rw [algorithm_5_2_1_one], ?_, fun h => ?_⟩
  · have hloop : (List.finRange 2).foldl (fun b j => Id.run (householderLSStep pure
        (1 : Matrix (Fin 2) (Fin 2) ℝ) b j)) ![1, 0] = ![-1, 0] := by
      simp only [householderLSStep_pure]
      rw [show List.finRange 2 = [0, 1] by decide]
      simp only [List.foldl_cons, List.foldl_nil]
      ext i
      fin_cases i <;>
        norm_num [mulVec, dotProduct, Fin.sum_univ_two, vecMulVec_apply, storedHouseholderVec,
          recomputedBeta, one_apply]
    have hR : (upperPart (1 : Matrix (Fin 2) (Fin 2) ℝ)).firstRows le_rfl = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperPart, firstRows, one_apply]
    simp only [algorithm_5_3_2, Id.run_bind, List.idRun_foldlM, algorithm_5_2_1_one]
    rw [hloop, hR]
    have hs := Chapter03.algorithm_3_1_2_spec (U := (1 : Matrix (Fin 2) (Fin 2) ℝ))
      blockTriangular_one (by simp) (fun i => (![-1, 0] : Fin 2 → ℝ) (Fin.castLE le_rfl i))
    rw [one_mulVec] at hs
    rw [hs]
    ext i
    fin_cases i <;> rfl
  · have h1 := h (toLp 2 ![1, 0])
    rw [toEuclideanLin_toLp, toEuclideanLin_toLp, one_mulVec, one_mulVec, sub_self,
      norm_zero] at h1
    have h2 : (toLp 2 ![-1, 0] : EuclideanSpace ℝ (Fin 2)) - toLp 2 ![1, 0] ≠ 0 := by
      intro e
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) e
      norm_num at this
    exact h2 (norm_le_zero_iff.1 h1)

end HouseholderLS

/-! ### §5.3.6 The sensitivity of the LS problem -/

section Sensitivity

/-- **Theorem 5.3.1's angle** `θ_LS ∈ [0, π/2]`, `sin θ_LS = ‖r_LS‖₂ / ‖b‖₂`, for the
least-squares solution `x_LS = A⁺ b` and its residual `r_LS = b - A x_LS`. -/
noncomputable def thetaLS (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.arcsin (‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ / ‖b‖)

/-- **(5.3.10)**: `ν_LS = ‖A x_LS‖₂ / (σ_n(A) ‖x_LS‖₂)`, with `σ_n(A) = min_i σ_i(A)`. -/
noncomputable def nuLS (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ /
    ((⨅ i, A.singularValues i) * ‖toEuclideanLin A.pinv b‖)

/-- **(5.3.16)**: for `b ≠ 0` and `A x_LS ≠ 0`, `cos θ_LS = ‖A x_LS‖₂ / ‖b‖₂` and
`tan θ_LS = ‖r_LS‖₂ / ‖A x_LS‖₂`, from `b = A x_LS + r_LS` with `A x_LS ⊥ r_LS`. -/
theorem equation_5_3_16 (A : Matrix (Fin m) (Fin n) ℝ) {b : EuclideanSpace ℝ (Fin m)}
    (hb : b ≠ 0) (hAx : toEuclideanLin A (toEuclideanLin A.pinv b) ≠ 0) :
    Real.cos (thetaLS A b) = ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ / ‖b‖ ∧
      Real.tan (thetaLS A b) = ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ /
        ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ := by
  set x := toEuclideanLin A.pinv b
  set y := toEuclideanLin A x with hy
  set r := b - y with hr
  have hN : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hY : 0 < ‖y‖ := norm_pos_iff.2 hAx
  have hpy : ‖b‖ ^ 2 = ‖r‖ ^ 2 + ‖y‖ ^ 2 := by
    have := norm_toEuclideanLin_sub_sq_eq_of_normalEquations (normalEquations_pinv A b) 0
    rwa [map_zero, zero_sub, norm_neg, zero_sub, map_neg, norm_neg, ← norm_neg (y - b),
      neg_sub] at this
  have h1 : 1 - (‖r‖ / ‖b‖) ^ 2 = (‖y‖ / ‖b‖) ^ 2 := by
    field_simp
    linarith
  have hs : √(1 - (‖r‖ / ‖b‖) ^ 2) = ‖y‖ / ‖b‖ := by
    rw [h1, Real.sqrt_sq (by positivity)]
  refine ⟨by rw [thetaLS, Real.cos_arcsin, hs], ?_⟩
  rw [thetaLS, Real.tan_arcsin, hs]
  field_simp
  rfl

end Sensitivity

/-! ### Theorem 5.3.1 and the facts (5.3.9) -/

section SensitivityBounds

open scoped Matrix.Norms.L2Operator

/-- A matrix with independent columns and at least one column is nonzero. -/
private theorem l2_opNorm_pos_of_linearIndependent [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) : 0 < ‖A‖ := by
  refine norm_pos_iff.2 fun h0 => ?_
  have := hA.ne_zero (0 : Fin n)
  rw [h0] at this
  exact this rfl

/-- Independent columns: `A x = 0` forces `x = 0`. -/
private theorem toEuclideanLin_ne_zero {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    toEuclideanLin A x ≠ 0 := by
  intro h
  apply hx
  have hinj : Function.Injective A.mulVec := mulVec_injective_iff.2 hA
  have h1 : A *ᵥ ofLp x = A *ᵥ 0 := by
    rw [mulVec_zero]
    have := congrArg ofLp h
    simpa [toEuclideanLin_apply] using this
  have := hinj h1
  ext i
  simpa using congrFun this i

/-- The column-indexed `κ₂(A) = ‖A‖₂ / σ_min(A)` for independent columns. -/
private theorem kappa2_eq_div [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) : kappa2 A = ‖A‖ / ⨅ i, A.singularValues i := by
  rw [kappa2, pinvCondNumberLp, lpOpNorm_two, lpOpNorm_two,
    l2_opNorm_pinv_eq_inv_iInf_singularValues hA, div_eq_mul_inv]

/-- Pythagoras for the least-squares split `b = A x_LS + r_LS`. -/
private theorem norm_sq_eq_residual_add (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖b‖ ^ 2 = ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ ^ 2 +
      ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ ^ 2 := by
  have := norm_toEuclideanLin_sub_sq_eq_of_normalEquations (normalEquations_pinv A b) 0
  rwa [map_zero, zero_sub, norm_neg, zero_sub, map_neg, norm_neg,
    ← norm_neg (toEuclideanLin A (toEuclideanLin A.pinv b) - b), neg_sub] at this

/-- `sin θ_LS = ‖r_LS‖₂ / ‖b‖₂`. -/
private theorem sin_thetaLS (A : Matrix (Fin m) (Fin n) ℝ) {b : EuclideanSpace ℝ (Fin m)}
    (hb : b ≠ 0) :
    Real.sin (thetaLS A b) = ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ / ‖b‖ := by
  have hN : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hle : ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ ≤ ‖b‖ := by
    refine le_of_sq_le_sq ?_ hN.le
    have := norm_sq_eq_residual_add A b
    nlinarith [sq_nonneg ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖]
  rw [thetaLS, Real.sin_arcsin (by
      exact le_trans (by norm_num) (div_nonneg (norm_nonneg _) hN.le))
    ((div_le_one hN).2 hle)]

/-- The absolute bounds of Theorem 5.3.1 in terms of the relative size `ε` of the perturbations:
`‖x̂ - x‖ ≤ ε ((‖b‖ + ‖A‖ ‖x‖)/σ' + ‖A‖ ‖r‖/σ'²)` and
`‖r̂ - r‖ ≤ ε (‖b‖ + ‖A‖ ‖x‖ + ‖A‖ ‖r‖/σ')`, `σ' = σ_min(A) - ‖δA‖₂`. -/
private theorem ls_perturbation_bounds {A δA : Matrix (Fin m) (Fin n) ℝ}
    {b δb r r' : EuclideanSpace ℝ (Fin m)} {x x' : EuclideanSpace ℝ (Fin n)}
    (hδA : ‖δA‖ < ⨅ i, A.singularValues i) (hx : x = toEuclideanLin A.pinv b)
    (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb)) (hr : r = b - toEuclideanLin A x)
    (hr' : r' = (b + δb) - toEuclideanLin (A + δA) x') {ε : ℝ}
    (hεA : ‖δA‖ ≤ ε * ‖A‖) (hεb : ‖δb‖ ≤ ε * ‖b‖) :
    ‖x' - x‖ ≤ ε * ((‖b‖ + ‖A‖ * ‖x‖) / ((⨅ i, A.singularValues i) - ‖δA‖) +
        ‖A‖ * ‖r‖ / ((⨅ i, A.singularValues i) - ‖δA‖) ^ 2) ∧
      ‖r' - r‖ ≤ ε * (‖b‖ + ‖A‖ * ‖x‖ + ‖A‖ * ‖r‖ / ((⨅ i, A.singularValues i) - ‖δA‖)) := by
  have h1 := (norm_leastSquares_sub_le hδA hx hx' hr).2
  have h2 := norm_leastSquares_residual_sub_le hδA hx hx' hr hr'
  have hd : 0 < (⨅ i, A.singularValues i) - ‖δA‖ := sub_pos.2 hδA
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · calc (‖δb‖ + ‖δA‖ * ‖x‖) / ((⨅ i, A.singularValues i) - ‖δA‖) +
          ‖δA‖ * ‖r‖ / ((⨅ i, A.singularValues i) - ‖δA‖) ^ 2
        ≤ (ε * ‖b‖ + ε * ‖A‖ * ‖x‖) / ((⨅ i, A.singularValues i) - ‖δA‖) +
          ε * ‖A‖ * ‖r‖ / ((⨅ i, A.singularValues i) - ‖δA‖) ^ 2 := by gcongr
      _ = _ := by ring
  · calc ‖δb‖ + ‖δA‖ * ‖x‖ + ‖δA‖ * ‖r‖ / ((⨅ i, A.singularValues i) - ‖δA‖)
        ≤ ε * ‖b‖ + ε * ‖A‖ * ‖x‖ + ε * ‖A‖ * ‖r‖ / ((⨅ i, A.singularValues i) - ‖δA‖) := by
          gcongr
      _ = _ := by ring

/-- The relative size `ε = max(‖δA‖₂/‖A‖₂, ‖δb‖₂/‖b‖₂)` of a perturbation bounds each part. -/
theorem le_max_div_mul {A δA : Matrix (Fin m) (Fin n) ℝ} {b δb : EuclideanSpace ℝ (Fin m)}
    (hA : 0 < ‖A‖) (hb : 0 < ‖b‖) :
    ‖δA‖ ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) * ‖A‖ ∧
      ‖δb‖ ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) * ‖b‖ ∧ 0 ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) :=
  ⟨(div_le_iff₀ hA).1 (le_max_left _ _), (div_le_iff₀ hb).1 (le_max_right _ _),
    le_max_of_le_left (div_nonneg (norm_nonneg _) hA.le)⟩

/-- **Theorem 5.3.1, (5.3.11), rigorous**: for `A` of rank `n`, `‖δA‖₂ < σ_n(A)`, `b ≠ 0`,
`x_LS ≠ 0`, `ε = max(‖δA‖₂/‖A‖₂, ‖δb‖₂/‖b‖₂)`, and with `σ' = σ_n(A) - ‖δA‖₂`,
`κ' = ‖A‖₂/σ'`, `ν' = ‖A x_LS‖₂/(σ' ‖x_LS‖₂)`:
`‖x̂_LS - x_LS‖₂/‖x_LS‖₂ ≤ ε (ν'/cos θ_LS + [1 + ν' tan θ_LS] κ')` — the bracket of (5.3.11) with
`σ_n(A)` replaced by `σ'`, and no `O(ε²)` term. (The book's hypothesis `r_LS ≠ 0` is not needed.)
-/
theorem theorem_5_3_1_a {A δA : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {b δb : EuclideanSpace ℝ (Fin m)} {x x' : EuclideanSpace ℝ (Fin n)}
    (hδA : ‖δA‖ < ⨅ i, A.singularValues i) (hb : b ≠ 0) (hx0 : x ≠ 0)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb)) :
    ‖x' - x‖ / ‖x‖ ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) *
      (‖toEuclideanLin A x‖ / (((⨅ i, A.singularValues i) - ‖δA‖) * ‖x‖) /
          Real.cos (thetaLS A b) +
        (1 + ‖toEuclideanLin A x‖ / (((⨅ i, A.singularValues i) - ‖δA‖) * ‖x‖) *
          Real.tan (thetaLS A b)) * (‖A‖ / ((⨅ i, A.singularValues i) - ‖δA‖))) := by
  have := neZero_of_ne_zero hx0
  have hAn := l2_opNorm_pos_of_linearIndependent hA
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hAx := toEuclideanLin_ne_zero hA hx0
  have hAxn : 0 < ‖toEuclideanLin A x‖ := norm_pos_iff.2 hAx
  obtain ⟨hεA, hεb, -⟩ := le_max_div_mul (δA := δA) (δb := δb) hAn hbn
  have hd : 0 < (⨅ i, A.singularValues i) - ‖δA‖ := sub_pos.2 hδA
  have h := (ls_perturbation_bounds hδA hx hx' rfl rfl hεA hεb).1
  obtain ⟨hcos, htan⟩ := equation_5_3_16 A hb (hx ▸ hAx)
  rw [← hx] at hcos htan
  rw [div_le_iff₀ hxn]
  refine h.trans (le_of_eq ?_)
  rw [hcos, htan]
  field_simp
  ring

/-- **Theorem 5.3.1, (5.3.12), rigorous**: under the hypotheses of `theorem_5_3_1_a` and
`r_LS ≠ 0`, with `r̂_LS = (b + δb) - (A + δA) x̂_LS`:
`‖r̂_LS - r_LS‖₂/‖r_LS‖₂ ≤ ε (1/sin θ_LS + [1/(ν_LS tan θ_LS)] κ₂(A) + κ')`, which is (5.3.12)
with `κ' = ‖A‖₂/(σ_n(A) - ‖δA‖₂)` in place of `κ₂(A)` in its last term and no `O(ε²)` term. -/
theorem theorem_5_3_1_b {A δA : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {b δb r r' : EuclideanSpace ℝ (Fin m)} {x x' : EuclideanSpace ℝ (Fin n)}
    (hδA : ‖δA‖ < ⨅ i, A.singularValues i) (hb : b ≠ 0) (hx0 : x ≠ 0) (hr0 : r ≠ 0)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) (hr' : r' = (b + δb) - toEuclideanLin (A + δA) x') :
    ‖r' - r‖ / ‖r‖ ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) *
      (1 / Real.sin (thetaLS A b) + 1 / (nuLS A b * Real.tan (thetaLS A b)) * kappa2 A +
        ‖A‖ / ((⨅ i, A.singularValues i) - ‖δA‖)) := by
  have := neZero_of_ne_zero hx0
  have hAn := l2_opNorm_pos_of_linearIndependent hA
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hrn : 0 < ‖r‖ := norm_pos_iff.2 hr0
  have hAx := toEuclideanLin_ne_zero hA hx0
  have hAxn : 0 < ‖toEuclideanLin A x‖ := norm_pos_iff.2 hAx
  have hσ := iInf_singularValues_pos_of_linearIndependent hA
  obtain ⟨hεA, hεb, -⟩ := le_max_div_mul (δA := δA) (δb := δb) hAn hbn
  have h := (ls_perturbation_bounds hδA hx hx' hr hr' hεA hεb).2
  obtain ⟨-, htan⟩ := equation_5_3_16 A hb (hx ▸ hAx)
  have hsin := sin_thetaLS A hb
  rw [← hx, ← hr] at htan hsin
  rw [div_le_iff₀ hrn]
  refine h.trans (le_of_eq ?_)
  rw [hsin, htan, kappa2_eq_div hA, nuLS, ← hx]
  field_simp

/-- `1/σ' ≤ 1/σ + 2t/σ²` and `1/σ'² ≤ 1/σ² + 6t/σ³` for `σ' ≥ σ - t`, `0 ≤ t ≤ σ/2`. -/
theorem one_div_le_add_of_sub_le {σ σ' t : ℝ} (hσ : 0 < σ) (ht0 : 0 ≤ t) (ht : 2 * t ≤ σ)
    (h : σ - t ≤ σ') :
    1 / σ' ≤ 1 / σ + 2 * t / σ ^ 2 ∧ 1 / σ' ^ 2 ≤ 1 / σ ^ 2 + 6 * t / σ ^ 3 := by
  have hst : 0 < σ - t := by linarith
  have h1 : 1 / σ' ≤ 1 / σ + 2 * t / σ ^ 2 := by
    refine (one_div_le_one_div_of_le hst h).trans ?_
    rw [div_le_iff₀ hst]
    have e : (1 / σ + 2 * t / σ ^ 2) * (σ - t) = 1 + t * (σ - 2 * t) / σ ^ 2 := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ t * (σ - 2 * t) / σ ^ 2 := div_nonneg (mul_nonneg ht0 (by linarith)) (by positivity)
    linarith
  refine ⟨h1, ?_⟩
  have h0 : 0 ≤ 1 / σ' := one_div_nonneg.2 (by linarith)
  have h2 : 1 / σ' ^ 2 ≤ (1 / σ + 2 * t / σ ^ 2) ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    rwa [div_pow, one_pow] at this
  have e2 : 1 / σ ^ 2 + 6 * t / σ ^ 3 - (1 / σ + 2 * t / σ ^ 2) ^ 2 =
      2 * t * (σ - 2 * t) / σ ^ 4 := by
    field_simp
    ring
  have : 0 ≤ 2 * t * (σ - 2 * t) / σ ^ 4 :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

/-- **Theorem 5.3.1** as printed, the `+ O(ε²)` reading: for `A` of rank `n` and `b` with `b`,
`r_LS` and `x_LS` nonzero there are `K` and `ε₀ > 0` such that for all perturbations with
`ε = max(‖δA‖₂/‖A‖₂, ‖δb‖₂/‖b‖₂) ≤ ε₀`,
`‖x̂_LS - x_LS‖₂/‖x_LS‖₂ ≤ ε {ν_LS/cos θ_LS + [1 + ν_LS tan θ_LS] κ₂(A)} + K ε²` (5.3.11) and
`‖r̂_LS - r_LS‖₂/‖r_LS‖₂ ≤ ε {1/sin θ_LS + [1/(ν_LS tan θ_LS) + 1] κ₂(A)} + K ε²` (5.3.12). From
the rigorous bounds behind `theorem_5_3_1_a` and `theorem_5_3_1_b` and
`1/(σ_n - ε‖A‖₂) ≤ 1/σ_n + 2ε‖A‖₂/σ_n²` for `ε ≤ ε₀ = σ_n/(2‖A‖₂)`. -/
theorem theorem_5_3_1 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {b : EuclideanSpace ℝ (Fin m)} (hb : b ≠ 0)
    (hr0 : b - toEuclideanLin A (toEuclideanLin A.pinv b) ≠ 0)
    (hx0 : toEuclideanLin A.pinv b ≠ 0) :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ (δA : Matrix (Fin m) (Fin n) ℝ) (δb : EuclideanSpace ℝ (Fin m)),
      max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) ≤ ε₀ →
      ‖toEuclideanLin (A + δA).pinv (b + δb) - toEuclideanLin A.pinv b‖ /
          ‖toEuclideanLin A.pinv b‖ ≤
        max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) * (nuLS A b / Real.cos (thetaLS A b) +
          (1 + nuLS A b * Real.tan (thetaLS A b)) * kappa2 A) +
          K * max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) ^ 2 ∧
      ‖((b + δb) - toEuclideanLin (A + δA) (toEuclideanLin (A + δA).pinv (b + δb))) -
          (b - toEuclideanLin A (toEuclideanLin A.pinv b))‖ /
          ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ ≤
        max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) * (1 / Real.sin (thetaLS A b) +
          (1 / (nuLS A b * Real.tan (thetaLS A b)) + 1) * kappa2 A) +
          K * max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) ^ 2 := by
  have := neZero_of_ne_zero hx0
  have hAn := l2_opNorm_pos_of_linearIndependent hA
  have hσ := iInf_singularValues_pos_of_linearIndependent hA
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hxn : 0 < ‖toEuclideanLin A.pinv b‖ := norm_pos_iff.2 hx0
  have hrn := norm_pos_iff.2 hr0
  have hAx := toEuclideanLin_ne_zero hA hx0
  have hAxn := norm_pos_iff.2 hAx
  obtain ⟨hcos, htan⟩ := equation_5_3_16 A hb hAx
  have hsin := sin_thetaLS A hb
  have hκ := kappa2_eq_div hA
  set x := toEuclideanLin A.pinv b with hx
  set r := b - toEuclideanLin A x with hr
  set σ := ⨅ i, A.singularValues i with hσdef
  set a := ‖A‖ with ha
  set P := ‖b‖ + a * ‖x‖ with hP
  set Q := a * ‖r‖ with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  -- the book's brackets
  have eq1 : nuLS A b / Real.cos (thetaLS A b) +
      (1 + nuLS A b * Real.tan (thetaLS A b)) * kappa2 A = (P / σ + Q / σ ^ 2) / ‖x‖ := by
    rw [nuLS, ← hx, ← hσdef, hcos, htan, hκ, hP, hQ]
    field_simp
    ring
  have eq2 : 1 / Real.sin (thetaLS A b) +
      (1 / (nuLS A b * Real.tan (thetaLS A b)) + 1) * kappa2 A = P / ‖r‖ + a / σ := by
    rw [nuLS, ← hx, ← hσdef, hsin, htan, hκ, hP]
    field_simp
    ring
  refine ⟨(2 * a * P / σ ^ 2 + 6 * a * Q / σ ^ 3) / ‖x‖ + 2 * a ^ 2 / σ ^ 2, σ / (2 * a),
    by positivity, fun δA δb hε => ?_⟩
  set ε := max (‖δA‖ / a) (‖δb‖ / ‖b‖) with hεdef
  obtain ⟨hεA, hεb, hε0⟩ := le_max_div_mul (δA := δA) (δb := δb) hAn hbn
  have ht : 2 * (ε * a) ≤ σ := by
    rw [le_div_iff₀ (by positivity)] at hε
    linarith
  have hδA : ‖δA‖ < σ := by nlinarith
  obtain ⟨h1, h2⟩ := ls_perturbation_bounds hδA hx rfl hr rfl hεA hεb
  obtain ⟨hu, hu2⟩ := one_div_le_add_of_sub_le hσ (by positivity) ht (show σ - ε * a ≤ σ - ‖δA‖ by
    linarith)
  have hK2 : 0 ≤ 2 * a ^ 2 / σ ^ 2 := by positivity
  have hK1 : 0 ≤ (2 * a * P / σ ^ 2 + 6 * a * Q / σ ^ 3) / ‖x‖ := by positivity
  constructor
  · rw [eq1, div_le_iff₀ hxn]
    calc ‖toEuclideanLin (A + δA).pinv (b + δb) - x‖
        ≤ ε * (P * (1 / σ + 2 * (ε * a) / σ ^ 2) + Q * (1 / σ ^ 2 + 6 * (ε * a) / σ ^ 3)) := by
          refine h1.trans ?_
          rw [div_eq_mul_one_div P, div_eq_mul_one_div Q]
          exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hu hP0)
            (mul_le_mul_of_nonneg_left hu2 hQ0)) hε0
      _ = (ε * ((P / σ + Q / σ ^ 2) / ‖x‖) +
            (2 * a * P / σ ^ 2 + 6 * a * Q / σ ^ 3) / ‖x‖ * ε ^ 2) * ‖x‖ := by
          field_simp
          ring
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_right hK2
  · rw [eq2, div_le_iff₀ hrn]
    calc ‖(b + δb) - toEuclideanLin (A + δA) (toEuclideanLin (A + δA).pinv (b + δb)) - r‖
        ≤ ε * (P + Q * (1 / σ + 2 * (ε * a) / σ ^ 2)) := by
          refine h2.trans ?_
          rw [div_eq_mul_one_div Q]
          exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hu hQ0)) hε0
      _ = (ε * (P / ‖r‖ + a / σ) + 2 * a ^ 2 / σ ^ 2 * ε ^ 2) * ‖r‖ := by
          rw [hQ]
          field_simp
          ring
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_left hK1

/-- **(5.3.9)**, "easily verified using the SVD": for `A ∈ ℝ^{m×n}` of full column rank
(`n ≥ 1`) and `m > n`, `‖A(AᵀA)⁻¹Aᵀ‖₂ = 1`, `‖(AᵀA)⁻¹Aᵀ‖₂ = 1/σ_n(A)`,
`‖I - A(AᵀA)⁻¹Aᵀ‖₂ = 1` and `‖(AᵀA)⁻¹‖₂ = 1/σ_n(A)²`. (`(AᵀA)⁻¹Aᵀ` is the pseudoinverse `A⁺`.) -/
theorem equation_5_3_9 [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (hmn : n < m) :
    ‖A * (Aᵀ * A)⁻¹ * Aᵀ‖ = 1 ∧ ‖(Aᵀ * A)⁻¹ * Aᵀ‖ = 1 / ⨅ i, A.singularValues i ∧
      ‖1 - A * (Aᵀ * A)⁻¹ * Aᵀ‖ = 1 ∧ ‖(Aᵀ * A)⁻¹‖ = 1 / (⨅ i, A.singularValues i) ^ 2 := by
  have hp : A.pinv = (Aᵀ * A)⁻¹ * Aᵀ := by
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA,
      conjTranspose_eq_transpose_of_trivial]
  have hA0 : A ≠ 0 := norm_pos_iff.1 (l2_opNorm_pos_of_linearIndependent hA)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← hp]
    exact l2_opNorm_mul_pinv_eq_one hA0
  · rw [← hp, l2_opNorm_pinv_eq_inv_iInf_singularValues hA, one_div]
  · rw [Matrix.mul_assoc, ← hp]
    exact l2_opNorm_one_sub_mul_pinv_eq_one (by simpa using hmn)
  · have h := l2_opNorm_inv_conjTranspose_mul_self hA
    rw [conjTranspose_eq_transpose_of_trivial] at h
    rw [h, one_div, inv_pow]

/-- **§5.3.6**: `ν_LS = ‖A x_LS‖₂/(σ_n(A) ‖x_LS‖₂) ≤ ‖A‖₂/σ_n(A) = κ₂(A)`, since
`‖A x_LS‖₂ ≤ ‖A‖₂ ‖x_LS‖₂`. -/
theorem nuLS_le_kappa2 [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (b : EuclideanSpace ℝ (Fin m)) : nuLS A b ≤ kappa2 A := by
  have hσ := iInf_singularValues_pos_of_linearIndependent hA
  rw [nuLS, kappa2_eq_div hA]
  rcases eq_or_ne (toEuclideanLin A.pinv b) 0 with h | h
  · rw [h, norm_zero, mul_zero, div_zero]
    exact div_nonneg (norm_nonneg _) hσ.le
  · have hxn := norm_pos_iff.2 h
    rw [div_le_div_iff₀ (by positivity) hσ]
    calc ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ * ⨅ i, A.singularValues i
        ≤ ‖A‖ * ‖toEuclideanLin A.pinv b‖ * ⨅ i, A.singularValues i := by
          gcongr
          exact norm_toEuclideanLin_apply_le _ _
      _ = ‖A‖ * ((⨅ i, A.singularValues i) * ‖toEuclideanLin A.pinv b‖) := by ring

/-- **(5.3.15)**: with `x(t) = (A + tE)⁺(b + tf)`, the solution of (5.3.13) near `t = 0`,
`ẋ(0) = (AᵀA)⁻¹Aᵀ(f - E x_LS) + (AᵀA)⁻¹Eᵀ r_LS`. -/
theorem equation_5_3_15 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (E : Matrix (Fin m) (Fin n) ℝ) (b f : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => toEuclideanLin (A + t • E).pinv (b + t • f))
      (toEuclideanLin ((Aᵀ * A)⁻¹ * Aᵀ) (f - toEuclideanLin E (toEuclideanLin A.pinv b)) +
        toEuclideanLin ((Aᵀ * A)⁻¹ * Eᵀ) (b - toEuclideanLin A (toEuclideanLin A.pinv b))) 0 := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using hasDerivAt_pinv_mulVec_line hA E b f

/-- **The residual's derivative** in the proof of Theorem 5.3.1: with
`r(t) = (b + tf) - (A + tE) x(t)`, `ṙ(0) = (I - A(AᵀA)⁻¹Aᵀ)(f - E x_LS) - A(AᵀA)⁻¹Eᵀ r_LS`. -/
theorem equation_5_3_15_residual {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (E : Matrix (Fin m) (Fin n) ℝ) (b f : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => (b + t • f) -
        toEuclideanLin (A + t • E) (toEuclideanLin (A + t • E).pinv (b + t • f)))
      (toEuclideanLin (1 - A * (Aᵀ * A)⁻¹ * Aᵀ)
          (f - toEuclideanLin E (toEuclideanLin A.pinv b)) -
        toEuclideanLin (A * (Aᵀ * A)⁻¹ * Eᵀ)
          (b - toEuclideanLin A (toEuclideanLin A.pinv b))) 0 := by
  set X : ℝ → EuclideanSpace ℝ (Fin n) := fun t => toEuclideanLin (A + t • E).pinv (b + t • f)
    with hXdef
  have hX := equation_5_3_15 hA E b f
  have hX0 : X 0 = toEuclideanLin A.pinv b := by simp [hXdef]
  have hb : HasDerivAt (fun t : ℝ => b + t • f) f 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const f).const_add b
  have hA' := (LinearMap.toContinuousLinearMap (toEuclideanLin A)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hX
  have hE' := (LinearMap.toContinuousLinearMap (toEuclideanLin E)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hX
  have hEt := (hasDerivAt_id (0 : ℝ)).smul hE'
  have hsum := hb.sub (hA'.add hEt)
  have hfun : (fun t : ℝ => (b + t • f) -
      toEuclideanLin (A + t • E) (toEuclideanLin (A + t • E).pinv (b + t • f))) =
      (fun t : ℝ => b + t • f) - (LinearMap.toContinuousLinearMap (toEuclideanLin A) ∘ X +
        (id : ℝ → ℝ) • (LinearMap.toContinuousLinearMap (toEuclideanLin E) ∘ X)) := by
    funext t
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap', id_eq, hXdef]
    rw [show toEuclideanLin (A + t • E) = toEuclideanLin A + t • toEuclideanLin E by
      rw [map_add, map_smul], LinearMap.add_apply, LinearMap.smul_apply]
  have e0 : ∀ v, toEuclideanLin (1 - A * (Aᵀ * A)⁻¹ * Aᵀ) v =
      v - toEuclideanLin A (toEuclideanLin ((Aᵀ * A)⁻¹ * Aᵀ) v) := fun v => by
    rw [map_sub, LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply, Matrix.mul_assoc,
      toEuclideanLin_mul_apply]
  have e1 : ∀ v, toEuclideanLin (A * (Aᵀ * A)⁻¹ * Eᵀ) v =
      toEuclideanLin A (toEuclideanLin ((Aᵀ * A)⁻¹ * Eᵀ) v) := fun v => by
    rw [Matrix.mul_assoc, toEuclideanLin_mul_apply]
  rw [hfun]
  convert hsum using 1
  simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap', id, zero_smul,
    add_zero, zero_add, one_smul]
  rw [e0, e1, map_add]
  abel

end SensitivityBounds

/-! ### §5.3.8 The augmented system -/

section Augmented

/-- **(5.3.20)**: if `[I_m A; Aᵀ 0][r; x] = [b; 0]` then `‖b - Ax‖₂ = min`; and the augmented
matrix is nonsingular iff `rank(A) = n`. -/
theorem equation_5_3_20 (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ (b r : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)),
        r + toEuclideanLin A x = b → toEuclideanLin Aᵀ r = 0 → IsLeastSquaresSolution A b x) ∧
      (IsUnit (fromBlocks 1 A Aᵀ 0) ↔ LinearIndependent ℝ Aᵀ) := by
  refine ⟨fun b r x h1 h2 => ?_, ?_⟩
  · have := isLeastSquaresSolution_of_augmented (M := (1 : Matrix (Fin m) (Fin m) ℝ)) isUnit_one
      (A := A) (b := b) (r := r) (x := x)
      (by simpa using h1) (by rwa [conjTranspose_eq_transpose_of_trivial])
    simpa using this
  · have := isUnit_augmented_iff A
    rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **§5.3.8, solving the augmented system by QR**: if `A = QR` (`n ≤ m`, `R₁ = R(1:n, 1:n)`),
`Qᵀf = [f₁; f₂]`, `R₁ᵀ h = g`, `R₁ z = f₁ - h` and `p = Q [h; f₂]`, then
`[I A; Aᵀ 0][p; z] = [f; g]` (the transformed system
`[I_n 0 R₁; 0 I_{m-n} 0; R₁ᵀ 0 0][h; f₂; z] = [f₁; f₂; g]`). The vector `[h; f₂]` is `h` in the
first `n` positions and `Qᵀf` below. -/
theorem augmentedSolve_qr {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (hQR : IsQR A Q R) (hnm : n ≤ m) (f : Fin m → ℝ)
    (g : Fin n → ℝ) {h z : Fin n → ℝ} (hh : (firstRows R hnm)ᵀ *ᵥ h = g)
    (hz : firstRows R hnm *ᵥ z = fun i => (Qᵀ *ᵥ f) (Fin.castLE hnm i) - h i) :
    fromBlocks 1 A Aᵀ 0 *ᵥ Sum.elim
        (Q *ᵥ fun i => if hi : (i : ℕ) < n then h ⟨i, hi⟩ else (Qᵀ *ᵥ f) i) z =
      Sum.elim f g := by
  set y : Fin m → ℝ := fun i => if hi : (i : ℕ) < n then h ⟨i, hi⟩ else (Qᵀ *ᵥ f) i with hy
  have hQ : Qᵀ * Q = 1 := by
    have := hQR.mem_unitaryGroup
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      at this
    exact this
  have hQ' : Q * Qᵀ = 1 := by
    have := hQR.mem_unitaryGroup
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      at this
    exact this
  -- `R z` is `R₁ z` padded with zeros
  have hRz : ∀ i : Fin m, (R *ᵥ z) i =
      if hi : (i : ℕ) < n then (firstRows R hnm *ᵥ z) ⟨i, hi⟩ else 0 := by
    intro i
    split_ifs with hi
    · rfl
    · simp only [mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hQR.apply_eq_zero i j (by have := j.isLt; omega), zero_mul]
  have hyRz : y + R *ᵥ z = Qᵀ *ᵥ f := by
    ext i
    rw [Pi.add_apply, hRz, hy]
    simp only
    split_ifs with hi
    · rw [hz]
      simp only
      rw [add_sub_cancel]
      rfl
    · rw [add_zero]
  have hRy : Rᵀ *ᵥ y = g := by
    ext j
    have h1 : ((firstRows R hnm)ᵀ *ᵥ h) j =
        ∑ k : Fin n, (fun i : Fin m => R i j * y i) (Fin.castLE hnm k) := by
      simp only [mulVec, dotProduct, transpose_apply, firstRows, submatrix_apply, id]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hy, Fin.val_castLE]
    rw [← hh, h1]
    refine Eq.trans ?_ (Fin.sum_castLE_eq_sum_ite hnm (fun i : Fin m => R i j * y i)).symm
    simp only [mulVec, dotProduct, transpose_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rfl
    · rw [hQR.apply_eq_zero i j (by have := j.isLt; omega), zero_mul]
  rw [fromBlocks_mulVec]
  ext (i | j)
  · simp only [Sum.elim_inl, Function.comp_def, Sum.elim_inr, one_mulVec]
    rw [← hQR.mul_eq, ← mulVec_mulVec, ← mulVec_add, hyRz, mulVec_mulVec, hQ', one_mulVec]
  · simp only [Sum.elim_inr, Function.comp_def, Sum.elim_inl, zero_mulVec, add_zero]
    rw [← hQR.mul_eq, transpose_mul, mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one, hRy]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- `Qᵀ y` for the factored form stored by Algorithm 5.2.1 with the `β` it **returned**
(convention 13): the reflectors `H₁, …, H_n` applied in turn, each by `householderApplyLeft` on the
rows `j:m` of the single column `y`. -/
noncomputable def storedQTransposeMulVec (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ)
    (y : Fin m → ℝ) : M (Fin m → ℝ) := do
  let Y ← (List.finRange n).foldlM (fun (Y : Matrix (Fin m) (Fin 1) ℝ) j =>
    householderApplyLeft rnd (storedHouseholderVec A j) (β j) (indexFrom m j) [0] Y)
    (of fun i _ => y i)
  pure fun i => Y i 0

/-- `Q y` for the factored form stored by Algorithm 5.2.1 with the returned `β`: the reflectors
applied in the reverse order `H_n, …, H₁`. The twin of `storedQTransposeMulVec`. -/
noncomputable def storedQMulVec (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ)
    (y : Fin m → ℝ) : M (Fin m → ℝ) := do
  let Y ← (List.finRange n).reverse.foldlM (fun (Y : Matrix (Fin m) (Fin 1) ℝ) j =>
    householderApplyLeft rnd (storedHouseholderVec A j) (β j) (indexFrom m j) [0] Y)
    (of fun i _ => y i)
  pure fun i => Y i 0

/-- One step of the iterative improvement of §5.3.8 at the iterate `(r, x)`, with the QR
factorization `(A', β)` of Algorithm 5.2.1: the residuals `f = b - r - A x`, `g = -Aᵀ r` in the
higher precision `rndHi`, then the QR solution of `[I A; Aᵀ 0][p; z] = [f; g]`
(`augmentedSolve_qr`: `[f₁; f₂] = Qᵀ f`, `R₁ᵀ h = g`, `R₁ z = f₁ - h`, `p = Q [h; f₂]`), then
`[r; x] += [p; z]`. -/
noncomputable def lsImprovementStep (rndHi : ℝ → M ℝ) (hnm : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (QR : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ))
    (st : (Fin m → ℝ) × (Fin n → ℝ)) : M ((Fin m → ℝ) × (Fin n → ℝ)) := do
  let f ← (List.finRange m).foldlM (fun (f : Fin m → ℝ) i => do
    let s ← dotAccum rndHi (List.finRange n) (A i) st.2 0
    let t ← rndHi (b i - st.1 i)
    let u ← rndHi (t - s)
    pure (Function.update f i u)) 0
  let g ← (List.finRange n).foldlM (fun (g : Fin n → ℝ) k => do
    let s ← dotAccum rndHi (List.finRange m) (fun i => A i k) st.1 0
    pure (Function.update g k (-s))) 0
  let c ← storedQTransposeMulVec rnd QR.1 QR.2 f
  let R₁ := (upperPart QR.1).firstRows hnm
  let h ← Chapter03.algorithm_3_1_1 rnd R₁ᵀ g
  let d ← (List.finRange n).foldlM (fun (d : Fin n → ℝ) k => do
    let e ← rnd (c (Fin.castLE hnm k) - h k)
    pure (Function.update d k e)) 0
  let z ← Chapter03.algorithm_3_1_2 rnd R₁ d
  let p ← storedQMulVec rnd QR.1 QR.2 fun i => if hi : (i : ℕ) < n then h ⟨i, hi⟩ else c i
  let r ← (List.finRange m).foldlM (fun (r : Fin m → ℝ) i => do
    let e ← rnd (r i + p i)
    pure (Function.update r i e)) st.1
  let x ← (List.finRange n).foldlM (fun (x : Fin n → ℝ) k => do
    let e ← rnd (x k + z k)
    pure (Function.update x k e)) st.2
  pure (r, x)

/-- **§5.3.8, iterative improvement of the augmented system** (displayed, unnumbered):
```
r⁽⁰⁾ = 0, x⁽⁰⁾ = 0
for k = 0, 1, …
    [f⁽ᵏ⁾; g⁽ᵏ⁾] = [b; 0] - [I A; Aᵀ 0][r⁽ᵏ⁾; x⁽ᵏ⁾]
    [I A; Aᵀ 0][p⁽ᵏ⁾; z⁽ᵏ⁾] = [f⁽ᵏ⁾; g⁽ᵏ⁾]
    [r⁽ᵏ⁺¹⁾; x⁽ᵏ⁺¹⁾] = [r⁽ᵏ⁾; x⁽ᵏ⁾] + [p⁽ᵏ⁾; z⁽ᵏ⁾]
end
```
"The residuals `f⁽ᵏ⁾` and `g⁽ᵏ⁾` must be computed in higher precision": a second rounding hook
`rndHi`. The augmented systems are solved through the QR factorization of Algorithm 5.2.1, computed
once, "stored in factored form" (`lsImprovementStep`). `fuel` is the number of iterations. -/
noncomputable def lsIterativeImprovement (rndHi : ℝ → M ℝ) (hnm : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (fuel : ℕ) :
    M ((Fin m → ℝ) × (Fin n → ℝ)) := do
  let QR ← algorithm_5_2_1 rnd A
  (List.range fuel).foldlM (fun st _ => lsImprovementStep rnd rndHi hnm A b QR st) (0, 0)

end Programs

/-- A reflector with a vector vanishing off `indexFrom m j`, applied to a single column. -/
private theorem householderApplyLeft_col_pure (A : Matrix (Fin m) (Fin n) ℝ) (β : ℝ) (j : Fin n)
    (Y : Matrix (Fin m) (Fin 1) ℝ) :
    Id.run (householderApplyLeft pure (storedHouseholderVec A j) β (indexFrom m j) [0] Y) =
      (1 - β • vecMulVec (storedHouseholderVec A j) (storedHouseholderVec A j)) * Y :=
  householderApplyLeft_spec_of_forall_mem (nodup_indexFrom m j) (List.nodup_singleton 0)
    (fun q => by rw [Fin.fin_one_eq_zero q]; exact List.mem_singleton_self 0)
    (fun _ hi => storedHouseholderVec_eq_zero A j hi) β Y

/-- In exact arithmetic `storedQTransposeMulVec` computes `Qᵀ y` for `Q = factoredQ β A`. -/
theorem storedQTransposeMulVec_pure (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ)
    (y : Fin m → ℝ) : Id.run (storedQTransposeMulVec pure A β y) = (factoredQ β A)ᵀ *ᵥ y := by
  simp only [storedQTransposeMulVec, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    householderApplyLeft_col_pure]
  rw [foldl_mul_eq_transpose_prod_mul _ (fun j => transpose_one_sub_smul_vecMulVec _ _),
    ← factoredQ_eq_prod]
  funext i
  simp [mul_apply, mulVec, dotProduct]

/-- In exact arithmetic `storedQMulVec` computes `Q y` for `Q = factoredQ β A`. -/
theorem storedQMulVec_pure (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) (y : Fin m → ℝ) :
    Id.run (storedQMulVec pure A β y) = factoredQ β A *ᵥ y := by
  simp only [storedQMulVec, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    householderApplyLeft_col_pure]
  have key : ∀ (l : List (Fin n)) (Y : Matrix (Fin m) (Fin 1) ℝ),
      l.reverse.foldl (fun Y j => (1 - β j • vecMulVec (storedHouseholderVec A j)
        (storedHouseholderVec A j)) * Y) Y =
        (l.map fun j => 1 - β j • vecMulVec (storedHouseholderVec A j)
          (storedHouseholderVec A j)).prod * Y := by
    intro l
    induction l with
    | nil => intro Y; simp
    | cons a l ih =>
      intro Y
      rw [List.reverse_cons, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        List.map_cons, List.prod_cons, Matrix.mul_assoc]
  rw [key, ← factoredQ_eq_prod]
  funext i
  simp [mul_apply, mulVec, dotProduct]

/-- One exact step of the iterative improvement lands on the solution of the augmented system
(5.3.20): whatever the current iterate, `r + A x = b` and `Aᵀ r = 0` afterwards. -/
private theorem lsImprovementStep_pure (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (b : Fin m → ℝ) (st : (Fin m → ℝ) × (Fin n → ℝ)) :
    (Id.run (lsImprovementStep pure pure hnm A b (Id.run (algorithm_5_2_1 pure A)) st)).1 +
        A *ᵥ (Id.run (lsImprovementStep pure pure hnm A b
          (Id.run (algorithm_5_2_1 pure A)) st)).2 = b ∧
      Aᵀ *ᵥ (Id.run (lsImprovementStep pure pure hnm A b
        (Id.run (algorithm_5_2_1 pure A)) st)).1 = 0 := by
  obtain ⟨hQR, -⟩ := algorithm_5_2_1_spec hnm A
  set QR := Id.run (algorithm_5_2_1 pure A) with hQRdef
  set Q := factoredQ QR.2 QR.1 with hQ
  set R₁ := (upperPart QR.1).firstRows hnm with hR₁
  have hup := hQR.isUpperTriangular_firstRows hnm
  have hdiag := hQR.firstRows_diag_ne_zero_of_linearIndependent hnm hA
  set f : Fin m → ℝ := b - st.1 - A *ᵥ st.2 with hf
  set g : Fin n → ℝ := -(Aᵀ *ᵥ st.1) with hg
  set h := Id.run (Chapter03.algorithm_3_1_1 pure R₁ᵀ g) with hh
  set z := Id.run (Chapter03.algorithm_3_1_2 pure R₁
    fun k => (Qᵀ *ᵥ f) (Fin.castLE hnm k) - h k) with hz
  set p := Q *ᵥ fun i => if hi : (i : ℕ) < n then h ⟨i, hi⟩ else (Qᵀ *ᵥ f) i with hp
  have hlow : R₁ᵀ.IsLowerTriangular := fun i j hij => hup hij
  have hh' : R₁ᵀ *ᵥ h = g := Chapter03.algorithm_3_1_1_spec hlow
    (fun i => by rw [transpose_apply]; exact hdiag i) g
  have hrun : Id.run (lsImprovementStep pure pure hnm A b QR st) = (st.1 + p, st.2 + z) := by
    have hf' : (fun k => b k - st.1 k - (0 + ((List.finRange n).map fun j =>
        A k j * st.2 j).sum)) = f := by
      funext k
      simp [hf, mulVec, dotProduct, Fin.sum_univ_def]
    have hg' : (fun k => -(0 + ((List.finRange m).map fun i => A i k * st.1 i).sum)) = g := by
      funext k
      simp [hg, mulVec, dotProduct, Fin.sum_univ_def]
    simp only [lsImprovementStep, Id.run_bind, Id.run_pure, List.idRun_foldlM, dotAccum_pure,
      storedQTransposeMulVec_pure, storedQMulVec_pure, pure_bind, foldl_update_eq,
      List.mem_finRange, ↓reduceIte, hf', hg', ← hQ, ← hR₁, ← hh]
    simp only [← hz, ← hp]
    rw [foldl_update_self_eq (fun k c => c + p k) _ (List.nodup_finRange m),
      foldl_update_self_eq (fun k c => c + z k) _ (List.nodup_finRange n)]
    simp only [List.mem_finRange, ↓reduceIte]
    rfl
  have hz' : R₁ *ᵥ z = fun k => (Qᵀ *ᵥ f) (Fin.castLE hnm k) - h k :=
    Chapter03.algorithm_3_1_2_spec hup hdiag _
  have haug := augmentedSolve_qr hQR hnm f g hh' hz'
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec, zero_mulVec,
    add_zero] at haug
  have e1 : p + A *ᵥ z = f := funext fun i => congrFun haug (Sum.inl i)
  have e2 : Aᵀ *ᵥ p = g := funext fun j => congrFun haug (Sum.inr j)
  rw [hrun]
  refine ⟨?_, ?_⟩
  · simp only
    rw [mulVec_add, show st.1 + p + (A *ᵥ st.2 + A *ᵥ z) = st.1 + A *ᵥ st.2 + (p + A *ᵥ z) by
      abel, e1, hf]
    abel
  · simp only
    rw [mulVec_add, e2, hg, add_neg_cancel]

/-- **Iterative improvement in exact arithmetic**: after at least one iteration the iterate is the
exact solution of the augmented system (5.3.20) — `r + A x = b`, `Aᵀ r = 0` — hence `x` is the
least-squares solution `x_LS` and `r = r_LS`. (Björck's digit-gain claim is not formalized.) -/
theorem lsIterativeImprovement_spec (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (b : Fin m → ℝ) {fuel : ℕ} (hfuel : 0 < fuel) :
    let out := Id.run (lsIterativeImprovement pure pure hnm A b fuel)
    out.1 + A *ᵥ out.2 = b ∧ Aᵀ *ᵥ out.1 = 0 ∧
      IsLeastSquaresSolution A (toLp 2 b) (toLp 2 out.2) := by
  intro out
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have hout : out = Id.run (lsImprovementStep pure pure hnm A b (Id.run (algorithm_5_2_1 pure A))
      ((List.range k).foldl (fun st _ => Id.run (lsImprovementStep pure pure hnm A b
        (Id.run (algorithm_5_2_1 pure A)) st)) (0, 0))) := by
    simp only [out, lsIterativeImprovement, Id.run_bind, List.idRun_foldlM, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  obtain ⟨h1, h2⟩ := lsImprovementStep_pure hnm hA b
    ((List.range k).foldl (fun st _ => Id.run (lsImprovementStep pure pure hnm A b
      (Id.run (algorithm_5_2_1 pure A)) st)) (0, 0))
  rw [← hout] at h1 h2
  refine ⟨h1, h2, (equation_5_3_20 A).1 _ (toLp 2 out.1) _ ?_ ?_⟩
  · rw [toEuclideanLin_toLp, ← toLp_add, h1]
  · rw [toEuclideanLin_toLp, h2]
    rfl

end Augmented

/-! ### §5.3.9 Point/line/plane nearness problems in 3-space -/

section CrossProduct

/-- **§5.3.9, the cross-product matrix** `v^c = [0 -v₃ v₂; v₃ 0 -v₁; -v₂ v₁ 0]` of `v ∈ ℝ³`, with
`p × q = p^c q` (`crossMatrix_mulVec`). -/
def crossMatrix (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0]

/-- `p × q = p^c q = -q^c p = -(q × p)`. -/
theorem crossMatrix_mulVec (p q : Fin 3 → ℝ) :
    p ⨯₃ q = crossMatrix p *ᵥ q ∧ p ⨯₃ q = -(crossMatrix q *ᵥ p) ∧ p ⨯₃ q = -(q ⨯₃ p) := by
  refine ⟨?_, ?_, (cross_anticomm q p).symm⟩ <;>
  · ext i
    fin_cases i <;> simp [crossMatrix, cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;>
      ring

/-- The entries of `(a bᵀ) x = a (bᵀx)`. -/
theorem vecMulVec_mulVec_apply {k : ℕ} (a b x : Fin k → ℝ) (i : Fin k) :
    (vecMulVec a b *ᵥ x) i = a i * (b ⬝ᵥ x) := by
  simp only [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]

/-- **(5.3.21)**: `p × q ∈ span{p, q}⊥`. -/
theorem equation_5_3_21 (p q : Fin 3 → ℝ) : p ⬝ᵥ (p ⨯₃ q) = 0 ∧ q ⬝ᵥ (p ⨯₃ q) = 0 :=
  ⟨dot_self_cross p q, dot_cross_self p q⟩

/-- **(5.3.22)**: `(p × q) × r = (p^c q)^c r = (q pᵀ - p qᵀ) r = (pᵀr) q - (qᵀr) p`. -/
theorem equation_5_3_22 (p q r : Fin 3 → ℝ) :
    (p ⨯₃ q) ⨯₃ r = crossMatrix (crossMatrix p *ᵥ q) *ᵥ r ∧
      (p ⨯₃ q) ⨯₃ r = (vecMulVec q p - vecMulVec p q) *ᵥ r ∧
      (p ⨯₃ q) ⨯₃ r = (p ⬝ᵥ r) • q - (q ⬝ᵥ r) • p := by
  have h3 := cross_cross_eq_smul_sub_smul p q r
  refine ⟨by rw [← (crossMatrix_mulVec p q).1, ← (crossMatrix_mulVec _ r).1], ?_, h3⟩
  rw [h3, sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec]
  ext i
  simp [mul_comm]

/-- **(5.3.23)**: `(p × q)ᵀ(r × s) = det([p q]ᵀ[r s])` (the Binet–Cauchy identity). -/
theorem equation_5_3_23 (p q r s : Fin 3 → ℝ) :
    (p ⨯₃ q) ⬝ᵥ (r ⨯₃ s) = det !![p ⬝ᵥ r, p ⬝ᵥ s; q ⬝ᵥ r, q ⬝ᵥ s] := by
  rw [cross_dot_cross, det_fin_two_of]

/-- **(5.3.24)**: `p^c p^c = p pᵀ - ‖p‖₂² I₃`. -/
theorem equation_5_3_24 (p : Fin 3 → ℝ) :
    crossMatrix p * crossMatrix p = vecMulVec p p - (p ⬝ᵥ p) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMatrix, Matrix.mul_apply, Fin.sum_univ_three, vecMulVec_apply, dotProduct] <;>
    ring

/-- **(5.3.25)**: `‖p^c q‖₂² = ‖p‖₂² ‖q‖₂² (1 - (pᵀq / (‖p‖₂ ‖q‖₂))²)` for `p, q ≠ 0`. -/
theorem equation_5_3_25 {p q : Fin 3 → ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    ‖(toLp 2 (crossMatrix p *ᵥ q) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 =
      ‖(toLp 2 p : EuclideanSpace ℝ (Fin 3))‖ ^ 2 * ‖(toLp 2 q : EuclideanSpace ℝ (Fin 3))‖ ^ 2 *
        (1 - (p ⬝ᵥ q / (‖(toLp 2 p : EuclideanSpace ℝ (Fin 3))‖ *
          ‖(toLp 2 q : EuclideanSpace ℝ (Fin 3))‖)) ^ 2) := by
  have hP : 0 < ‖(toLp 2 p : EuclideanSpace ℝ (Fin 3))‖ := by simpa using hp
  have hQ : 0 < ‖(toLp 2 q : EuclideanSpace ℝ (Fin 3))‖ := by simpa using hq
  rw [← (crossMatrix_mulVec p q).1, ← dotProduct_self_eq_norm_sq, cross_dot_cross,
    ← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq, div_pow, mul_pow,
    ← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq, dotProduct_comm q p]
  have hp' : p ⬝ᵥ p ≠ 0 := by rw [dotProduct_self_eq_norm_sq]; positivity
  have hq' : q ⬝ᵥ q ≠ 0 := by rw [dotProduct_self_eq_norm_sq]; positivity
  field_simp

/-- `(z - y) ⊥ v` makes `z` the point of the line `{z + τ v}` closest to `y`: the squared distance
from `y` to `z + τ v` is `‖z - y‖² + τ² ‖v‖²`. -/
private theorem norm_le_of_dotProduct_eq_zero {v w : Fin 3 → ℝ} (h : v ⬝ᵥ w = 0) (τ : ℝ) :
    ‖(toLp 2 w : EuclideanSpace ℝ (Fin 3))‖ ≤
      ‖(toLp 2 (w + τ • v) : EuclideanSpace ℝ (Fin 3))‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq]
  have hvv : 0 ≤ v ⬝ᵥ v := by rw [dotProduct_self_eq_norm_sq]; positivity
  have : (w + τ • v) ⬝ᵥ (w + τ • v) = w ⬝ᵥ w + τ ^ 2 * (v ⬝ᵥ v) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm w v, h]
    ring
  rw [this]
  nlinarith [sq_nonneg τ]

/-- **(5.3.26), point–line**: for `p₁ ≠ p₂`, `v = p₂ - p₁`, the point
`z = y + (1/vᵀv) v^c v^c (y - p₁)` lies on the line `L = {p₁ + τ v}` and is the point of `L`
closest to `y`. -/
theorem equation_5_3_26 {p₁ p₂ : Fin 3 → ℝ} (hp : p₁ ≠ p₂) (y : Fin 3 → ℝ) :
    let v := p₂ - p₁
    let z := y + (1 / (v ⬝ᵥ v)) • ((crossMatrix v * crossMatrix v) *ᵥ (y - p₁))
    (∃ τ : ℝ, z = p₁ + τ • v) ∧
      ∀ τ : ℝ, ‖(toLp 2 (z - y) : EuclideanSpace ℝ (Fin 3))‖ ≤
        ‖(toLp 2 (p₁ + τ • v - y) : EuclideanSpace ℝ (Fin 3))‖ := by
  intro v z
  have hv : v ≠ 0 := sub_ne_zero.2 hp.symm
  have hvv : v ⬝ᵥ v ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]; exact pow_ne_zero 2 (by simpa using hv)
  set t := v ⬝ᵥ (y - p₁) / (v ⬝ᵥ v) with ht
  have hz : z = p₁ + t • v := by
    ext i
    simp only [z, equation_5_3_24, sub_mulVec, smul_mulVec, one_mulVec, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vecMulVec_mulVec_apply, ht]
    field_simp
    ring
  refine ⟨⟨t, hz⟩, fun τ => ?_⟩
  have horth : v ⬝ᵥ (z - y) = 0 := by
    rw [hz, show p₁ + t • v - y = t • v - (y - p₁) by abel, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, ht]
    field_simp
    ring
  have := norm_le_of_dotProduct_eq_zero horth (τ - t)
  rwa [show z - y + (τ - t) • v = p₁ + τ • v - y by rw [hz, sub_smul]; abel] at this

/-- The two closest points of two non-parallel lines, as coefficients along the lines: with
`d₀ = q₁ - p₁`, `r = v × w ≠ 0`, `α = wᵀ r^c d₀ / rᵀr`, `β = vᵀ r^c d₀ / rᵀr`, the difference
`(p₁ + α v) - (q₁ + β w)` is orthogonal to both `v` and `w`. -/
private theorem lineLine_orthogonal {v w d₀ : Fin 3 → ℝ} (hr : v ⨯₃ w ≠ 0) :
    let α := w ⬝ᵥ (crossMatrix (v ⨯₃ w) *ᵥ d₀) / ((v ⨯₃ w) ⬝ᵥ (v ⨯₃ w))
    let β := v ⬝ᵥ (crossMatrix (v ⨯₃ w) *ᵥ d₀) / ((v ⨯₃ w) ⬝ᵥ (v ⨯₃ w))
    v ⬝ᵥ (-d₀ + α • v - β • w) = 0 ∧ w ⬝ᵥ (-d₀ + α • v - β • w) = 0 := by
  intro α β
  have hN : (v ⨯₃ w) ⬝ᵥ (v ⨯₃ w) ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]; exact pow_ne_zero 2 (by simpa using hr)
  have hc : crossMatrix (v ⨯₃ w) *ᵥ d₀ = (v ⬝ᵥ d₀) • w - (w ⬝ᵥ d₀) • v := by
    rw [← (crossMatrix_mulVec _ _).1, cross_cross_eq_smul_sub_smul]
  have hNe : (v ⨯₃ w) ⬝ᵥ (v ⨯₃ w) = (v ⬝ᵥ v) * (w ⬝ᵥ w) - (v ⬝ᵥ w) * (v ⬝ᵥ w) := by
    rw [cross_dot_cross, dotProduct_comm w v]
  simp only [α, β, hc, dotProduct_sub, dotProduct_smul, dotProduct_add, dotProduct_neg,
    smul_eq_mul] at hN ⊢
  rw [dotProduct_comm w v] at *
  constructor <;> field_simp <;> rw [hNe] <;> ring

/-- **(5.3.27), line–line**: for lines `L₁ = {p₁ + τ v}`, `L₂ = {q₁ + τ w}` through `p₁, p₂` and
`q₁, q₂` (`v = p₂ - p₁`, `w = q₂ - q₁`) with `r = v^c w` **nonzero** (non-parallel lines; the book
omits the hypothesis, and for `r = 0` the formula divides by zero), the points
`z₁ = p₁ + (1/rᵀr) v wᵀ r^c (q₁ - p₁)` and `z₂ = q₁ + (1/rᵀr) w vᵀ r^c (q₁ - p₁)` lie on `L₁`
and `L₂` and minimize `‖z₁ - z₂‖₂` over all pairs of points of the two lines. -/
theorem equation_5_3_27 {p₁ p₂ q₁ q₂ : Fin 3 → ℝ}
    (hr : crossMatrix (p₂ - p₁) *ᵥ (q₂ - q₁) ≠ 0) :
    let v := p₂ - p₁
    let w := q₂ - q₁
    let r := crossMatrix v *ᵥ w
    let z₁ := p₁ + (1 / (r ⬝ᵥ r)) • (vecMulVec v w *ᵥ (crossMatrix r *ᵥ (q₁ - p₁)))
    let z₂ := q₁ + (1 / (r ⬝ᵥ r)) • (vecMulVec w v *ᵥ (crossMatrix r *ᵥ (q₁ - p₁)))
    (∃ τ : ℝ, z₁ = p₁ + τ • v) ∧ (∃ τ : ℝ, z₂ = q₁ + τ • w) ∧
      ∀ τ₁ τ₂ : ℝ, ‖(toLp 2 (z₁ - z₂) : EuclideanSpace ℝ (Fin 3))‖ ≤
        ‖(toLp 2 ((p₁ + τ₁ • v) - (q₁ + τ₂ • w)) : EuclideanSpace ℝ (Fin 3))‖ := by
  intro v w r z₁ z₂
  have hr' : v ⨯₃ w ≠ 0 := by rwa [(crossMatrix_mulVec v w).1]
  have hrr : r = v ⨯₃ w := ((crossMatrix_mulVec v w).1).symm
  obtain ⟨hv, hw⟩ := lineLine_orthogonal (d₀ := q₁ - p₁) hr'
  set α := w ⬝ᵥ (crossMatrix (v ⨯₃ w) *ᵥ (q₁ - p₁)) / ((v ⨯₃ w) ⬝ᵥ (v ⨯₃ w)) with hα
  set β := v ⬝ᵥ (crossMatrix (v ⨯₃ w) *ᵥ (q₁ - p₁)) / ((v ⨯₃ w) ⬝ᵥ (v ⨯₃ w)) with hβ
  have hz₁ : z₁ = p₁ + α • v := by
    ext i
    simp only [z₁, hrr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vecMulVec_mulVec_apply, hα]
    ring
  have hz₂ : z₂ = q₁ + β • w := by
    ext i
    simp only [z₂, hrr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vecMulVec_mulVec_apply, hβ]
    ring
  refine ⟨⟨α, hz₁⟩, ⟨β, hz₂⟩, fun τ₁ τ₂ => ?_⟩
  set e := -(q₁ - p₁) + α • v - β • w with he
  have hze : z₁ - z₂ = e := by rw [hz₁, hz₂, he]; abel
  have hd : (p₁ + τ₁ • v) - (q₁ + τ₂ • w) = e + ((τ₁ - α) • v - (τ₂ - β) • w) := by
    rw [he, sub_smul, sub_smul]; abel
  rw [hze, hd]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq]
  set g := (τ₁ - α) • v - (τ₂ - β) • w with hg
  have hge : e ⬝ᵥ g = 0 := by
    rw [hg, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_comm e v,
      dotProduct_comm e w, hv, hw]
    simp
  have hgg : 0 ≤ g ⬝ᵥ g := by rw [dotProduct_self_eq_norm_sq]; positivity
  rw [add_dotProduct, dotProduct_add, dotProduct_add, hge, dotProduct_comm g e, hge]
  linarith

/-- **(5.3.28)**: the point `z₂ = q₁ + (1/rᵀr) w vᵀ r^c (q₁ - p₁)` of `L₂` closest to `L₁` (the
second half of `equation_5_3_27`, under the same non-parallelism hypothesis). -/
theorem equation_5_3_28 {p₁ p₂ q₁ q₂ : Fin 3 → ℝ}
    (hr : crossMatrix (p₂ - p₁) *ᵥ (q₂ - q₁) ≠ 0) :
    let v := p₂ - p₁
    let w := q₂ - q₁
    let r := crossMatrix v *ᵥ w
    let z₁ := p₁ + (1 / (r ⬝ᵥ r)) • (vecMulVec v w *ᵥ (crossMatrix r *ᵥ (q₁ - p₁)))
    let z₂ := q₁ + (1 / (r ⬝ᵥ r)) • (vecMulVec w v *ᵥ (crossMatrix r *ᵥ (q₁ - p₁)))
    (∃ τ : ℝ, z₂ = q₁ + τ • w) ∧
      ∀ τ₁ τ₂ : ℝ, ‖(toLp 2 (z₁ - z₂) : EuclideanSpace ℝ (Fin 3))‖ ≤
        ‖(toLp 2 ((p₁ + τ₁ • v) - (q₁ + τ₂ • w)) : EuclideanSpace ℝ (Fin 3))‖ :=
  ⟨(equation_5_3_27 hr).2.1, (equation_5_3_27 hr).2.2⟩

/-- **(5.3.29), point–plane**: for `p₁, p₂, p₃` **not collinear** (`v = (p₂ - p₁)^c (p₃ - p₁) ≠ 0`;
the book's "three distinct points" is not enough), the point
`z = p₁ - (1/vᵀv) v^c v^c (y - p₁)` lies on the plane `P = {x : xᵀv = p₁ᵀv}` through the three
points, and is the point of `P` closest to `y`. -/
theorem equation_5_3_29 {p₁ p₂ p₃ : Fin 3 → ℝ}
    (hv : crossMatrix (p₂ - p₁) *ᵥ (p₃ - p₁) ≠ 0) (y : Fin 3 → ℝ) :
    let v := crossMatrix (p₂ - p₁) *ᵥ (p₃ - p₁)
    let z := p₁ - (1 / (v ⬝ᵥ v)) • ((crossMatrix v * crossMatrix v) *ᵥ (y - p₁))
    z ⬝ᵥ v = p₁ ⬝ᵥ v ∧ p₂ ⬝ᵥ v = p₁ ⬝ᵥ v ∧ p₃ ⬝ᵥ v = p₁ ⬝ᵥ v ∧
      ∀ x : Fin 3 → ℝ, x ⬝ᵥ v = p₁ ⬝ᵥ v →
        ‖(toLp 2 (z - y) : EuclideanSpace ℝ (Fin 3))‖ ≤
          ‖(toLp 2 (x - y) : EuclideanSpace ℝ (Fin 3))‖ := by
  intro v z
  have hvv : v ⬝ᵥ v ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]; exact pow_ne_zero 2 (by simpa using hv)
  set t := v ⬝ᵥ (y - p₁) / (v ⬝ᵥ v) with ht
  -- `z = y - t v`
  have hz : z = y - t • v := by
    ext i
    simp only [z, equation_5_3_24, sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, vecMulVec_mulVec_apply, ht]
    field_simp
    ring
  have hzv : z ⬝ᵥ v = p₁ ⬝ᵥ v := by
    rw [hz, sub_dotProduct, smul_dotProduct, smul_eq_mul, ht, dotProduct_comm v (y - p₁),
      sub_dotProduct]
    field_simp
    ring
  -- `p₂ - p₁` and `p₃ - p₁` are orthogonal to `v`
  have h2 : p₂ ⬝ᵥ v = p₁ ⬝ᵥ v := by
    have := (equation_5_3_21 (p₂ - p₁) (p₃ - p₁)).1
    rw [(crossMatrix_mulVec _ _).1, sub_dotProduct] at this
    linarith
  have h3 : p₃ ⬝ᵥ v = p₁ ⬝ᵥ v := by
    have := (equation_5_3_21 (p₂ - p₁) (p₃ - p₁)).2
    rw [(crossMatrix_mulVec _ _).1, sub_dotProduct] at this
    linarith
  refine ⟨hzv, h2, h3, fun x hx => ?_⟩
  -- `x - z ⊥ v`, and `z - y = -t v ∥ v`
  have hxz : (x - z) ⬝ᵥ v = 0 := by rw [sub_dotProduct, hx, hzv, sub_self]
  have key : (x - y) ⬝ᵥ (x - y) = (z - y) ⬝ᵥ (z - y) + (x - z) ⬝ᵥ (x - z) := by
    have hzy : z - y = -t • v := by rw [hz]; module
    have e : x - y = (x - z) + (z - y) := by abel
    rw [e, add_dotProduct, dotProduct_add, dotProduct_add, hzy, dotProduct_smul,
      smul_dotProduct, hxz, dotProduct_comm v (x - z), hxz]
    ring
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq, key]
  have : 0 ≤ (x - z) ⬝ᵥ (x - z) := by rw [dotProduct_self_eq_norm_sq]; positivity
  linarith

end CrossProduct

end GolubVanLoan.Chapter05
