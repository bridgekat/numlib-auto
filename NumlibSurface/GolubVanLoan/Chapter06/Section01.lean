import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted

/-!
# Golub–Van Loan §6.1: weighting and regularization

Surface file for [golub2013matrix] §6.1: row weighting and its normal equations (6.1.1)–(6.1.5),
the generalized least-squares problem and Paige's method (6.1.7)–(6.1.10), column weighting
(§6.1.3), ridge regression and cross-validation (6.1.11)–(6.1.19), Tikhonov regularization
(6.1.20)–(6.1.21), and the generalized singular value decomposition (Theorem 6.1.1 with
(6.1.22)–(6.1.23), and (6.1.26)).

## Conventions

Real matrices `A : Matrix (Fin m) (Fin n) ℝ`, 0-based. Vectors of a least-squares statement are
`EuclideanSpace ℝ (Fin n)` and matrices act through `Matrix.toEuclideanLin`, the convention of the
backbone's `LeastSquares`; the entrywise formulas of §6.1.4 (the cross-validation of Golub, Heath
and Wahba) use plain vectors `Fin m → ℝ` and `Matrix.mulVec`, as the backbone's leave-one-out
lemmas do. The book's weight matrix `D = diag(d₁, …, d_m)` is `diagonal d`; `a_kᵀ = A(k, :)` is the
row `A k`. The ridge solution `x(λ) = (AᵀA + λI)⁻¹Aᵀb` is the backbone's Tikhonov regularization
`A.tikhonov λ` applied to `b`. An SVD is a factorization `Matrix.IsSVD A U σ V` (`Uᵀ A V = Σ`,
`σ` sorted and nonnegative), the book's `u_i`, `v_i` the columns of `U` and `V` (the rows
`Uᵀ i`, `Vᵀ i` of the transposes), and a GSVD is
`Matrix.IsGSVD A B U₁ U₂ X α β` in Theorem 6.1.1's block order (`D_A = rectDiagonal α`,
`D_B = shiftedRectDiagonal p β`, `p = max(r − m₂, 0)`). The book's parameter `λ` is written `μ`
(`λ` is reserved in Lean).

## Not formalized

(6.1.6) (a statistical model), (6.1.13) (recalls the SVD), (6.1.24)–(6.1.25) (steps of the proof of
Theorem 6.1.1), Paige's stability claim, van der Sluis's "`κ₂(AG⁻¹)` is approximately minimized",
the choice of `λ` minimizing `C(λ)`, the flop counts.

## Errata

* (6.1.4) and after: the book's `d/dδ [r_k(δ)²] < 0` fails when `a_k = 0` or `r_k(δ) = 0`; only the
  non-strict monotonicity of `|r_k(δ)|` holds (`abs_weightedResidual_antitoneOn`).
* §6.1.3: the least-`G`-norm property of `x_G` holds for every rank, not only `rank(A) < n`.
* (6.1.19): the numerator's `b̃_k` must be `b_k` (as `λ → ∞` the leave-one-out residual tends to
  `b_k`); `equation_6_1_19` states the corrected formula.
* Theorem 6.1.1: the printed row labels of `D_B` (`p, r − p, m₂ − r`) should be
  `r − p, m₂ − r + p`, and `n_{1−r}` is `n₁ − r`; the proof cites "(6.1.21) and (6.1.22)" for
  (6.1.22)–(6.1.23). The theorem never states `α_i² + β_i² = 1`, which its proof gives
  (`theorem_6_1_1_b`).
* §6.1.6: "if `B = I` and we set `X = U₂`, then we obtain the SVD of `A`" is loose: `X = U₂ D_B`,
  and `U₁ᵀ A U₂ = diag(α_i / β_i)` (`gsvd_one`).

## Sources

Backbone `Numlib/LinearAlgebra/Matrix/LeastSquares/{Weighted,Regularized}`,
`Numlib/LinearAlgebra/Matrix/GSVD`.
-/

open Matrix Finset Filter Topology

namespace GolubVanLoan.Chapter06

variable {m n : ℕ}

/-! ### §6.1.1 Row weighting -/

/-- **§6.1.1, the weighted least-squares problem (6.1.1).** "Note that if `x_D` minimizes this
summation, then it minimizes `‖Ãx − b̃‖₂` where `Ã = DA` and `b̃ = Db`": for the weights
`d : Fin m → ℝ` (the book's `D = diag(d₁, …, d_m)`), `x` solves the weighted problem when it is a
least-squares solution of `DAx = Db`. -/
def IsWeightedLeastSquaresSolution (d : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsLeastSquaresSolution (diagonal d * A) (toEuclideanLin (diagonal d) b) x

/-- The weighted objective in coordinates: `‖D(Ax − b)‖₂² = ∑ᵢ dᵢ² (aᵢᵀx − bᵢ)²`. -/
private theorem norm_sq_weighted_eq (d : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    ‖toEuclideanLin (diagonal d * A) x - toEuclideanLin (diagonal d) b‖ ^ 2 =
      ∑ i, d i ^ 2 * (A i ⬝ᵥ WithLp.ofLp x - WithLp.ofLp b i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine sum_congr rfl fun i _ => ?_
  simp only [PiLp.sub_apply, toEuclideanLin_apply, ← mulVec_mulVec, mulVec_diagonal,
    Real.norm_eq_abs, sq_abs]
  rw [← mul_sub, mul_pow]
  rfl

/-- **(6.1.1).** "`min ‖D(Ax − b)‖₂² = min ∑ᵢ dᵢ² (aᵢᵀx − bᵢ)²`": the weighted objective is the
weighted sum of squared discrepancies, so `x` solves the weighted problem iff it minimizes that
sum. -/
theorem equation_6_1_1 (d : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    (‖toEuclideanLin (diagonal d * A) x - toEuclideanLin (diagonal d) b‖ ^ 2 =
      ∑ i, d i ^ 2 * (A i ⬝ᵥ WithLp.ofLp x - WithLp.ofLp b i) ^ 2) ∧
    (IsWeightedLeastSquaresSolution d A b x ↔
      ∀ y : EuclideanSpace ℝ (Fin n),
        ∑ i, d i ^ 2 * (A i ⬝ᵥ WithLp.ofLp x - WithLp.ofLp b i) ^ 2 ≤
          ∑ i, d i ^ 2 * (A i ⬝ᵥ WithLp.ofLp y - WithLp.ofLp b i) ^ 2) := by
  refine ⟨norm_sq_weighted_eq d A b x, ?_⟩
  refine forall_congr' fun y => ?_
  rw [← norm_sq_weighted_eq, ← norm_sq_weighted_eq]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).symm

/-- `D D = diag(dᵢ²)`. -/
private theorem diagonal_mul_diagonal_self (d : Fin m → ℝ) :
    diagonal d * diagonal d = diagonal fun i => d i ^ 2 := by
  rw [diagonal_mul_diagonal]
  simp only [sq]

/-- `(DA)ᵀ = AᵀD` for a real diagonal `D`. -/
private theorem conjTranspose_diagonal_mul (d : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (diagonal d * A)ᴴ = Aᵀ * diagonal d := by
  rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, diagonal_transpose]

/-- `DᵀD = diag(dᵢ²)` for a real diagonal `D`. -/
private theorem conjTranspose_diagonal_mul_self (d : Fin m → ℝ) :
    (diagonal d)ᴴ * diagonal d = diagonal fun i => d i ^ 2 := by
  rw [conjTranspose_eq_transpose_of_trivial, diagonal_transpose, diagonal_mul_diagonal_self]

/-- A diagonal matrix with nonzero diagonal is invertible. -/
private theorem isUnit_diagonal_of_ne_zero {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) :
    IsUnit (diagonal d) :=
  (isUnit_iff_isUnit_det _).2 (by
    rw [det_diagonal]
    exact (prod_ne_zero_iff.2 fun i _ => hd i).isUnit)

/-- A nonzero weight has a positive square. -/
private theorem sq_weight_pos {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (i : Fin m) : 0 < d i ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hd i)))

/-- **(6.1.2).** "If `A` has full column rank and we apply the method of normal equations, then we
are led to the following positive definite system: `(AᵀD²A)x_D = AᵀD²b`": for `d` nowhere zero,
`AᵀD²A` is positive definite, the weighted solutions are the solutions of this system, and the
solution is `x_D = (AᵀD²A)⁻¹AᵀD²b`. -/
theorem equation_6_1_2 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (b : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    (Aᵀ * diagonal (fun i => d i ^ 2) * A).PosDef ∧
    (IsWeightedLeastSquaresSolution d A b x ↔
      toEuclideanLin (Aᵀ * diagonal (fun i => d i ^ 2) * A) x =
        toEuclideanLin (Aᵀ * diagonal (fun i => d i ^ 2)) b) ∧
    (IsWeightedLeastSquaresSolution d A b x ↔
      x = toEuclideanLin (weightedLeastSquaresOp (diagonal fun i => d i ^ 2) A) b) := by
  refine ⟨?_, ?_, ?_⟩
  · have := posDef_conjTranspose_mul_diagonal_mul hA (u := fun i => d i ^ 2)
      (sq_weight_pos hd)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  · rw [IsWeightedLeastSquaresSolution, isLeastSquaresSolution_iff_normalEquations,
      conjTranspose_diagonal_mul, ← toEuclideanLin_mul_apply, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal d), diagonal_mul_diagonal_self, Matrix.mul_assoc,
      ← Matrix.mul_assoc Aᵀ, diagonal_mul_diagonal_self]
  · rw [IsWeightedLeastSquaresSolution,
      isLeastSquaresSolution_weightedLeastSquaresOp (isUnit_diagonal_of_ne_zero hd) hA,
      conjTranspose_diagonal_mul_self]

/-- **(6.1.3).** "Subtracting the unweighted system `AᵀAx_LS = Aᵀb` we see that
`x_D − x_LS = (AᵀD²A)⁻¹Aᵀ(D² − I)(b − Ax_LS)`", for `A` of full column rank and `d` nowhere zero. -/
theorem equation_6_1_3 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) {b : EuclideanSpace ℝ (Fin m)}
    {xD xLS : EuclideanSpace ℝ (Fin n)} (hxD : IsWeightedLeastSquaresSolution d A b xD)
    (hxLS : IsLeastSquaresSolution A b xLS) :
    xD - xLS = toEuclideanLin ((Aᵀ * diagonal (fun i => d i ^ 2) * A)⁻¹ * Aᵀ *
      (diagonal (fun i => d i ^ 2) - 1)) (b - toEuclideanLin A xLS) := by
  obtain ⟨hpd, -, h3⟩ := equation_6_1_2 hA hd b xD
  rw [(isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent hA).1 hxLS, h3.1 hxD]
  have hW : IsUnit (Aᴴ * diagonal (fun i => d i ^ 2) * A) := by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hpd.isUnit
  rw [weightedLeastSquaresOp_mulVec_sub_pinv_mulVec hW b, conjTranspose_eq_transpose_of_trivial]

/-- The book's `D(δ)²` has diagonal `d²` with its `k`-th entry replaced by `d_k²(1 + δ)`; the
residual `r_k(δ) = e_kᵀ(b − Ax(δ))` of the weighted solution `x(δ)`. -/
private theorem update_update_weights (d : Fin m → ℝ) (k : Fin m) (s t : ℝ) :
    Function.update (Function.update (fun i => d i ^ 2) k s) k t =
      Function.update (fun i => d i ^ 2) k t :=
  Function.update_idem _ _ _

/-- The perturbed weights are positive. -/
private theorem update_weights_pos {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (k : Fin m) {t : ℝ}
    (ht : 0 < t) (i : Fin m) : 0 < Function.update (fun i => d i ^ 2) k t i := by
  by_cases hi : i = k
  · rw [hi, Function.update_self]
    exact ht
  · rw [Function.update_of_ne hi]
    exact sq_weight_pos hd i

/-- **(6.1.4).** With `D(δ) = diag(d₁, …, d_k√(1 + δ), …, d_m)`, `δ > −1`, `x(δ)` minimizing
`‖D(δ)(Ax − b)‖₂` and `r_k(δ) = e_kᵀ(b − Ax(δ))`, "it can be shown that
`d/dδ r_k(δ) = −d_k² (a_kᵀ (AᵀD(δ)²A)⁻¹ a_k) r_k(δ)`", for `A` of full column rank and `d` nowhere
zero. The residual is the backbone's `weightedResidual A b w k` at the weights `w = diag(D(δ)²)`. -/
theorem equation_6_1_4 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (b : Fin m → ℝ) (k : Fin m) {δ : ℝ} (hδ : -1 < δ) :
    HasDerivAt
      (fun δ => weightedResidual A b (Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ))) k)
      (-d k ^ 2 * (A k ⬝ᵥ ((Aᵀ * diagonal
          (Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ))) * A)⁻¹ *ᵥ A k)) *
        weightedResidual A b (Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ))) k) δ := by
  have hdk : 0 < d k ^ 2 := sq_weight_pos hd k
  set w := Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ)) with hw
  have hwpos : ∀ i, 0 < w i :=
    update_weights_pos hd k (mul_pos hdk (by linarith))
  have hback := hasDerivAt_weightedResidual hA hwpos b k
  have hwk : w k = d k ^ 2 * (1 + δ) := by rw [hw, Function.update_self]
  rw [hwk] at hback
  have hin : HasDerivAt (fun δ : ℝ => d k ^ 2 * (1 + δ)) (d k ^ 2) δ := by
    simpa using ((hasDerivAt_id δ).const_add 1).const_mul (d k ^ 2)
  have := hback.comp δ hin
  convert this using 1
  · funext δ'
    simp only [Function.comp_apply, hw, update_update_weights]
  · ring

/-- **§6.1.1.** "It follows that `|r_k(δ)|` is a monotone decreasing function of `δ`": for `A` of
full column rank and `d` nowhere zero, `δ ↦ |r_k(δ)|` is antitone on `δ > −1`. The book's
derivation claims `d/dδ [r_k(δ)²] < 0`, which fails when `a_k = 0` or `r_k(δ) = 0`; the non-strict
statement is the theorem. -/
theorem abs_weightedResidual_antitoneOn {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) (b : Fin m → ℝ)
    (k : Fin m) :
    AntitoneOn
      (fun δ => |weightedResidual A b
        (Function.update (fun i => d i ^ 2) k (d k ^ 2 * (1 + δ))) k|) (Set.Ioi (-1)) := by
  have hdk : 0 < d k ^ 2 := sq_weight_pos hd k
  have hw : ∀ i, 0 < (fun i => d i ^ 2) i := sq_weight_pos hd
  have hback := antitoneOn_abs_weightedResidual hA hw b k
  intro δ₁ h₁ δ₂ h₂ h12
  simp only [Set.mem_Ioi] at h₁ h₂
  refine hback (Set.mem_Ioi.2 (mul_pos hdk (by linarith)))
    (Set.mem_Ioi.2 (mul_pos hdk (by linarith))) ?_
  exact mul_le_mul_of_nonneg_left (by linarith) hdk.le

/-- **(6.1.5).** "If `[D⁻² A; Aᵀ 0][r; x] = [b; 0]` then `x` minimizes (6.1.1)", for `d` nowhere
zero. -/
theorem equation_6_1_5 {d : Fin m → ℝ} (hd : ∀ i, d i ≠ 0) {A : Matrix (Fin m) (Fin n) ℝ}
    {b r : EuclideanSpace ℝ (Fin m)} {x : EuclideanSpace ℝ (Fin n)}
    (h1 : toEuclideanLin (diagonal fun i => d i ^ 2)⁻¹ r + toEuclideanLin A x = b)
    (h2 : toEuclideanLin Aᵀ r = 0) : IsWeightedLeastSquaresSolution d A b x := by
  refine isLeastSquaresSolution_of_augmented (r := r) (isUnit_diagonal_of_ne_zero hd) ?_ ?_
  · rwa [conjTranspose_diagonal_mul_self]
  · rwa [conjTranspose_eq_transpose_of_trivial]

/-! ### §6.1.2 Generalized least squares -/

/-- **(6.1.7)–(6.1.8).** For `B` nonsingular (`W = BBᵀ`), "(6.1.7) is equivalent to the generalized
least squares problem `min_{b = Ax + Bv} vᵀv`": `x` minimizes `‖B⁻¹(Ax − b)‖₂` iff
`(x, B⁻¹(b − Ax))` solves (6.1.8). -/
theorem equation_6_1_8 {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : IsUnit B) {b : EuclideanSpace ℝ (Fin m)} {x : EuclideanSpace ℝ (Fin n)} :
    IsLeastSquaresSolution (B⁻¹ * A) (toEuclideanLin B⁻¹ b) x ↔
      IsGeneralizedLeastSquaresSolution A B b x (toEuclideanLin B⁻¹ (b - toEuclideanLin A x)) := by
  rw [isGeneralizedLeastSquaresSolution_iff hB]
  exact ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩

/-- **(6.1.9)–(6.1.10), Paige's method.** For `A ∈ ℝ^{(n+q)×n}` with QR factorization
`QᵀA = [R₁; 0]`, `Q = [Q₁ Q₂]`, and an orthogonal `Z = [Z₁ Z₂]` with `(Q₂ᵀB)Z = [0 S]`: "The bottom
half of this equation determines `v` while the top half prescribes `x`: `Su = Q₂ᵀb`, `v = Z₂u`,
`R₁x = Q₁ᵀb − Q₁ᵀBZ₂u`", and `(x, v)` solves the generalized problem (6.1.8). The book assumes `A`
of full column rank and `B` nonsingular, so that `S` (upper triangular) and `R₁` are nonsingular;
the statement needs only that `S` is. -/
theorem equation_6_1_9 {q : ℕ} {A : Matrix (Fin (n + q)) (Fin n) ℝ}
    {Q : Matrix (Fin (n + q)) (Fin (n + q)) ℝ} {R : Matrix (Fin (n + q)) (Fin n) ℝ}
    (hQR : IsQR A Q R) {B Z : Matrix (Fin (n + q)) (Fin (n + q)) ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin (n + q)) ℝ) {S : Matrix (Fin q) (Fin q) ℝ} (hS : IsUnit S)
    (hZ₁ : (Q.submatrix id (Fin.natAdd n))ᵀ * B * Z.submatrix id (Fin.castAdd q) = 0)
    (hZ₂ : (Q.submatrix id (Fin.natAdd n))ᵀ * B * Z.submatrix id (Fin.natAdd n) = S)
    {b : EuclideanSpace ℝ (Fin (n + q))} {u : EuclideanSpace ℝ (Fin q)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hu : toEuclideanLin S u = toEuclideanLin (Q.submatrix id (Fin.natAdd n))ᵀ b)
    (hx : toEuclideanLin (firstRows R (Nat.le_add_right n q)) x =
      toEuclideanLin (firstColumns Q (Nat.le_add_right n q))ᵀ b -
        toEuclideanLin ((firstColumns Q (Nat.le_add_right n q))ᵀ * B *
          Z.submatrix id (Fin.natAdd n)) u) :
    IsGeneralizedLeastSquaresSolution A B b x
      (toEuclideanLin (Z.submatrix id (Fin.natAdd n)) u) := by
  simp only [← conjTranspose_eq_transpose_of_trivial] at hZ₁ hZ₂ hu hx
  exact isGeneralizedLeastSquaresSolution_of_paige hQR hZ hS hZ₁ hZ₂ hu hx

/-- **(6.1.10), the simplification.** "`R₁x = Q₁ᵀb − (Q₁ᵀBZ₁Z₁ᵀ + Q₁ᵀBZ₂Z₂ᵀ)v = Q₁ᵀb − Q₁ᵀBZ₂u`"
for `v = Z₂u` and `Z = [Z₁ Z₂]` orthogonal; here `C` stands for `Q₁ᵀB` and `c` for `Q₁ᵀb`. -/
theorem equation_6_1_10 {k q : ℕ} {Z : Matrix (Fin (n + q)) (Fin (n + q)) ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin (n + q)) ℝ) (C : Matrix (Fin k) (Fin (n + q)) ℝ)
    (c : Fin k → ℝ) (u : Fin q → ℝ) :
    c - (C * Z.submatrix id (Fin.castAdd q) * (Z.submatrix id (Fin.castAdd q))ᵀ +
        C * Z.submatrix id (Fin.natAdd n) * (Z.submatrix id (Fin.natAdd n))ᵀ) *ᵥ
          (Z.submatrix id (Fin.natAdd n) *ᵥ u) =
      c - (C * Z.submatrix id (Fin.natAdd n)) *ᵥ u := by
  have hZZ : Z.submatrix id (Fin.castAdd q) * (Z.submatrix id (Fin.castAdd q))ᵀ +
      Z.submatrix id (Fin.natAdd n) * (Z.submatrix id (Fin.natAdd n))ᵀ = 1 := by
    have h1 : Z * Zᵀ = 1 := by
      have := mem_unitaryGroup_iff.1 hZ
      rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
    rw [← h1]
    ext i j
    simp only [Matrix.add_apply, mul_apply, submatrix_apply, transpose_apply, id,
      Fin.sum_univ_add]
  rw [Matrix.mul_assoc, Matrix.mul_assoc C, ← Matrix.mul_add, hZZ, Matrix.mul_one, mulVec_mulVec]

/-! ### §6.1.3 Column weighting -/

/-- **§6.1.3.** "If … we compute the minimum 2-norm solution `y_LS` to `min ‖(AG⁻¹)y − b‖₂`, then
`x_G = G⁻¹y_LS` is a minimizer of `‖Ax − b‖₂`", for `G` nonsingular (for any least-squares
solution `y` in fact). -/
theorem isLeastSquaresSolution_columnWeighting {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : IsUnit G) {b : EuclideanSpace ℝ (Fin m)}
    {y : EuclideanSpace ℝ (Fin n)} (hy : IsLeastSquaresSolution (A * G⁻¹) b y) :
    IsLeastSquaresSolution A b (toEuclideanLin G⁻¹ y) :=
  (isLeastSquaresSolution_mul_inv_iff hG).1 hy

/-- **§6.1.3.** "If `rank(A) < n`, then within the set of minimizers, `x_G` has the smallest
`G`-norm", `‖z‖_G = ‖Gz‖₂`: for `y_LS` the minimum-norm solution of `min ‖(AG⁻¹)y − b‖₂` and every
minimizer `x` of `‖Ax − b‖₂`, `‖G⁻¹y_LS‖_G ≤ ‖x‖_G`. It holds for every rank. -/
theorem norm_columnWeighting_le {A : Matrix (Fin m) (Fin n) ℝ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : IsUnit G) {b : EuclideanSpace ℝ (Fin m)} {y x : EuclideanSpace ℝ (Fin n)}
    (hy : IsMinNormLeastSquaresSolution (A * G⁻¹) b y) (hx : IsLeastSquaresSolution A b x) :
    ‖toEuclideanLin G (toEuclideanLin G⁻¹ y)‖ ≤ ‖toEuclideanLin G x‖ := by
  rw [toEuclideanLin_mul_nonsing_inv_apply hG]
  exact hy.norm_le_of_mul_inv hG hx

/-! ### §6.1.4 Ridge regression -/

/-- `‖√μ x‖² = μ ‖x‖²` for `μ ≥ 0`, the regularization term of a stacked problem. -/
private theorem norm_sqrt_smul_sub_zero_sq {k : ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (M : Matrix (Fin k) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖toEuclideanLin (Real.sqrt μ • M) x - WithLp.toLp 2 0‖ ^ 2 =
      μ * ‖toEuclideanLin M x‖ ^ 2 := by
  rw [WithLp.toLp_zero, sub_zero, toEuclideanLin_smul_apply, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt hμ]

/-- **(6.1.11).** "`min ‖[A; √λ I]x − [b; 0]‖₂² = min ‖Ax − b‖₂² + λ‖x‖₂²`": for `λ ≥ 0` the two
objectives agree, so the ridge problem is the least-squares problem of the stacked matrix. -/
theorem equation_6_1_11 (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) {μ : ℝ}
    (hμ : 0 ≤ μ) (x : EuclideanSpace ℝ (Fin n)) :
    (‖toEuclideanLin (fromRows A (Real.sqrt μ • (1 : Matrix (Fin n) (Fin n) ℝ))) x -
        WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) 0)‖ ^ 2 =
      ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖x‖ ^ 2) ∧
    (IsLeastSquaresSolution (fromRows A (Real.sqrt μ • (1 : Matrix (Fin n) (Fin n) ℝ)))
        (WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) 0)) x ↔
      ∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖y‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · rw [norm_fromRows_sub_sq, WithLp.toLp_ofLp, norm_sqrt_smul_sub_zero_sq hμ,
      toEuclideanLin_one_apply]
  · have h := isLeastSquaresSolution_fromRows_iff A (1 : Matrix (Fin n) (Fin n) ℝ)
      (WithLp.ofLp b) 0 hμ x
    simp only [smul_zero, WithLp.toLp_ofLp, toEuclideanLin_one_apply, WithLp.toLp_zero,
      sub_zero, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h

/-- **(6.1.12).** "The normal equation system for this problem is given by `(AᵀA + λI)x = Aᵀb`":
for `λ > 0`, `x` minimizes `‖Ax − b‖₂² + λ‖x‖₂²` iff it solves the normal equations, iff it is the
ridge solution `x(λ) = (AᵀA + λI)⁻¹Aᵀb`, the backbone's `A.tikhonov λ` applied to `b`. -/
theorem equation_6_1_12 (A : Matrix (Fin m) (Fin n) ℝ) {μ : ℝ} (hμ : 0 < μ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    ((∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖y‖ ^ 2) ↔
      toEuclideanLin (Aᵀ * A + μ • (1 : Matrix (Fin n) (Fin n) ℝ)) x = toEuclideanLin Aᵀ b) ∧
    ((∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖y‖ ^ 2) ↔
      x = toEuclideanLin (A.tikhonov μ) b) := by
  have h2 := (tikhonov_mulVec_eq_iff_isMinOn A hμ b x).symm
  refine ⟨?_, h2⟩
  rw [h2, ← tikhonov_unique A μ hμ b x]
  have e : toEuclideanLin (Aᵀ * A + μ • (1 : Matrix (Fin n) (Fin n) ℝ)) x =
      μ • x + toEuclideanLin (Aᵀ * A) x := by
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, toEuclideanLin_one,
      LinearMap.id_apply, add_comm]
  rw [e, conjTranspose_eq_transpose_of_trivial]
  rfl

/-- **(6.1.14).** "If `A = UΣVᵀ = ∑ᵢ σᵢuᵢvᵢᵀ` is the SVD of `A`, then (6.1.12) converts to …
`x(λ) = ∑_{i=1}^r (σᵢuᵢᵀb/(σᵢ² + λ)) vᵢ`": for any SVD `Matrix.IsSVD A U σ V` and `λ > 0`. The sum
runs over `i < min(m, n)`; its terms with `σᵢ = 0` (those past the rank `r`) vanish. -/
theorem equation_6_1_14 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {μ : ℝ} (hμ : 0 < μ)
    (b : EuclideanSpace ℝ (Fin m)) :
    toEuclideanLin (A.tikhonov μ) b = ∑ i : Fin (min m n),
      (σ i * inner ℝ (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i))) b / (σ i ^ 2 + μ)) •
        (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)) : EuclideanSpace ℝ (Fin n)) := by
  rw [tikhonov_mulVec_eq_sum_of_isSVD h hμ b]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_smul, RCLike.ofReal_real_eq_id, id_eq, mul_div_right_comm]

/-- **§6.1.4.** "By inspection, it is clear that `lim_{λ→0} x(λ) = x_LS`", `x_LS = A⁺b` the minimum
norm least-squares solution. -/
theorem tendsto_ridge_leastSquares (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun μ => toEuclideanLin (A.tikhonov μ) b) (𝓝[>] 0)
      (𝓝 (toEuclideanLin A.pinv b)) := by
  have hc : Continuous fun M : Matrix (Fin n) (Fin m) ℝ => toEuclideanLin M b := by
    simp only [toEuclideanLin_apply]
    exact (PiLp.continuous_toLp 2 _).comp (continuous_id.matrix_mulVec continuous_const)
  exact (hc.tendsto _).comp (tendsto_tikhonov_pinv A)

/-- **§6.1.4.** "… and `‖x(λ)‖₂` is a monotone decreasing function of `λ`": antitone on `λ > 0`,
strictly decreasing when `Aᵀb ≠ 0`. -/
theorem norm_ridge_antitoneOn (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    AntitoneOn (fun μ => ‖toEuclideanLin (A.tikhonov μ) b‖) (Set.Ioi 0) ∧
      (toEuclideanLin Aᵀ b ≠ 0 →
        StrictAntiOn (fun μ => ‖toEuclideanLin (A.tikhonov μ) b‖) (Set.Ioi 0)) := by
  refine ⟨antitoneOn_norm_tikhonov_mulVec A b, fun hb => ?_⟩
  rw [← conjTranspose_eq_transpose_of_trivial] at hb
  exact strictAntiOn_norm_tikhonov_mulVec A hb

/-- **§6.1.4, (6.1.15).** "Let `x_k(λ)` solve `min ‖D_k(Ax − b)‖₂² + λ‖x‖₂²`", with
`D_k = I − e_ke_kᵀ = diag(1, …, 1, 0, 1, …, 1)` (the `k`-th equation deleted): the ridge solution of
the reduced problem, `x_k(λ) = ((D_kA)ᵀ(D_kA) + λI)⁻¹(D_kA)ᵀ(D_kb)` (`ridgeDeleted_spec`). -/
noncomputable def ridgeDeleted (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (μ : ℝ)
    (k : Fin m) : Fin n → ℝ :=
  (diagonal (Function.update (1 : Fin m → ℝ) k 0) * A).tikhonov μ *ᵥ
    (diagonal (Function.update (1 : Fin m → ℝ) k 0) *ᵥ b)

/-- **(6.1.15).** For `λ > 0`, `x_k(λ)` is the unique solution of
`min ‖D_k(Ax − b)‖₂² + λ‖x‖₂²`. -/
theorem ridgeDeleted_spec (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (k : Fin m) (x : EuclideanSpace ℝ (Fin n)) :
    x = WithLp.toLp 2 (ridgeDeleted A b μ k) ↔
      ∀ y, ‖toEuclideanLin (diagonal (Function.update (1 : Fin m → ℝ) k 0) * A) x -
            WithLp.toLp 2 (diagonal (Function.update (1 : Fin m → ℝ) k 0) *ᵥ b)‖ ^ 2 +
          μ * ‖x‖ ^ 2 ≤
        ‖toEuclideanLin (diagonal (Function.update (1 : Fin m → ℝ) k 0) * A) y -
            WithLp.toLp 2 (diagonal (Function.update (1 : Fin m → ℝ) k 0) *ᵥ b)‖ ^ 2 +
          μ * ‖y‖ ^ 2 :=
  tikhonov_mulVec_eq_iff_isMinOn (diagonal (Function.update (1 : Fin m → ℝ) k 0) * A) hμ
    (WithLp.toLp 2 (diagonal (Function.update (1 : Fin m → ℝ) k 0) *ᵥ b)) x

/-- **(6.1.16).** "Assuming that `λ > 0`, an algebraic manipulation shows that
`x_k(λ) = x(λ) + ((a_kᵀx(λ) − b_k)/(1 − z_kᵀa_k)) z_k` where `z_k = (AᵀA + λI)⁻¹a_k` and
`x(λ) = (AᵀA + λI)⁻¹Aᵀb`"; the denominator is positive. -/
theorem equation_6_1_16 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (k : Fin m) :
    ridgeDeleted A b μ k = A.tikhonov μ *ᵥ b +
        ((A k ⬝ᵥ (A.tikhonov μ *ᵥ b) - b k) /
          (1 - ((Aᵀ * A + μ • 1)⁻¹ *ᵥ A k) ⬝ᵥ A k)) • ((Aᵀ * A + μ • 1)⁻¹ *ᵥ A k) ∧
      0 < 1 - ((Aᵀ * A + μ • 1)⁻¹ *ᵥ A k) ⬝ᵥ A k := by
  refine ⟨tikhonov_deleteRow_eq A b hμ k, ?_⟩
  rw [dotProduct_comm]
  exact one_sub_dotProduct_inv_gram_pos A hμ k

/-- **(6.1.17).** "`r_k = b_k − a_kᵀx_k(λ) =
e_kᵀ(I − A(AᵀA + λI)⁻¹Aᵀ)b / e_kᵀ(I − A(AᵀA + λI)⁻¹Aᵀ)e_k`",
for `λ > 0`; the denominator is positive. -/
theorem equation_6_1_17 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (k : Fin m) :
    b k - A k ⬝ᵥ ridgeDeleted A b μ k =
        ((1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) *ᵥ b) k /
          (1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) k k ∧
      0 < (1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) k k :=
  tikhonov_deleteRow_residual_eq A b hμ k

/-- **§6.1.4, the cross-validation weighted square error.** "Now consider choosing `λ` so as to
minimize the cross-validation weighted square error `C(λ)` defined by
`C(λ) = (1/m) ∑_{k=1}^m w_k (a_kᵀx_k(λ) − b_k)²`. Here, `w₁, …, w_m` are nonnegative weights." -/
noncomputable def crossValidationError (w : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (μ : ℝ) : ℝ :=
  (1 / m : ℝ) * ∑ k, w k * (A k ⬝ᵥ ridgeDeleted A b μ k - b k) ^ 2

/-- The residual `r = (I − H)b` is affine in `b_k` with slope the diagonal entry `(I − H)_{kk}`. -/
private theorem hasDerivAt_mulVec_update (M : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ)
    (k : Fin m) :
    HasDerivAt (fun t => (M *ᵥ Function.update b k t) k) (M k k) (b k) := by
  have e : (fun t => (M *ᵥ Function.update b k t) k) =
      fun t => (M *ᵥ b) k + M k k * (t - b k) := by
    funext t
    have hu : Function.update b k t = b + Pi.single k (t - b k) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp
      · simp [hj]
    rw [hu, mulVec_add, Pi.add_apply]
    congr 1
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [e]
  simpa using (((hasDerivAt_id (b k)).sub_const (b k)).const_mul (M k k)).const_add ((M *ᵥ b) k)

/-- **(6.1.18).** "Noting that the residual `r = [r₁, …, r_m]ᵀ = b − Ax(λ)` is given by the formula
`r = [I − A(AᵀA + λI)⁻¹Aᵀ]b` we see that `C(λ) = (1/m) ∑_k w_k (r_k / (∂r_k/∂b_k))²`", for `λ > 0`:
`∂r_k/∂b_k` is the diagonal entry `(I − A(AᵀA + λI)⁻¹Aᵀ)_{kk}`. -/
theorem equation_6_1_18 (w : Fin m → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {μ : ℝ}
    (hμ : 0 < μ) :
    (∀ k, HasDerivAt
      (fun t => ((1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) *ᵥ
        Function.update b k t) k)
      ((1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) k k) (b k)) ∧
    crossValidationError w A b μ = (1 / m : ℝ) * ∑ k, w k *
      (((1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) *ᵥ b) k /
        (1 - A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ : Matrix (Fin m) (Fin m) ℝ) k k) ^ 2 := by
  refine ⟨fun k => hasDerivAt_mulVec_update _ b k, ?_⟩
  rw [crossValidationError]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [← neg_sub, neg_sq, (equation_6_1_17 A b hμ k).1]

/-- The ridge hat matrix in an SVD: `A(AᵀA + λI)⁻¹Aᵀ = U diag(cᵢ) Uᵀ` with
`cᵢ = σᵢ²/(σᵢ² + λ)` for `i < n` and `0` beyond. -/
private theorem hat_eq_of_isSVD {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {μ : ℝ} (hμ : 0 < μ) :
    A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ = U * diagonal (fun i : Fin m =>
      if (i : ℕ) < n then σ i * (σ i / (σ i ^ 2 + μ)) else 0) * Uᵀ := by
  have hV : star V * V = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
  have hT : A * (Aᵀ * A + μ • 1)⁻¹ * Aᵀ = A * A.tikhonov μ := by
    rw [tikhonov_eq_real, Matrix.mul_assoc]
  rw [hT, h.tikhonov_eq hμ]
  conv_lhs => rw [h.eq_mul_mul_star]
  have e : U * (rectDiagonal fun i => ((σ i : ℝ) : ℝ) : Matrix (Fin m) (Fin n) ℝ) * star V *
      (V * (rectDiagonal fun i => ((σ i / (σ i ^ 2 + μ) : ℝ) : ℝ) :
        Matrix (Fin n) (Fin m) ℝ) * star U) =
      U * ((rectDiagonal fun i => ((σ i : ℝ) : ℝ) : Matrix (Fin m) (Fin n) ℝ) *
        (rectDiagonal fun i => ((σ i / (σ i ^ 2 + μ) : ℝ) : ℝ) : Matrix (Fin n) (Fin m) ℝ)) *
        star U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star V), hV, Matrix.one_mul]
  simp only [RCLike.ofReal_real_eq_id, id_eq] at e ⊢
  rw [e, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

/-- **(6.1.19).** "Using the SVD (6.1.13) and Equations (6.1.17) and (6.1.18), it can be shown
that `C(λ) = (1/m) ∑_k w_k [(b_k − ∑_{j=1}^r u_{kj} b̃_j (σ_j²/(σ_j² + λ))) /
(1 − ∑_{j=1}^r u_{kj}² (σ_j²/(σ_j² + λ)))]²` where `b̃ = Uᵀb`", for any SVD `Matrix.IsSVD A U σ V`
and `λ > 0`. The sums run over `j < min(m, n)` (the terms past the rank vanish). The book prints
`b̃_k` in the numerator; the correct entry is `b_k` (as `λ → ∞` the numerator must tend to
`b_k`). -/
theorem equation_6_1_19 (w : Fin m → ℝ) {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V)
    (b : Fin m → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    crossValidationError w A b μ = (1 / m : ℝ) * ∑ k, w k *
      ((b k - ∑ j : Fin (min m n), U k (Fin.castLE (min_le_left m n) j) *
          (Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) j) * (σ j ^ 2 / (σ j ^ 2 + μ))) /
        (1 - ∑ j : Fin (min m n), U k (Fin.castLE (min_le_left m n) j) ^ 2 *
          (σ j ^ 2 / (σ j ^ 2 + μ)))) ^ 2 := by
  rw [(equation_6_1_18 w A b hμ).2, hat_eq_of_isSVD h hμ]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  congr 3
  · rw [sub_mulVec, one_mulVec, Pi.sub_apply, ← mulVec_mulVec, ← mulVec_mulVec]
    congr 1
    have e := Fin.sum_castLE_eq_sum_ite (min_le_left m n) fun i : Fin m =>
      U k i * (Uᵀ *ᵥ b) i * (σ i ^ 2 / (σ i ^ 2 + μ))
    simp only [Fin.val_castLE] at e
    rw [e]
    change ∑ i, U k i * (diagonal _ *ᵥ (Uᵀ *ᵥ b)) i = _
    refine sum_congr rfl fun i _ => ?_
    rw [mulVec_diagonal]
    have hi := i.isLt
    by_cases hin : (i : ℕ) < n
    · rw [ite_eq_left (lt_min hi hin), ite_eq_left hin]
      ring
    · rw [ite_eq_right (fun h' => hin (lt_of_lt_of_le h' (min_le_right m n))), ite_eq_right hin]
      ring
  · rw [Matrix.sub_apply, one_apply_eq]
    congr 1
    have e := Fin.sum_castLE_eq_sum_ite (min_le_left m n) fun i : Fin m =>
      U k i ^ 2 * (σ i ^ 2 / (σ i ^ 2 + μ))
    simp only [Fin.val_castLE] at e
    rw [e, mul_apply]
    refine sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    rw [mul_apply, sum_eq_single i, diagonal_apply_eq, transpose_apply]
    · by_cases hin : (i : ℕ) < n
      · rw [ite_eq_left (lt_min hi hin), ite_eq_left hin]
        ring
      · rw [ite_eq_right (fun h' => hin (lt_of_lt_of_le h' (min_le_right m n))),
          ite_eq_right hin]
        ring
    · intro j _ hj
      rw [diagonal_apply_ne _ hj, mul_zero]
    · intro h'
      exact absurd (mem_univ _) h'

/-! ### §6.1.5 Tikhonov regularization -/

/-- **(6.1.20).** "`min ‖[A; √λ B]x − [b; 0]‖₂² = min ‖Ax − b‖₂² + λ‖Bx‖₂²`": for `λ ≥ 0` and
`B ∈ ℝ^{n×n}` the two objectives agree, so the Tikhonov problem is the least-squares problem of the
stacked matrix. -/
theorem equation_6_1_20 (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) {μ : ℝ} (hμ : 0 ≤ μ) (x : EuclideanSpace ℝ (Fin n)) :
    (‖toEuclideanLin (fromRows A (Real.sqrt μ • B)) x -
        WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) 0)‖ ^ 2 =
      ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x‖ ^ 2) ∧
    (IsLeastSquaresSolution (fromRows A (Real.sqrt μ • B))
        (WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) 0)) x ↔
      ∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖toEuclideanLin B y‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · rw [norm_fromRows_sub_sq, WithLp.toLp_ofLp, norm_sqrt_smul_sub_zero_sq hμ]
  · have h := isLeastSquaresSolution_fromRows_iff A B (WithLp.ofLp b) 0 hμ x
    simp only [smul_zero, WithLp.toLp_ofLp, WithLp.toLp_zero, sub_zero,
      RCLike.ofReal_real_eq_id, id_eq] at h
    exact h

/-- **(6.1.21).** "The normal equations for this problem have the form `(AᵀA + λBᵀB)x = Aᵀb`. This
system is nonsingular if `null(A) ∩ null(B) = {0}`": for `λ > 0`, `AᵀA + λBᵀB` is positive definite
iff (so in particular nonsingular if) the null spaces meet trivially, and then the minimizers of
(6.1.20) are exactly the solutions of the normal equations. -/
theorem equation_6_1_21 (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) {μ : ℝ}
    (hμ : 0 < μ) :
    ((Aᵀ * A + μ • (Bᵀ * B)).PosDef ↔
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) ∧
    (LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ →
      ∀ (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)),
        (∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x‖ ^ 2 ≤
            ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖toEuclideanLin B y‖ ^ 2) ↔
          toEuclideanLin (Aᵀ * A + μ • (Bᵀ * B)) x = toEuclideanLin Aᵀ b) := by
  refine ⟨?_, fun hAB b x => ?_⟩
  · have h := posDef_gram_add_smul_gram_iff A B hμ
    simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h
  · have h := generalFormTikhonov_mulVec_eq_iff_isMinOn A B hμ hAB b x
    simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h.2.symm.trans h.1

/-! ### §6.1.6 The generalized singular value decomposition -/

/-- **Theorem 6.1.1 (Generalized Singular Value Decomposition).** "Assume that `A ∈ ℝ^{m₁×n₁}` and
`B ∈ ℝ^{m₂×n₁}` with `m₁ ≥ n₁` and `r = rank([A; B])`. There exist orthogonal `U₁ ∈ ℝ^{m₁×m₁}` and
`U₂ ∈ ℝ^{m₂×m₂}` and invertible `X ∈ ℝ^{n₁×n₁}` such that `U₁ᵀAX = D_A` (6.1.22),
`U₂ᵀBX = D_B` (6.1.23), where `p = max{r − m₂, 0}`": `D_A = rectDiagonal α` with `α_i = 1` for
`i < p` and `α_i = 0` for `i ≥ r` (the blocks `I`, `diag(α_{p+1}, …, α_r)`, `0`), and
`D_B = shiftedRectDiagonal p β` with `β_i = 0` for `i < p` and `i ≥ r` (row `i` of `D_B` carries
`β_{i+p}` in column `i + p`: the blocks `0`, `diag(β_{p+1}, …, β_r)`, `0`). The printed row labels
of `D_B` (`p, r − p, m₂ − r`) are a conversion error for `r − p, m₂ − r + p`. -/
theorem theorem_6_1_1 {m₁ m₂ n₁ : ℕ} (hmn : n₁ ≤ m₁) (A : Matrix (Fin m₁) (Fin n₁) ℝ)
    (B : Matrix (Fin m₂) (Fin n₁) ℝ) :
    ∃ (U₁ : Matrix (Fin m₁) (Fin m₁) ℝ) (U₂ : Matrix (Fin m₂) (Fin m₂) ℝ)
      (X : Matrix (Fin n₁) (Fin n₁) ℝ) (α β : ℕ → ℝ),
      U₁ ∈ orthogonalGroup (Fin m₁) ℝ ∧ U₂ ∈ orthogonalGroup (Fin m₂) ℝ ∧ IsUnit X ∧
      U₁ᵀ * A * X = rectDiagonal α ∧
      U₂ᵀ * B * X = shiftedRectDiagonal ((fromRows A B).rank - m₂) β ∧
      (∀ i < (fromRows A B).rank - m₂, α i = 1 ∧ β i = 0) ∧
      ∀ i, (fromRows A B).rank ≤ i → α i = 0 ∧ β i = 0 := by
  obtain ⟨U₁, U₂, X, α, β, h⟩ := exists_isGSVD hmn A B
  refine ⟨U₁, U₂, X, α, β, h.mem_unitaryGroup_left, h.mem_unitaryGroup_right, h.isUnit, ?_, ?_,
    h.of_lt_p, h.of_le_r⟩
  · have e := h.star_mul_mul_left
    simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, id_eq] at e
    exact e
  · have e := h.star_mul_mul_right
    simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, id_eq] at e
    exact e

/-- **Theorem 6.1.1, the unprinted clause.** The decomposition can be chosen with
`α_i² + β_i² = 1` and `α_i, β_i ≥ 0` for `p < i ≤ r` (the cosine–sine pairs of the proof's CS
decomposition (6.1.25)): the whole specification `Matrix.IsGSVD`. -/
theorem theorem_6_1_1_b {m₁ m₂ n₁ : ℕ} (hmn : n₁ ≤ m₁) (A : Matrix (Fin m₁) (Fin n₁) ℝ)
    (B : Matrix (Fin m₂) (Fin n₁) ℝ) : ∃ U₁ U₂ X α β, IsGSVD A B U₁ U₂ X α β :=
  exists_isGSVD hmn A B

/-- **§6.1.6.** "Note that if `B = I_{n₁}` and we set `X = U₂`, then we obtain the SVD of `A`": for
a GSVD of `(A, I)`, every `β_i` (`i < n₁`) is positive and `U₁ᵀAU₂ = diag(α_i/β_i)`. (The book's
"set `X = U₂`" is loose: `X = U₂D_B`.) -/
theorem gsvd_one {m₁ n₁ : ℕ} {A : Matrix (Fin m₁) (Fin n₁) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ X : Matrix (Fin n₁) (Fin n₁) ℝ} {α β : ℕ → ℝ} (h : IsGSVD A 1 U₁ U₂ X α β) :
    (∀ i < n₁, 0 < β i) ∧ U₁ᵀ * A * U₂ = rectDiagonal fun i => α i / β i := by
  obtain ⟨-, -, hβ, e⟩ := h.svd_of_eq_one
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, id_eq] at e
  exact ⟨hβ, e⟩

/-- **§6.1.6.** "The GSVD is related to the generalized eigenvalue problem `AᵀAx = μ²BᵀBx`": for
`m₁ ≥ n₁` and every column `x_i` of `X`, `β_i² AᵀA x_i = α_i² BᵀB x_i`, so `x_i` is a generalized
eigenvector with `μ_i = α_i/β_i` when `β_i ≠ 0`. -/
theorem gsvd_generalizedEigen {m₁ m₂ n₁ : ℕ} {A : Matrix (Fin m₁) (Fin n₁) ℝ}
    {B : Matrix (Fin m₂) (Fin n₁) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ} {X : Matrix (Fin n₁) (Fin n₁) ℝ} {α β : ℕ → ℝ}
    (h : IsGSVD A B U₁ U₂ X α β) (hmn : n₁ ≤ m₁) (i : Fin n₁) :
    β i ^ 2 • ((Aᵀ * A) *ᵥ X.col i) = α i ^ 2 • ((Bᵀ * B) *ᵥ X.col i) ∧
      (β i ≠ 0 → (Aᵀ * A) *ᵥ X.col i = (α i / β i) ^ 2 • ((Bᵀ * B) *ᵥ X.col i)) := by
  have e := h.gram_mulVec_col hmn i
  simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at e
  refine ⟨e, fun hβ => ?_⟩
  have hβ2 : β i ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  rw [div_pow, div_eq_inv_mul, mul_smul, ← e, smul_smul, inv_mul_cancel₀ hβ2, one_smul]

/-- **(6.1.26)** and the display before it. "If `B` is square and nonsingular, then the GSVD …
transforms the system (6.1.21) to `(D_AᵀD_A + λD_BᵀD_B)y = D_Aᵀb̃` where `x = Xy`, `b̃ = U₁ᵀb`, and
`D_AᵀD_A + λD_BᵀD_B = diag(α₁² + λβ₁², …, α_n² + λβ_n²)`. Thus … `x(λ) = ∑_{k=1}^n
(α_k b̃_k/(α_k² + λβ_k²)) x_k` solves (6.1.20)", for `m ≥ n` and `λ > 0`
(`Xᵀ(AᵀA + λBᵀB)X = D_AᵀD_A + λD_BᵀD_B`). -/
theorem equation_6_1_26 {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsUnit B) {U₁ : Matrix (Fin m) (Fin m) ℝ} {U₂ X : Matrix (Fin n) (Fin n) ℝ}
    {α β : ℕ → ℝ} (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m) {μ : ℝ} (hμ : 0 < μ)
    (b : EuclideanSpace ℝ (Fin m)) :
    Xᵀ * (Aᵀ * A + μ • (Bᵀ * B)) * X = diagonal (fun i : Fin n => α i ^ 2 + μ * β i ^ 2) ∧
    ∀ x : EuclideanSpace ℝ (Fin n),
      x = WithLp.toLp 2 (∑ k : Fin n, (α k / (α k ^ 2 + μ * β k ^ 2) *
        (U₁ᵀ *ᵥ WithLp.ofLp b) (Fin.castLE hnm k)) • X.col k) →
      ∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖toEuclideanLin B y‖ ^ 2 := by
  refine ⟨?_, fun x hx => ?_⟩
  · have e := h.conjTranspose_mul_gram_add_smul_gram_mul hnm μ
    simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at e
    exact e
  · have hker : LinearMap.ker B.mulVecLin = ⊥ :=
      LinearMap.ker_eq_bot.2 (mulVec_injective_iff_isUnit.2 hB)
    have hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ := by
      rw [hker, inf_bot_eq]
    refine (generalFormTikhonov_mulVec_eq_iff_isMinOn A B hμ hAB b x).2.1 ?_
    have e := generalFormTikhonov_mulVec_eq_sum_of_isGSVD hB h hnm hμ (WithLp.ofLp b)
    simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, id_eq] at e
    rw [hx, toEuclideanLin_apply, e]

end GolubVanLoan.Chapter06
