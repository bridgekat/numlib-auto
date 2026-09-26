import Mathlib.LinearAlgebra.CrossProduct
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted
import NumlibSurface.GolubVanLoan.Chapter05.Section02

/-!
# Golub–Van Loan §5.3: the full-rank least-squares problem

Surface file for [golub2013matrix] §5.3: the normal equations and the gradient (§5.3.1), the SVD
expansion (5.3.2)–(5.3.3), the QR solution (5.3.5), the augmented system and its QR solution
(§5.3.8, (5.3.20)), and the cross-product nearness problems of §5.3.9 ((5.3.21)–(5.3.29)).

## Conventions

Least-squares statements are on `EuclideanSpace ℝ (Fin m)` (the backbone's
`Matrix.IsLeastSquaresSolution A b x`: `x` minimizes `‖A x - b‖₂`), vectors of algorithms are
`Fin m → ℝ` and are converted with `WithLp.toLp 2`. The book's `u_i`, `v_i` are the columns of
the SVD factors (`Matrix.IsSVD A U σ V`), `u_iᵀ b` is `U.col i ⬝ᵥ b`. Indices are 0-based. The
cross-product matrix of `v ∈ ℝ³` is `crossMatrix v` (Mathlib has the cross product `⨯₃` but no
matrix form).

## Book slips carried

(5.3.3)'s upper summation limit is printed `2` (read `m`); (5.3.26)–(5.3.29) need non-parallel
lines (`r ≠ 0`) and non-collinear points (`v ≠ 0`), which the book omits.

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
