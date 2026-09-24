import Numlib.FloatingPoint.LU
import Numlib.LinearAlgebra.Matrix.Products
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Rounding errors of Householder transformations

The backward error analysis of computations with Householder reflectors, in the relational
rounding model of `Numlib/FloatingPoint/Model` and in the style of
`Numlib/FloatingPoint/Substitution`: [higham2002accuracy] §19.3 (Lemmas 19.1–19.3), which is the
model that the stability statements of [quarteroni2000numerical] §5.6 ((5.46), the Householder
reduction to Hessenberg form), §5.8.3 and §5.9.2 rest on.

The algorithms are described by *what is rounded*, for an explicit order of the operations, and
every statement quantifies over all admissible roundings at once:

* `FloatingPoint.RoundsHouseholderVector m x i v̂ β̂` is [higham2002accuracy] Lemma 19.1's
  construction (19.1) of the reflector data `(v, β)` with `P = I - β v vᵀ`, `v = x + s e_i`,
  `s = sign(x_i) ‖x‖₂`, `β = 1/(s v_i)`: the norm is `fl(√(fl(xᵀx)))`, the pivot entry
  `fl(x_i + s)`, and `β̂ = fl(1 / fl(ŝ v̂_i))`. Lemma 19.1 (`RoundsHouseholderVector.isRelPert`)
  says that `β̂ = β (1 + θ)` with `|θ| ≤ γ_{4n+8}`, `v̂_i = v_i (1 + θ')` with `|θ'| ≤ γ_{n+2}`,
  and `v̂_j = v_j = x_j` for `j ≠ i` — Higham's constants exactly. The exact `(v, β)` is the
  backbone's `Matrix.householderAxis x i` and `2 / (v ⬝ᵥ v)`, whose reflector is
  `Matrix.householder (Matrix.householderVec x i)` (`householder_householderVec_eq`).
* `FloatingPoint.RoundsHouseholderApply m β v b y` is the update `y = b - v (β (vᵀ b))` of
  [quarteroni2000numerical] (5.49)–(5.50) with one rounding per operation (the inner product as
  `RoundsDot`). Lemma 19.2 (`norm_sub_le_of_roundsHouseholderApply`): if the data `(β̂, v̂)` used
  are relative perturbations of order `k` of exact data `(β, v)` with `|β| ‖v‖₂² ≤ 2` (a
  reflector, or the degenerate `(0, 0)`), then `‖ŷ - P b‖₂ ≤ 3 γ_{3k+n+3} ‖b‖₂` for the exact
  `P = I - β v vᵀ`; with Lemma 19.1's `k = 4n + 8` this is Higham's `γ̃_n`, here
  `3 γ_{13n+27}`.
* Lemma 19.3, in three forms and with no reference to reflectors at all: a sequence of vectors
  with `‖x_{k+1} - P_k x_k‖₂ ≤ ε ‖x_k‖₂` for orthogonal `P_k` satisfies
  `x_r = P_{r-1} ⋯ P_0 (x_0 + Δx)` with `‖Δx‖₂ ≤ ((1 + ε)^r - 1) ‖x_0‖₂ ≤ γ_r(ε) ‖x_0‖₂`
  (`exists_eq_prodRev_mulVec_add`, `exists_eq_prodRev_mulVec_add_gamma`); the columnwise
  matrix form `exists_eq_prodRev_mul_add`; and the two-sided Frobenius form
  `exists_eq_prodRev_mul_add_mul_prodFwd` for `A_{k+1} ≈ L_k A_k R_k`, which is the analogue
  Higham's §19.10 attributes to Ortega and Wilkinson, with its reflector (symmetric) specialization
  `exists_eq_transpose_mul_add_mul_prodFwd`. The products are `Matrix.prodRev P r =
  P_{r-1} ⋯ P_0` and `Matrix.prodFwd P r = P_0 ⋯ P_{r-1}` of
  `Numlib/LinearAlgebra/Matrix/Products`.
* The Householder reduction to Hessenberg form in floating-point arithmetic,
  `FloatingPoint.RoundsHessenbergStep` and `FloatingPoint.RoundsHessenbergReduce`
  ([quarteroni2000numerical] §5.6.2, Program 29, as [higham2002accuracy] Theorem 19.4 models
  such an algorithm): at step `k` the reflector data are computed from the tail of column `k` of
  the current matrix, the columns `j ≥ k` are updated by `RoundsHouseholderApply`, the entries of
  column `k` below the first subdiagonal are **set to zero explicitly** (Higham's convention for
  the annihilated entries, which every implementation storing the reflector in place follows;
  Program 29 leaves them as roundoff-sized junk), the columns `j < k` — already zero below the
  first subdiagonal — are left alone, and then the rows are updated by `RoundsHouseholderApply`,
  the entries in columns `≤ k`, which the reflector fixes exactly, being left alone. The
  reflector `P_k` of the analysis is the *exact* reflector of the *computed* matrix's column,
  `Matrix.hessenbergReflector (Â_k) k`. The theorem `exists_roundsHessenbergReduce_eq` is
  (5.46) with the constants explicit: `Ĥ = Qᵀ (A + E) Q` with `Q = P_0 ⋯ P_{n-3}` orthogonal and
  `‖E‖_F ≤ γ_{2(n-2)}(3 γ_{13n+27}) ‖A‖_F`, which is `c n² u ‖A‖_F` for `u` small.
* The two-sided triangular solve `Ĉ = fl(H⁻ᵀ A H⁻¹)` of the QR–Cholesky algorithm
  ([quarteroni2000numerical] §5.9.2, step 2), `FloatingPoint.RoundsTwoSidedSolve`: the
  columnwise and rowwise forms of [higham2002accuracy] Theorem 8.5 with a matrix right-hand side
  (`frobenius_norm_sub_le_of_forall_roundsForwardSubst_col`, `…_row`) and the forward bound
  `‖Ĉ - H⁻ᵀ A H⁻¹‖_F ≤ (2θ/(1 - θ)²) ‖H⁻¹‖_F² ‖A‖_F`, `θ = γ_n ‖H⁻¹‖_F ‖H‖_F`
  (`frobenius_norm_sub_le_of_roundsTwoSidedSolve`) — the book's `u ‖A‖₂ ‖B⁻¹‖₂` carries the
  condition number of the Cholesky factor as well. The rounding model of Givens rotations
  ([higham2002accuracy] §19.6) is `Numlib/FloatingPoint/Givens`.

**The [golub2013matrix] variants.** The Householder vector of [golub2013matrix] Algorithm 5.1.1
(Parlett's formula for `v₁` when `x₁ > 0`, the normalization `v₁ = 1`, and `P x = +‖x‖ e₁`) is a
different computation from Higham's (19.1) and gets its own relation
`FloatingPoint.RoundsHouseholderVectorParlett` with its Lemma 19.1 analogue
(`RoundsHouseholderVectorParlett.isReflectorPert`, order `18 n + 31`). The book's application order
`A - (β v)(vᵀ A)` associates the product differently from `RoundsHouseholderApply` and gets
`FloatingPoint.RoundsHouseholderApplyScaled` with the same Lemma 19.2 constant; both are proved
from one shared lemma, `norm_sub_le_of_forall_rounds_sub_sum`. The two-sided accumulation of Lemma
19.3 is stated for rectangular `A_k : Matrix ι κ ℝ`
(`exists_eq_prodRev_mul_add_mul_prodFwd_rect`, [golub2013matrix] (5.1.11)), the square form being
its instance.

**Householder reductions with any reflector-vector formula.** The reflector data of a step enter
only through `FloatingPoint.IsReflectorPert` (the computed `(v̂, β̂)` are order-`K` relative
perturbations of exact reflector data mapping the column to `c e_i`), which Higham's
`RoundsHouseholderVector` and Golub–Van Loan's `RoundsHouseholderVectorParlett` both provide. The
Hessenberg step in the book's association (`RoundsHessenbergStepPert`, [golub2013matrix]
Algorithm 7.4.2) and the symmetric tridiagonalization step (`RoundsTridiagonalizeStepPert`,
[golub2013matrix] Algorithm 8.3.1: the trailing block by the symmetric rank-two update
`RoundsSymmRankTwoUpdate`, one triangle computed and mirrored, the subdiagonal the freshly computed
`fl(√fl(xᵀx))`) are stated over it on the active block `{i // k + 1 ≤ i}`, each with its Frobenius
step bound against the exact reflector extended by the identity, and both reductions
(`exists_roundsHessenbergReducePert_eq`, `exists_roundsTridiagonalizePert_eq`) follow from the one
accumulation lemma `exists_eq_transpose_mul_add_mul_of_forall_step` (Lemma 19.3, two-sided, the
reflector of each step chosen). The Higham-convention `RoundsHessenbergStep` above is the
unscaled-association twin of `RoundsHessenbergStepPert`.

The scalar calculus of the constants is that of `Numlib/FloatingPoint/Model`, including the
one-step forms a Householder computation needs (`IsRelPert.mul_one_add`, `IsRelPert.div_one_add`,
`IsRelPert.rounds`, `IsRelPert.sqrt`, `isRelPert_of_abs_sub_le`).
Everything is over `ℝ`, since the statements need the Euclidean and Frobenius norms.
-/

open Finset Matrix WithLp

open scoped Matrix

namespace FloatingPoint

/-- The real phase (sign) squares to one. -/
theorem phase_mul_phase (z : ℝ) : phase z * phase z = 1 := by
  have h := norm_phase z
  rw [Real.norm_eq_abs] at h
  nlinarith [abs_mul_abs_self (phase z)]

/-- `sign z * z = |z|`. -/
theorem phase_mul_self_real (z : ℝ) : phase z * z = |z| := by
  have h := conj_phase_mul_self z
  simpa using h

/-- The real phase has absolute value one. -/
theorem abs_phase (z : ℝ) : |phase z| = 1 := by
  have h := norm_phase z
  rwa [Real.norm_eq_abs] at h

/-! ### Euclidean and Frobenius norms: the inequalities the analysis uses -/

section Norms

variable {ι κ : Type*} [Fintype ι] [Fintype κ]


/-- Monotonicity of the Euclidean norm in the entries. -/
theorem norm_toLp_le_of_abs_le {x y : ι → ℝ} (h : ∀ i, |x i| ≤ |y i|) :
    ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ ≤ ‖(toLp 2 y : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

/-- `‖|x|‖₂ = ‖x‖₂`. -/
theorem norm_toLp_abs (x : ι → ℝ) :
    ‖(toLp 2 |x| : EuclideanSpace ℝ ι)‖ = ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- Cauchy–Schwarz in the form `|x|ᵀ |y| ≤ ‖x‖₂ ‖y‖₂`. -/
theorem abs_dotProduct_abs_le (x y : ι → ℝ) :
    |x| ⬝ᵥ |y| ≤ ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ * ‖(toLp 2 y : EuclideanSpace ℝ ι)‖ := by
  have h := abs_real_inner_le_norm (toLp 2 |x| : EuclideanSpace ℝ ι) (toLp 2 |y|)
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, norm_toLp_abs, norm_toLp_abs] at h
  refine le_trans (le_abs_self _) ?_
  rwa [dotProduct_comm] at h

/-- A vector bounded entrywise by `a |b| + c |v|` has Euclidean norm at most `a ‖b‖ + c ‖v‖`. -/
theorem norm_toLp_le_of_abs_le_add {z b v : ι → ℝ} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ i, |z i| ≤ a * |b i| + c * |v i|) :
    ‖(toLp 2 z : EuclideanSpace ℝ ι)‖ ≤
      a * ‖(toLp 2 b : EuclideanSpace ℝ ι)‖ + c * ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  calc ‖(toLp 2 z : EuclideanSpace ℝ ι)‖
      ≤ ‖(toLp 2 (a • |b| + c • |v|) : EuclideanSpace ℝ ι)‖ := by
        refine norm_toLp_le_of_abs_le fun i => (h i).trans (le_of_eq ?_)
        have hi : (a • |b| + c • |v|) i = a * |b i| + c * |v i| := rfl
        rw [hi]
        exact (abs_of_nonneg (by positivity)).symm
    _ ≤ ‖(toLp 2 (a • |b|) : EuclideanSpace ℝ ι)‖ + ‖(toLp 2 (c • |v|) : EuclideanSpace ℝ ι)‖ := by
        rw [WithLp.toLp_add]
        exact norm_add_le _ _
    _ = a * ‖(toLp 2 b : EuclideanSpace ℝ ι)‖ + c * ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ := by
        rw [WithLp.toLp_smul, WithLp.toLp_smul, norm_smul, norm_smul, Real.norm_of_nonneg ha,
          Real.norm_of_nonneg hc, norm_toLp_abs, norm_toLp_abs]

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm squared is the sum of the squared Euclidean norms of the columns. -/
theorem frobenius_norm_sq_eq_sum_col (A : Matrix ι κ ℝ) :
    ‖A‖ ^ 2 = ∑ j, ‖(toLp 2 (A.col j) : EuclideanSpace ℝ ι)‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  rfl

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm squared is the sum of the squared Euclidean norms of the rows. -/
theorem frobenius_norm_sq_eq_sum_row (A : Matrix ι κ ℝ) :
    ‖A‖ ^ 2 = ∑ i, ‖(toLp 2 (A.row i) : EuclideanSpace ℝ κ)‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  rfl

open scoped Matrix.Norms.Frobenius in
/-- Columnwise bounds give a Frobenius bound: if `‖a_j‖₂ ≤ c ‖b_j‖₂` for every column `j`, then
`‖A‖_F ≤ c ‖B‖_F` ([higham2002accuracy] Lemma 6.6 (a)). -/
theorem frobenius_norm_le_of_forall_col_le {A B : Matrix ι κ ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, ‖(toLp 2 (A.col j) : EuclideanSpace ℝ ι)‖ ≤
      c * ‖(toLp 2 (B.col j) : EuclideanSpace ℝ ι)‖) : ‖A‖ ≤ c * ‖B‖ := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, frobenius_norm_sq_eq_sum_col, frobenius_norm_sq_eq_sum_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h j) 2

open scoped Matrix.Norms.Frobenius in
/-- Rowwise bounds give a Frobenius bound. -/
theorem frobenius_norm_le_of_forall_row_le {A B : Matrix ι κ ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ‖(toLp 2 (A.row i) : EuclideanSpace ℝ κ)‖ ≤
      c * ‖(toLp 2 (B.row i) : EuclideanSpace ℝ κ)‖) : ‖A‖ ≤ c * ‖B‖ := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, frobenius_norm_sq_eq_sum_row, frobenius_norm_sq_eq_sum_row, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2

open scoped Matrix.Norms.Frobenius in
/-- An entrywise bound `|A i j| ≤ c |B i j|` gives `‖A‖_F ≤ c ‖B‖_F`. -/
theorem frobenius_norm_le_of_forall_abs_le {A B : Matrix ι κ ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) : ‖A‖ ≤ c * ‖B‖ := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2

end Norms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `v ⬝ᵥ v = 2 s (x i + s)` for the Householder axis `v = x + s e_i`, `s = sign(x_i) ‖x‖₂`. -/
theorem householderAxis_dotProduct_self (x : ι → ℝ) (i : ι) :
    householderAxis x i ⬝ᵥ householderAxis x i =
      2 * (phase (x i) * ‖(toLp 2 x : EuclideanSpace ℝ ι)‖) *
        (x i + phase (x i) * ‖(toLp 2 x : EuclideanSpace ℝ ι)‖) := by
  set N := ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ with hN
  have hxx : x ⬝ᵥ x = N ^ 2 := by
    rw [hN, EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  have hv : householderAxis x i = x + (phase (x i) * N) • Pi.single i 1 := by
    simp [householderAxis, hN]
  rw [hv, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_smul, smul_dotProduct,
    smul_dotProduct, dotProduct_single, single_dotProduct, single_dotProduct, hxx]
  simp only [smul_eq_mul, mul_one, Pi.smul_apply, Pi.single_eq_same]
  have := phase_mul_phase (x i)
  linear_combination (-(N ^ 2)) * this

/-- The pivot entry of the Householder axis. -/
theorem householderAxis_apply_self (x : ι → ℝ) (i : ι) :
    householderAxis x i i = x i + phase (x i) * ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ := by
  simp [householderAxis]

/-- `|x i + sign(x i) ‖x‖| = |x i| + ‖x‖`: no cancellation in the pivot entry of the axis. -/
theorem abs_householderAxis_apply_self (x : ι → ℝ) (i : ι) :
    |householderAxis x i i| = |x i| + ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ := by
  rw [householderAxis_apply_self]
  set N := ‖(toLp 2 x : EuclideanSpace ℝ ι)‖
  have hN : 0 ≤ N := norm_nonneg _
  have h1 : phase (x i) * (x i + phase (x i) * N) = |x i| + N := by
    rw [mul_add, phase_mul_self_real, ← mul_assoc, phase_mul_phase, one_mul]
  have h2 : |phase (x i) * (x i + phase (x i) * N)| = |x i + phase (x i) * N| := by
    rw [abs_mul, abs_phase, one_mul]
  rw [← h2, h1, abs_of_nonneg (by positivity)]

/-- The reflector of the unit axis is `1 - β v vᵀ` with `β = 2 / (vᵀ v)`. -/
theorem householder_householderVec_eq (x : ι → ℝ) (i : ι) :
    householder (householderVec x i) =
      1 - (2 / (householderAxis x i ⬝ᵥ householderAxis x i)) •
        vecMulVec (householderAxis x i) (householderAxis x i) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : householderAxis (0 : ι → ℝ) i = 0 := by simp [householderAxis]
    rw [householderVec_zero, householder_zero, h]
    simp
  · have hv : householderAxis x i ≠ 0 := householderAxis_ne_zero hx i
    have hn : ‖(toLp 2 (householderAxis x i) : EuclideanSpace ℝ ι)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (by simpa using hv)
    have hsq : ‖(toLp 2 (householderAxis x i) : EuclideanSpace ℝ ι)‖ ^ 2 =
        householderAxis x i ⬝ᵥ householderAxis x i :=
      (dotProduct_self_eq_norm_sq _).symm
    change householder ((‖(toLp 2 (householderAxis x i) : EuclideanSpace ℝ ι)‖)⁻¹ •
      householderAxis x i) = _
    rw [householder, star_trivial, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul, ← hsq]
    congr 2
    field_simp

/-! ### The computed Householder vector -/

/-- **The Householder vector in floating-point arithmetic**, [higham2002accuracy] Lemma 19.1,
construction (19.1). -/
def RoundsHouseholderVector (m : RoundingModel ℝ) (x : ι → ℝ) (i : ι) (vhat : ι → ℝ)
    (βhat : ℝ) : Prop :=
  ∃ s₀ nhat what phat : ℝ, RoundsDot m x x s₀ ∧ m.Rounds (√s₀) nhat ∧
    m.Rounds (x i + phase (x i) * nhat) what ∧
    m.Rounds (phase (x i) * nhat * what) phat ∧ m.Rounds (1 / phat) βhat ∧
    vhat i = what ∧ ∀ j, j ≠ i → vhat j = x j

/-- **[higham2002accuracy] Lemma 19.1.** -/
theorem RoundsHouseholderVector.isRelPert {m : RoundingModel ℝ}
    (hcard : ((4 * Fintype.card ι + 8 : ℕ) : ℝ) * m.u < 1) {x : ι → ℝ} {i : ι} {vhat : ι → ℝ}
    {βhat : ℝ} (h : RoundsHouseholderVector m x i vhat βhat) :
    IsRelPert m.u (4 * Fintype.card ι + 8)
        (2 / (householderAxis x i ⬝ᵥ householderAxis x i)) βhat ∧
      IsRelPert m.u (Fintype.card ι + 2) (householderAxis x i i) (vhat i) ∧
      ∀ j, j ≠ i → vhat j = householderAxis x i j := by
  obtain ⟨s₀, nhat, what, phat, hs₀, hn, hw, hp, hβ, hvi, hvj⟩ := h
  set n := Fintype.card ι with hn_def
  have hu0 := m.u_nonneg
  have hlt : ∀ k : ℕ, k ≤ 4 * n + 8 → ((k : ℕ) : ℝ) * m.u < 1 := fun k hk =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hu0).trans_lt hcard
  have hu1 : m.u < 1 := by simpa using hlt 1 (by omega)
  have hγ : ∀ k : ℕ, k ≤ 4 * n + 8 → 0 ≤ gamma m.u k := fun k hk =>
    gamma_nonneg hu0 (hlt k hk)
  have hvj' : ∀ j, j ≠ i → vhat j = householderAxis x i j := fun j hj => by
    rw [hvj j hj, householderAxis_apply_of_ne x hj]
  rcases eq_or_ne x 0 with rfl | hx
  · -- the degenerate case `x = 0`: everything is zero
    have h0 : s₀ = 0 := by
      have := abs_sub_le_of_roundsDot hu1 (hlt n (by omega)) hs₀
      simp only [dotProduct_zero, sub_zero, abs_zero, mul_zero] at this
      exact abs_nonpos_iff.1 this
    subst h0
    rw [Real.sqrt_zero] at hn
    have h1 := hn.eq_zero_of_zero
    subst h1
    simp only [Pi.zero_apply, mul_zero, add_zero] at hw
    have h2 := hw.eq_zero_of_zero
    subst h2
    simp only [mul_zero] at hp
    have h3 := hp.eq_zero_of_zero
    subst h3
    simp only [div_zero] at hβ
    rw [hβ.eq_zero_of_zero]
    have hax : householderAxis (0 : ι → ℝ) i = 0 := by simp [householderAxis]
    refine ⟨?_, ?_, hvj'⟩
    · rw [hax]
      simpa using IsRelPert.zero (hγ _ le_rfl)
    · rw [hax, hvi]
      simpa using IsRelPert.zero (hγ _ (by omega))
  · -- the main case
    set N := ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ with hN_def
    set σ := phase (x i) with hσ_def
    have hNpos : 0 < N := norm_pos_iff.2 (by simpa using hx)
    have hvv : householderAxis x i ⬝ᵥ householderAxis x i = 2 * (σ * N) * (x i + σ * N) :=
      householderAxis_dotProduct_self x i
    have hvii : householderAxis x i i = x i + σ * N := householderAxis_apply_self x i
    have hwabs : |x i + σ * N| = |x i| + N := by
      rw [← hvii]
      exact abs_householderAxis_apply_self x i
    have hwne : x i + σ * N ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hwabs
      linarith [abs_nonneg (x i)]
    have hσne : σ ≠ 0 := by
      intro h0
      have := abs_phase (x i)
      rw [← hσ_def, h0, abs_zero] at this
      exact zero_ne_one this
    -- the computed norm
    have hxx : x ⬝ᵥ x = N ^ 2 := dotProduct_self_eq_norm_sq x
    have hxxabs : |x| ⬝ᵥ |x| = x ⬝ᵥ x := by
      simp only [dotProduct, Pi.abs_apply, abs_mul_abs_self]
    have hnn : 0 ≤ x ⬝ᵥ x := by rw [hxx]; positivity
    have h1 : IsRelPert m.u n (x ⬝ᵥ x) s₀ := by
      refine isRelPert_of_abs_sub_le (hγ n (by omega)) ?_
      have := abs_sub_le_of_roundsDot hu1 (hlt n (by omega)) hs₀
      rw [hxxabs] at this
      rwa [abs_of_nonneg hnn]
    have h2 : IsRelPert m.u n N (√s₀) := by
      have := h1.sqrt (gamma_lt_one hu0 (by
        have := hlt (2 * n) (by omega)
        push_cast at this
        linarith)).le (by rw [hxx]; positivity)
      rwa [hxx, Real.sqrt_sq hNpos.le] at this
    have h3 : IsRelPert m.u (n + 1) N nhat := h2.rounds hu1 (hlt _ (by omega)) hn
    have h4 : IsRelPert m.u (n + 1) (σ * N) (σ * nhat) := h3.const_mul σ
    -- the pivot entry: no cancellation
    have h5 : IsRelPert m.u (n + 1) (x i + σ * N) (x i + σ * nhat) := by
      obtain ⟨θ, hθ, hθe⟩ := h4
      refine ⟨σ * N * θ / (x i + σ * N), ?_, ?_⟩
      · rw [abs_div, div_le_iff₀ (abs_pos.2 hwne), hwabs, abs_mul, abs_mul, abs_phase, one_mul,
          abs_of_pos hNpos]
        have := abs_nonneg (x i)
        nlinarith [hγ (n + 1) (by omega)]
      · rw [mul_add, mul_one, mul_div_cancel₀ _ hwne, hθe]
        ring
    have h6 : IsRelPert m.u (n + 2) (x i + σ * N) what := h5.rounds hu1 (hlt _ (by omega)) hw
    have h7 : IsRelPert m.u (2 * n + 3) (σ * N * (x i + σ * N)) (σ * nhat * what) := by
      have := h4.mul hu0 (k := n + 1) (j := n + 2) (hlt _ (by omega)) h6
      rwa [show n + 1 + (n + 2) = 2 * n + 3 by ring] at this
    -- the reciprocal
    obtain ⟨δ₃, hδ₃, hpe⟩ := hp.exists_delta
    obtain ⟨δ₄, hδ₄, hβe⟩ := hβ.exists_delta
    have hδ₄' : IsRelPert m.u 1 1 (1 + δ₄) :=
      ⟨δ₄, hδ₄.trans (le_gamma_one hu0 hu1), by ring⟩
    have h8 : IsRelPert m.u (4 * n + 7) (1 / (σ * N * (x i + σ * N)))
        ((1 + δ₄) / (σ * nhat * what)) := by
      have := hδ₄'.div hu0 (k := 1) (j := 2 * n + 3) (hlt _ (by omega)) h7
      rwa [show 1 + 2 * (2 * n + 3) = 4 * n + 7 by ring] at this
    have h9 : IsRelPert m.u (4 * n + 8) (1 / (σ * N * (x i + σ * N))) βhat := by
      have := h8.div_one_add hu0 (hlt _ (by omega)) hδ₃
      rw [hβe, hpe]
      convert this using 1
      rw [div_div, mul_comm]
      field_simp
    refine ⟨?_, ?_, hvj'⟩
    · have hAB : 2 / (householderAxis x i ⬝ᵥ householderAxis x i) =
          1 / (σ * N * (x i + σ * N)) := by
        rw [hvv]
        have h2ne : (σ * N) * (x i + σ * N) ≠ 0 := mul_ne_zero (mul_ne_zero hσne hNpos.ne') hwne
        field_simp
      rw [hAB]
      exact h9
    · rw [hvii, hvi]
      exact h6

/-! ### Reflector data, whatever the formula that produced them -/

omit [Fintype ι] in
/-- The matrix `1 - β v vᵀ` is symmetric. -/
theorem transpose_one_sub_smul_vecMulVec (β : ℝ) (v : ι → ℝ) :
    (1 - β • vecMulVec v v)ᵀ = 1 - β • vecMulVec v v := by
  rw [transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]

/-- `(1 - β v vᵀ)² = 1 + β (β vᵀv - 2) v vᵀ`. -/
theorem one_sub_smul_vecMulVec_mul_self (β : ℝ) (v : ι → ℝ) :
    (1 - β • vecMulVec v v) * (1 - β • vecMulVec v v) =
      1 + (β * (β * (v ⬝ᵥ v) - 2)) • vecMulVec v v := by
  have hV : vecMulVec v v * vecMulVec v v = (v ⬝ᵥ v) • vecMulVec v v := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hV, smul_smul]
  module

/-- `1 - β v vᵀ` is orthogonal as soon as `β (β vᵀv - 2) = 0`: a reflector (`β vᵀv = 2`) or the
identity (`β = 0`). -/
theorem one_sub_smul_vecMulVec_mem_orthogonalGroup {β : ℝ} {v : ι → ℝ}
    (h : β * (β * (v ⬝ᵥ v) - 2) = 0) :
    (1 - β • vecMulVec v v) ∈ Matrix.orthogonalGroup ι ℝ := by
  rw [mem_orthogonalGroup_iff, transpose_one_sub_smul_vecMulVec,
    one_sub_smul_vecMulVec_mul_self, h, zero_smul, add_zero]

/-- The entries of `(1 - β v vᵀ) b`. -/
theorem one_sub_smul_vecMulVec_mulVec_apply (β : ℝ) (v b : ι → ℝ) (i : ι) :
    ((1 - β • vecMulVec v v) *ᵥ b) i = b i - β * v i * (v ⬝ᵥ b) := by
  rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul,
    Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- **Computed reflector data, whatever the formula that produced them.** For `x : ι → ℝ`, a
pivot `i : ι` and a target `c : ℝ`, `IsReflectorPert u K x i c v̂ β̂` says that the computed
`(v̂, β̂)` are relative perturbations of order `K` of exact data `(v, β)` whose matrix
`1 - β v vᵀ` is orthogonal, sends `x` to `c e_i` (so `|c| = ‖x‖₂`), and has `|β| ‖v‖₂² ≤ 2`.
This is the only thing a Householder *reduction* needs from the formula that computed the
vector, so the reductions below are stated over it: [higham2002accuracy] (19.1)
(`RoundsHouseholderVector.isReflectorPert`) and [golub2013matrix] Algorithm 5.1.1 with Parlett's
formula (`RoundsHouseholderVectorParlett.isReflectorPert`) both provide it. -/
def IsReflectorPert (u : ℝ) (K : ℕ) (x : ι → ℝ) (i : ι) (c : ℝ) (vhat : ι → ℝ) (βhat : ℝ) :
    Prop :=
  ∃ (v : ι → ℝ) (β : ℝ), (1 - β • vecMulVec v v) ∈ Matrix.orthogonalGroup ι ℝ ∧
    (1 - β • vecMulVec v v) *ᵥ x = c • Pi.single i 1 ∧ |β| * (v ⬝ᵥ v) ≤ 2 ∧
    IsRelPert u K β βhat ∧ ∀ j, IsRelPert u K (v j) (vhat j)

omit [DecidableEq ι] in
/-- `|2 / (v ⬝ᵥ v)| (v ⬝ᵥ v) ≤ 2`: the normalization of a reflector, `0` included. -/
theorem abs_two_div_dotProduct_self_mul_le (v : ι → ℝ) : |2 / (v ⬝ᵥ v)| * (v ⬝ᵥ v) ≤ 2 := by
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
  rcases eq_or_lt_of_le hvv with h0 | hpos
  · rw [← h0]; simp
  · rw [abs_of_pos (by positivity), div_mul_cancel₀ _ hpos.ne']

/-- [higham2002accuracy]'s computed Householder vector is reflector data in the sense of
`IsReflectorPert`, with the exact data `v = householderAxis x i`, `β = 2 / (vᵀv)` and the target
`-sign(x_i) ‖x‖₂` (Lemma 19.1, `RoundsHouseholderVector.isRelPert`). -/
theorem RoundsHouseholderVector.isReflectorPert {m : RoundingModel ℝ}
    (hcard : ((4 * Fintype.card ι + 8 : ℕ) : ℝ) * m.u < 1) {x : ι → ℝ} {i : ι} {vhat : ι → ℝ}
    {βhat : ℝ} (h : RoundsHouseholderVector m x i vhat βhat) :
    IsReflectorPert m.u (4 * Fintype.card ι + 8) x i
      (-(phase (x i) * ‖(toLp 2 x : EuclideanSpace ℝ ι)‖)) vhat βhat := by
  obtain ⟨hβ, hvi, hvj⟩ := h.isRelPert hcard
  have hu0 := m.u_nonneg
  have hP := householder_householderVec_eq x i
  refine ⟨householderAxis x i, 2 / (householderAxis x i ⬝ᵥ householderAxis x i), ?_, ?_,
    abs_two_div_dotProduct_self_mul_le _, hβ, fun j => ?_⟩
  · rw [← hP]
    rcases eq_or_ne x 0 with rfl | hx
    · rw [householderVec_zero, householder_zero]
      exact one_mem _
    · exact householder_householderVec_mem_unitaryGroup hx i
  · rw [← hP]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [householder_mulVec_eq_smul_single hx i]
      simp
  · rcases eq_or_ne j i with rfl | hj
    · exact hvi.mono hu0 (by omega) hcard
    · rw [hvj j hj]
      exact (IsRelPert.refl _ _).mono hu0 (Nat.zero_le _) hcard

/-! ### Parlett's formula: [golub2013matrix] Algorithm 5.1.1 -/

/-- **The computed Householder vector of [golub2013matrix] Algorithm 5.1.1** (`house`, with
Parlett's formula for the pivot entry), as a relation on `x : ι → ℝ`, a pivot `i : ι` and the
computed `(v̂, β̂)`: the tail inner product `σ̂ = fl(∑_{j ≠ i} x_j²)` is a `RoundsDot`, `v̂_i = 1`,
and either `σ̂ = 0` and `β̂ = 0` (for `x_i ≥ 0`) or `β̂ = 2` (for `x_i < 0`) with `v̂_j = x_j` off
the pivot, or `σ̂ ≠ 0` and `μ = fl(√fl(fl(x_i²) + σ̂))`, `v₁ = fl(x_i - μ)` for `x_i ≤ 0` and
`v₁ = fl(-σ̂ / fl(x_i + μ))` for `x_i > 0`, `β̂ = fl(fl(2 fl(v₁²)) / fl(σ̂ + fl(v₁²)))` and
`v̂_j = fl(x_j / v₁)` off the pivot. The book prints `β = -2` in the second case, which makes
`I - β v vᵀ = I + 2 e_i e_iᵀ` not orthogonal; `β = 2` is the correct value. -/
def RoundsHouseholderVectorParlett (m : RoundingModel ℝ) (x : ι → ℝ) (i : ι) (vhat : ι → ℝ)
    (βhat : ℝ) : Prop :=
  ∃ σhat, RoundsDot m (fun j : {j // j ≠ i} => x j) (fun j => x j) σhat ∧ vhat i = 1 ∧
    ((σhat = 0 ∧ 0 ≤ x i ∧ βhat = 0 ∧ ∀ j, j ≠ i → vhat j = x j) ∨
     (σhat = 0 ∧ x i < 0 ∧ βhat = 2 ∧ ∀ j, j ≠ i → vhat j = x j) ∨
     (σhat ≠ 0 ∧ ∃ p t μ v₁ q w d : ℝ, m.Rounds (x i * x i) p ∧
        m.Rounds (p + σhat) t ∧ m.Rounds (√t) μ ∧
        (x i ≤ 0 ∧ m.Rounds (x i - μ) v₁ ∨
          0 < x i ∧ ∃ e, m.Rounds (x i + μ) e ∧ m.Rounds (-σhat / e) v₁) ∧
        m.Rounds (v₁ * v₁) q ∧ m.Rounds (2 * q) w ∧ m.Rounds (σhat + q) d ∧
        m.Rounds (w / d) βhat ∧ ∀ j, j ≠ i → m.Rounds (x j / v₁) (vhat j)))

/-- `‖x‖₂² = x_i² + ∑_{j ≠ i} x_j²`. -/
theorem norm_toLp_sq_eq_mul_self_add_sum (x : ι → ℝ) (i : ι) :
    ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 = x i * x i + ∑ j : {j // j ≠ i}, x j * x j := by
  rw [← dotProduct_self_eq_norm_sq, dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ i]

/-- **The analogue of [higham2002accuracy] Lemma 19.1 for [golub2013matrix] Algorithm 5.1.1.**
With `n = card ι` and `(18 n + 31) u < 1`, the computed `(v̂, β̂)` of Parlett's formula have
`v̂_i = 1` and are reflector data of order `18 n + 31` with the target `+‖x‖₂` (the book's sign):
the exact `(v, β)` are the exact output of the same branch. With `k = n - 1` terms in `σ̂`: `μ̂` has
order `k + 2`; `v̂₁` order `k + 3` (`x_i ≤ 0`, a same-sign sum) or `3k + 7` (Parlett's quotient);
`v̂₁²` order `6k + 15`; `β̂` order `18k + 49`; `v̂_j` order `6k + 15`. -/
theorem RoundsHouseholderVectorParlett.isReflectorPert {m : RoundingModel ℝ}
    (hcard : ((18 * Fintype.card ι + 31 : ℕ) : ℝ) * m.u < 1) {x : ι → ℝ} {i : ι}
    {vhat : ι → ℝ} {βhat : ℝ} (h : RoundsHouseholderVectorParlett m x i vhat βhat) :
    vhat i = 1 ∧ IsReflectorPert m.u (18 * Fintype.card ι + 31) x i
      ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ vhat βhat := by
  obtain ⟨σhat, hσ, hvi, hbr⟩ := h
  refine ⟨hvi, ?_⟩
  set n := Fintype.card ι with hn_def
  set K := 18 * n + 31 with hK_def
  set k := Fintype.card {j // j ≠ i} with hk_def
  have hkn : k + 1 ≤ n := Fintype.card_subtype_lt (p := fun j => j ≠ i) (x := i) (by simp)
  have hu0 := m.u_nonneg
  have hlt : ∀ j : ℕ, j ≤ K → ((j : ℕ) : ℝ) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hu0).trans_lt hcard
  have hu1 : m.u < 1 := by simpa using hlt 1 (by omega)
  have hmono : ∀ {j : ℕ} {a b : ℝ}, j ≤ K → IsRelPert m.u j a b → IsRelPert m.u K a b :=
    fun hj h => h.mono hu0 hj (hlt K le_rfl)
  set σ := ∑ j : {j // j ≠ i}, x j * x j with hσ_def
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hσrel : IsRelPert m.u k σ σhat := by
    refine isRelPert_of_abs_sub_le (gamma_nonneg hu0 (hlt k (by omega))) ?_
    have := abs_sub_le_of_roundsDot hu1 (hlt k (by omega)) hσ
    have e2 : |(fun j : {j // j ≠ i} => x j)| ⬝ᵥ |(fun j : {j // j ≠ i} => x j)| = σ := by
      simp only [dotProduct, Pi.abs_apply, abs_mul_abs_self, hσ_def]
    rw [e2] at this
    rwa [abs_of_nonneg hσ0]
  set N := ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ with hN_def
  have hN0 : 0 ≤ N := norm_nonneg _
  have hN2 : N * N = x i * x i + σ := by rw [← sq]; exact norm_toLp_sq_eq_mul_self_add_sum x i
  -- the tail vanishes exactly when its computed square norm does
  have htail0 : σ = 0 → ∀ j, j ≠ i → x j = 0 := fun h0 j hj => by
    have := (Finset.sum_eq_zero_iff_of_nonneg
      fun (j : {j // j ≠ i}) _ => mul_self_nonneg (x j)).1 h0 ⟨j, hj⟩ (Finset.mem_univ _)
    exact mul_self_eq_zero.1 this
  have hσhat0 : σhat = 0 → σ = 0 := fun h0 => by
    obtain ⟨θ, hθ, he⟩ := hσrel
    rw [h0] at he
    have hg : gamma m.u k < 1 := gamma_lt_one hu0 (by
      have := hlt (2 * k) (by omega)
      push_cast at this
      linarith)
    have hθ1 : 0 < 1 + θ := by linarith [neg_le_of_abs_le hθ]
    rcases mul_eq_zero.1 he.symm with h | h
    · exact h
    · linarith
  have hσ0hat : σ = 0 → σhat = 0 := fun h0 => by
    obtain ⟨θ, -, he⟩ := hσrel
    rw [he, h0, zero_mul]
  have hxsingle : σ = 0 → x = x i • Pi.single i 1 := fun h0 => by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [Pi.single_eq_of_ne hj, htail0 h0 j hj]
  have hNabs : σ = 0 → N = |x i| := fun h0 => by
    have h2 : N ^ 2 = |x i| ^ 2 := by rw [sq, hN2, h0, add_zero, sq_abs, sq]
    exact (pow_left_inj₀ hN0 (abs_nonneg _) two_ne_zero).1 h2
  rcases hbr with ⟨h0, hxi, hβ0, hvj⟩ | ⟨h0, hxi, hβ2, hvj⟩ |
      ⟨h0, p, t, μ, v₁, q, w, d, hp, ht, hμ, hv₁, hq, hw, hd, hβ, hvj⟩
  · -- `σ = 0`, `x_i ≥ 0`: `β = 0`, the identity
    have hσz := hσhat0 h0
    refine ⟨vhat, 0, one_sub_smul_vecMulVec_mem_orthogonalGroup (by ring), ?_, by simp, ?_,
      fun j => hmono (Nat.zero_le _) (IsRelPert.refl _ _)⟩
    · rw [zero_smul, sub_zero, one_mulVec, hNabs hσz, abs_of_nonneg hxi]
      exact hxsingle hσz
    · rw [hβ0]
      exact hmono (Nat.zero_le _) (IsRelPert.refl _ _)
  · -- `σ = 0`, `x_i < 0`: `β = 2`, the reflection in the pivot coordinate
    have hσz := hσhat0 h0
    have hv : vhat = Pi.single i 1 := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp [hvi]
      · rw [hvj j hj, htail0 hσz j hj, Pi.single_eq_of_ne hj]
    have hvv : vhat ⬝ᵥ vhat = 1 := by rw [hv]; simp
    refine ⟨vhat, 2, one_sub_smul_vecMulVec_mem_orthogonalGroup (by rw [hvv]; ring), ?_,
      le_of_eq (by rw [hvv]; norm_num), ?_,
      fun j => hmono (Nat.zero_le _) (IsRelPert.refl _ _)⟩
    · ext r
      rw [one_sub_smul_vecMulVec_mulVec_apply, hNabs hσz, abs_of_neg hxi, hv, single_dotProduct]
      rcases eq_or_ne r i with rfl | hr
      · simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
        ring
      · simp [Pi.single_eq_of_ne hr, htail0 hσz r hr]
    · rw [hβ2]
      exact hmono (Nat.zero_le _) (IsRelPert.refl _ _)
  · -- the main branch
    have hσpos : 0 < σ := lt_of_le_of_ne hσ0 fun h => h0 (hσ0hat h.symm)
    have hk1 : 1 ≤ k := by
      obtain ⟨j, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσpos.ne'
      exact Fintype.card_pos_iff.2 ⟨j⟩
    have hNpos : 0 < N := lt_of_le_of_ne hN0 fun h => by
      rw [← h, mul_zero] at hN2
      nlinarith [mul_self_nonneg (x i)]
    have hxN : x i < N := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith [mul_le_mul hc' hc' hN0 (hN0.trans hc')]
    set e := x i - N with he_def
    have he_neg : e < 0 := by linarith
    have he_ne : e ≠ 0 := he_neg.ne
    have hkey : e * (x i + N) = -σ := by
      rw [he_def]
      linear_combination (-1 : ℝ) * hN2
    -- the exact data
    set v : ι → ℝ := fun j => if j = i then 1 else x j / e with hv_def
    set β : ℝ := 2 * (e * e) / (σ + e * e) with hβ_def
    have hden : 0 < σ + e * e := add_pos_of_pos_of_nonneg hσpos (mul_self_nonneg e)
    have hvi' : v i = 1 := by simp [hv_def]
    have htail : ∀ j, j ≠ i → v j = x j / e := fun j hj => by simp [hv_def, hj]
    have hvv : v ⬝ᵥ v = 1 + σ / (e * e) := by
      rw [dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ i, hvi', hσ_def, Finset.sum_div]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun j _ => by rw [htail j j.2, div_mul_div_comm]
    have hβvv : β * (v ⬝ᵥ v) = 2 := by
      rw [hvv, hβ_def]
      field_simp
      ring
    have hβpos : 0 < β := div_pos (mul_pos two_pos (mul_self_pos.2 he_ne)) hden
    have hvx : v ⬝ᵥ x = -N := by
      rw [dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ i, hvi']
      have hs : ∑ j : {j // j ≠ i}, v j * x j = σ / e := by
        rw [hσ_def, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by rw [htail j j.2]; ring
      rw [hs, eq_neg_iff_add_eq_zero]
      field_simp
      linear_combination hkey
    have hβN : β * N = -e := by
      rw [hβ_def, div_mul_eq_mul_div, div_eq_iff hden.ne']
      have hσe : σ = -(e * (x i + N)) := by linarith
      rw [hσe, he_def]
      ring
    have hPx : (1 - β • vecMulVec v v) *ᵥ x = N • Pi.single i 1 := by
      ext r
      rw [one_sub_smul_vecMulVec_mulVec_apply, hvx,
        show x r - β * v r * -N = x r + β * N * v r by ring, hβN]
      rcases eq_or_ne r i with rfl | hr
      · rw [hvi']
        simp [he_def]
      · rw [htail r hr, Pi.smul_apply, Pi.single_eq_of_ne hr, smul_zero]
        field_simp
        ring
    -- the computed quantities, one rounding at a time
    have hp1 : IsRelPert m.u k (x i * x i) p :=
      (hp.isRelPert hu1).mono hu0 hk1 (hlt k (by omega))
    have ht1 : IsRelPert m.u (k + 1) (x i * x i + σ) t :=
      (IsRelPert.add_of_nonneg (mul_self_nonneg _) hσ0 hp1 hσrel).rounds hu1 (hlt _ (by omega)) ht
    have hsqrt : IsRelPert m.u (k + 1) N (√t) := by
      have hg : gamma m.u (k + 1) ≤ 1 := (gamma_lt_one hu0 (by
        have := hlt (2 * (k + 1)) (by omega)
        push_cast at this ⊢
        linarith)).le
      have := ht1.sqrt hg (add_nonneg (mul_self_nonneg _) hσ0)
      rwa [← hN2, Real.sqrt_mul_self hN0] at this
    have hμ1 : IsRelPert m.u (k + 2) N μ := hsqrt.rounds hu1 (hlt _ (by omega)) hμ
    have hx0 : IsRelPert m.u (k + 2) (x i) (x i) :=
      (IsRelPert.refl _ _).mono hu0 (Nat.zero_le _) (hlt _ (by omega))
    have hv₁' : IsRelPert m.u (3 * k + 7) e v₁ := by
      rcases hv₁ with ⟨hxi, hr⟩ | ⟨hxi, e', he', hr⟩
      · have hmx : IsRelPert m.u (k + 2) (-x i) (-x i) :=
          (IsRelPert.refl _ _).mono hu0 (Nat.zero_le _) (hlt _ (by omega))
        obtain ⟨θ, hθ, hθe⟩ := IsRelPert.add_of_nonneg (by linarith) hN0 hmx hμ1
        have h2 : IsRelPert m.u (k + 2) e (x i - μ) :=
          ⟨θ, hθ, by rw [he_def]; linear_combination (-1 : ℝ) * hθe⟩
        exact (h2.rounds hu1 (hlt _ (by omega)) hr).mono hu0 (by omega) (hlt _ (by omega))
      · have h2 : IsRelPert m.u (k + 3) (x i + N) e' :=
          (IsRelPert.add_of_nonneg hxi.le hN0 hx0 hμ1).rounds hu1 (hlt _ (by omega)) he'
        have hneg : IsRelPert m.u k (-σ) (-σhat) := by simpa using hσrel.const_mul (-1)
        have h3 := hneg.div hu0 (k := k) (j := k + 3) (hlt _ (by omega)) h2
        have hval : -σ / (x i + N) = e := by
          rw [div_eq_iff (by linarith), hkey]
        rw [hval] at h3
        have h4 := h3.rounds hu1 (hlt _ (by omega)) hr
        rwa [show k + 2 * (k + 3) + 1 = 3 * k + 7 by ring] at h4
    have hq1 : IsRelPert m.u (6 * k + 15) (e * e) q := by
      have := (hv₁'.mul hu0 (k := 3 * k + 7) (j := 3 * k + 7) (hlt _ (by omega)) hv₁').rounds
        hu1 (hlt _ (by omega)) hq
      rwa [show 3 * k + 7 + (3 * k + 7) + 1 = 6 * k + 15 by ring] at this
    have hw1 : IsRelPert m.u (6 * k + 16) (2 * (e * e)) w :=
      (hq1.const_mul 2).rounds hu1 (hlt _ (by omega)) hw
    have hd1 : IsRelPert m.u (6 * k + 16) (σ + e * e) d :=
      (IsRelPert.add_of_nonneg hσ0 (mul_self_nonneg e)
        (hσrel.mono hu0 (by omega) (hlt _ (by omega))) hq1).rounds hu1 (hlt _ (by omega)) hd
    have hβ1 : IsRelPert m.u (18 * k + 49) β βhat := by
      have := (hw1.div hu0 (k := 6 * k + 16) (j := 6 * k + 16) (hlt _ (by omega)) hd1).rounds
        hu1 (hlt _ (by omega)) hβ
      rwa [show 6 * k + 16 + 2 * (6 * k + 16) + 1 = 18 * k + 49 by ring] at this
    have hvj1 : ∀ j, j ≠ i → IsRelPert m.u (6 * k + 15) (x j / e) (vhat j) := fun j hj => by
      have := ((IsRelPert.refl m.u (x j)).div hu0 (k := 0) (j := 3 * k + 7) (hlt _ (by omega))
        hv₁').rounds hu1 (hlt _ (by omega)) (hvj j hj)
      rwa [show 0 + 2 * (3 * k + 7) + 1 = 6 * k + 15 by ring] at this
    refine ⟨v, β, one_sub_smul_vecMulVec_mem_orthogonalGroup (by rw [hβvv]; ring), hPx,
      le_of_eq (by rw [abs_of_pos hβpos, hβvv]), hmono (by omega) hβ1, fun j => ?_⟩
    rcases eq_or_ne j i with rfl | hj
    · rw [hvi', hvi]
      exact hmono (Nat.zero_le _) (IsRelPert.refl _ _)
    · rw [htail j hj]
      exact hmono (by omega) (hvj1 j hj)

/-! ### The computed application of a reflector -/
/-- **The application of a Householder matrix in floating-point arithmetic**,
[higham2002accuracy] Lemma 19.2: `y = (I - β v vᵀ) b` computed as `b - v (β (vᵀ b))`. -/
def RoundsHouseholderApply (m : RoundingModel ℝ) (β : ℝ) (v b y : ι → ℝ) : Prop :=
  ∃ (s t : ℝ) (w : ι → ℝ), RoundsDot m v b s ∧ m.Rounds (β * s) t ∧
    (∀ i, m.Rounds (v i * t) (w i)) ∧ ∀ i, m.Rounds (b i - w i) (y i)

/-- **The core of [higham2002accuracy] Lemma 19.2**, shared by both associations of the update
(`norm_sub_le_of_roundsHouseholderApply`, `norm_sub_le_of_roundsHouseholderApplyScaled`): if
`ŷ_i = fl(b_i - w_i)` where `w_i = ∑_j c_ij b_j` and every coefficient `c_ij` is a relative
perturbation of order `K` of `β v_i v_j`, and `|β| ‖v‖₂² ≤ 2`, then
`‖ŷ - (1 - β v vᵀ) b‖₂ ≤ 3 γ_{K+1} ‖b‖₂`. -/
theorem norm_sub_le_of_forall_rounds_sub_sum {m : RoundingModel ℝ} {K : ℕ}
    (hK : ((K + 1 : ℕ) : ℝ) * m.u < 1) {β : ℝ} {v b w y : ι → ℝ} {c : ι → ι → ℝ}
    (hc : ∀ i j, IsRelPert m.u K (β * v i * v j) (c i j)) (hwi : ∀ i, w i = ∑ j, c i j * b j)
    (hy : ∀ i, m.Rounds (b i - w i) (y i)) (hP : |β| * (v ⬝ᵥ v) ≤ 2) :
    ‖(toLp 2 (y - (1 - β • vecMulVec v v) *ᵥ b) : EuclideanSpace ℝ ι)‖ ≤
      3 * gamma m.u (K + 1) * ‖(toLp 2 b : EuclideanSpace ℝ ι)‖ := by
  have hu0 := m.u_nonneg
  have hKu : (K : ℝ) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ K)) hu0).trans_lt hK
  have hu1 : m.u < 1 := by
    have := (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.succ_le_succ (Nat.zero_le K))) hu0)
    simp only [Nat.cast_one, one_mul] at this
    linarith
  set γ' := gamma m.u K with hγ'_def
  set γ := gamma m.u (K + 1) with hγ_def
  have hγ'0 : 0 ≤ γ' := gamma_nonneg hu0 hKu
  have hγ0 : 0 ≤ γ := gamma_nonneg hu0 hK
  choose δ₃ hδ₃ hyeq using fun i => (hy i).exists_delta
  have hvb : v ⬝ᵥ b = ∑ j, v j * b j := rfl
  have habsdot : |v| ⬝ᵥ |b| = ∑ j, |v j| * |b j| := rfl
  have hD0 : 0 ≤ |v| ⬝ᵥ |b| := by
    rw [habsdot]
    exact Finset.sum_nonneg fun j _ => by positivity
  -- the error and the size of `w i`
  have hwerr : ∀ i, |w i - β * v i * (v ⬝ᵥ b)| ≤ γ' * (|β| * |v i| * (|v| ⬝ᵥ |b|)) := by
    intro i
    rw [hwi, hvb, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [habsdot, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := (hc i j).abs_sub_le
    rw [abs_mul, abs_mul] at this
    calc |c i j * b j - β * v i * (v j * b j)|
        = |c i j - β * v i * v j| * |b j| := by
          rw [← abs_mul]
          congr 1
          ring
      _ ≤ γ' * (|β| * |v i| * |v j|) * |b j| :=
          mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = γ' * (|β| * |v i| * (|v j| * |b j|)) := by ring
  have hwsize : ∀ i, |w i| ≤ (1 + γ') * (|β| * |v i| * (|v| ⬝ᵥ |b|)) := by
    intro i
    have h1 : |β * v i * (v ⬝ᵥ b)| ≤ |β| * |v i| * (|v| ⬝ᵥ |b|) := by
      rw [abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hvb, habsdot]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ =>
        abs_mul _ _))
    have h2 := hwerr i
    have h3 : |w i| ≤ |w i - β * v i * (v ⬝ᵥ b)| + |β * v i * (v ⬝ᵥ b)| := by
      simpa using abs_add_le (w i - β * v i * (v ⬝ᵥ b)) (β * v i * (v ⬝ᵥ b))
    nlinarith
  -- the entrywise error of `y`
  have hstep : γ' * (1 + m.u) + m.u ≤ γ := gamma_mul_one_add_add_le hu0 hu1 hK
  have hyerr : ∀ i, |y i - ((1 - β • vecMulVec v v) *ᵥ b) i| ≤
      m.u * |b i| + (γ * (|β| * (|v| ⬝ᵥ |b|))) * |v i| := by
    intro i
    rw [one_sub_smul_vecMulVec_mulVec_apply, hyeq i]
    have hsplit : (b i - w i) * (1 + δ₃ i) - (b i - β * v i * (v ⬝ᵥ b)) =
        (b i - w i) * δ₃ i + (β * v i * (v ⬝ᵥ b) - w i) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h1 : |b i - w i| ≤ |b i| + |w i| := abs_sub _ _
    have h2 := hwsize i
    have h3 : |β * v i * (v ⬝ᵥ b) - w i| ≤ γ' * (|β| * |v i| * (|v| ⬝ᵥ |b|)) := by
      rw [abs_sub_comm]
      exact hwerr i
    have h4 : |b i - w i| * |δ₃ i| ≤ (|b i| + (1 + γ') * (|β| * |v i| * (|v| ⬝ᵥ |b|))) * m.u :=
      mul_le_mul (h1.trans (by linarith)) (hδ₃ i) (abs_nonneg _) (by positivity)
    have hP0 : 0 ≤ |β| * |v i| * (|v| ⬝ᵥ |b|) := by positivity
    have h5 : (γ' * (1 + m.u) + m.u) * (|β| * |v i| * (|v| ⬝ᵥ |b|)) ≤
        γ * (|β| * |v i| * (|v| ⬝ᵥ |b|)) := mul_le_mul_of_nonneg_right hstep hP0
    nlinarith
  -- collect
  have hnorm := norm_toLp_le_of_abs_le_add hu0 (by positivity) hyerr
  refine hnorm.trans ?_
  have hCS := abs_dotProduct_abs_le v b
  have hvv : ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = v ⬝ᵥ v := (dotProduct_self_eq_norm_sq v).symm
  have hb0 : 0 ≤ ‖(toLp 2 b : EuclideanSpace ℝ ι)‖ := norm_nonneg _
  have hv0 : 0 ≤ ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ := norm_nonneg _
  have hβv : |β| * ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 ≤ 2 := by rw [hvv]; exact hP
  have hug : m.u ≤ γ := (le_gamma_one hu0 hu1).trans (gamma_mono hu0 (by omega) hK)
  have h1 : γ * (|β| * (|v| ⬝ᵥ |b|)) * ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ ≤
      γ * (|β| * ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2) * ‖(toLp 2 b : EuclideanSpace ℝ ι)‖ := by
    have : |β| * (|v| ⬝ᵥ |b|) * ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ ≤
        |β| * ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 * ‖(toLp 2 b : EuclideanSpace ℝ ι)‖ := by
      have := mul_le_mul_of_nonneg_left hCS (abs_nonneg β)
      nlinarith [mul_le_mul_of_nonneg_right this hv0]
    nlinarith
  have h2 : γ * (|β| * ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2) * ‖(toLp 2 b : EuclideanSpace ℝ ι)‖
      ≤ γ * 2 * ‖(toLp 2 b : EuclideanSpace ℝ ι)‖ := by
    have := mul_le_mul_of_nonneg_left hβv hγ0
    exact mul_le_mul_of_nonneg_right this hb0
  nlinarith [mul_le_mul_of_nonneg_right hug hb0]

/-- **[higham2002accuracy] Lemma 19.2.** -/
theorem norm_sub_le_of_roundsHouseholderApply {m : RoundingModel ℝ} {k : ℕ}
    (hcard : ((3 * k + Fintype.card ι + 3 : ℕ) : ℝ) * m.u < 1) {β βhat : ℝ} {v vhat : ι → ℝ}
    (hβ : IsRelPert m.u k β βhat) (hv : ∀ i, IsRelPert m.u k (v i) (vhat i))
    (hP : |β| * (v ⬝ᵥ v) ≤ 2) {b y : ι → ℝ} (h : RoundsHouseholderApply m βhat vhat b y) :
    ‖(toLp 2 (y - (1 - β • vecMulVec v v) *ᵥ b) : EuclideanSpace ℝ ι)‖ ≤
      3 * gamma m.u (3 * k + Fintype.card ι + 3) * ‖(toLp 2 b : EuclideanSpace ℝ ι)‖ := by
  obtain ⟨s, t, w, hs, ht, hw, hy⟩ := h
  set n := Fintype.card ι with hn_def
  have hu0 := m.u_nonneg
  have hlt : ∀ j : ℕ, j ≤ 3 * k + n + 3 → ((j : ℕ) : ℝ) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hu0).trans_lt hcard
  have hu1 : m.u < 1 := by simpa using hlt 1 (by omega)
  -- the rounding errors, one by one
  obtain ⟨dx, hdx, hseq⟩ := exists_roundsDot_eq_dotProduct_add hu1 (hlt n (by omega)) hs
  obtain ⟨δ₁, hδ₁, hteq⟩ := ht.exists_delta
  choose δ₂ hδ₂ hweq using fun i => (hw i).exists_delta
  -- the coefficients of `w i = ∑ j, c i j * b j` are relative perturbations of `β v i v j`
  have hβ' : IsRelPert m.u (k + 1) β (βhat * (1 + δ₁)) :=
    hβ.mul_one_add hu0 hu1 (hlt _ (by omega)) hδ₁
  have hvi' : ∀ i, IsRelPert m.u (k + 1) (v i) (vhat i * (1 + δ₂ i)) := fun i =>
    (hv i).mul_one_add hu0 hu1 (hlt _ (by omega)) (hδ₂ i)
  have hvj' : ∀ j, IsRelPert m.u (k + n) (v j) (vhat j + dx j) := fun j =>
    (hv j).trans hu0 (hlt _ (by omega))
      (isRelPert_of_abs_sub_le (gamma_nonneg hu0 (hlt n (by omega)))
        (by rw [add_sub_cancel_left]; exact hdx j))
  have hc : ∀ i j, IsRelPert m.u (3 * k + n + 2) (β * v i * v j)
      (βhat * (1 + δ₁) * (vhat i * (1 + δ₂ i)) * (vhat j + dx j)) := fun i j => by
    have h1 := hβ'.mul hu0 (k := k + 1) (j := k + 1) (hlt _ (by omega)) (hvi' i)
    have h2 := h1.mul hu0 (k := k + 1 + (k + 1)) (j := k + n) (hlt _ (by omega)) (hvj' j)
    rwa [show k + 1 + (k + 1) + (k + n) = 3 * k + n + 2 by ring] at h2
  have hwi : ∀ i, w i = ∑ j, βhat * (1 + δ₁) * (vhat i * (1 + δ₂ i)) * (vhat j + dx j) * b j := by
    intro i
    rw [hweq i, hteq, hseq, dotProduct]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.add_apply]
    ring
  have := norm_sub_le_of_forall_rounds_sub_sum (K := 3 * k + n + 2) (hlt _ (by omega)) hc hwi
    hy hP
  rwa [show 3 * k + n + 2 + 1 = 3 * k + n + 3 by ring] at this

/-- The update `y = b - (β v)(vᵀ b)` in [golub2013matrix]'s association (§5.1.4:
`P A = A - (β v)(vᵀ A)`, the scaled vector `β v` formed once), with one rounding per operation
and the inner product as `RoundsDot`. Compare `RoundsHouseholderApply` (`y = b - v (β (vᵀ b))`).
The row application `A - (A v)(β v)ᵀ` is the same relation on each row. -/
def RoundsHouseholderApplyScaled (m : RoundingModel ℝ) (β : ℝ) (v b y : ι → ℝ) : Prop :=
  ∃ (s : ℝ) (w : ι → ℝ), RoundsDot m v b s ∧ (∀ i, m.Rounds (β * v i) (w i)) ∧
    ∀ i, ∃ t, m.Rounds (w i * s) t ∧ m.Rounds (b i - t) (y i)

/-- **[higham2002accuracy] Lemma 19.2 for the scaled association** `b - (β v)(vᵀ b)`, with the
constant of `norm_sub_le_of_roundsHouseholderApply`: the two associations give coefficients
`c_ij` of the same order `3k + n + 2` and share `norm_sub_le_of_forall_rounds_sub_sum`. -/
theorem norm_sub_le_of_roundsHouseholderApplyScaled {m : RoundingModel ℝ} {k : ℕ}
    (hcard : ((3 * k + Fintype.card ι + 3 : ℕ) : ℝ) * m.u < 1) {β βhat : ℝ} {v vhat : ι → ℝ}
    (hβ : IsRelPert m.u k β βhat) (hv : ∀ i, IsRelPert m.u k (v i) (vhat i))
    (hP : |β| * (v ⬝ᵥ v) ≤ 2) {b y : ι → ℝ} (h : RoundsHouseholderApplyScaled m βhat vhat b y) :
    ‖(toLp 2 (y - (1 - β • vecMulVec v v) *ᵥ b) : EuclideanSpace ℝ ι)‖ ≤
      3 * gamma m.u (3 * k + Fintype.card ι + 3) * ‖(toLp 2 b : EuclideanSpace ℝ ι)‖ := by
  obtain ⟨s, w, hs, hw, ht⟩ := h
  choose t ht hy using ht
  set n := Fintype.card ι with hn_def
  have hu0 := m.u_nonneg
  have hlt : ∀ j : ℕ, j ≤ 3 * k + n + 3 → ((j : ℕ) : ℝ) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hu0).trans_lt hcard
  have hu1 : m.u < 1 := by simpa using hlt 1 (by omega)
  obtain ⟨dx, hdx, hseq⟩ := exists_roundsDot_eq_dotProduct_add hu1 (hlt n (by omega)) hs
  choose δ₂ hδ₂ hweq using fun i => (hw i).exists_delta
  choose δ₁ hδ₁ hteq using fun i => (ht i).exists_delta
  have hvj' : ∀ j, IsRelPert m.u (k + n) (v j) (vhat j + dx j) := fun j =>
    (hv j).trans hu0 (hlt _ (by omega))
      (isRelPert_of_abs_sub_le (gamma_nonneg hu0 (hlt n (by omega)))
        (by rw [add_sub_cancel_left]; exact hdx j))
  have hc : ∀ i j, IsRelPert m.u (3 * k + n + 2) (β * v i * v j)
      (βhat * vhat i * (1 + δ₂ i) * (1 + δ₁ i) * (vhat j + dx j)) := fun i j => by
    have h1 := hβ.mul hu0 (k := k) (j := k) (hlt _ (by omega)) (hv i)
    have h2 := h1.mul_one_add hu0 hu1 (hlt (k + k + 1) (by omega)) (hδ₂ i)
    have h3 := h2.mul_one_add hu0 hu1 (hlt (k + k + 1 + 1) (by omega)) (hδ₁ i)
    have h4 := h3.mul hu0 (k := k + k + 1 + 1) (j := k + n) (hlt _ (by omega)) (hvj' j)
    rwa [show k + k + 1 + 1 + (k + n) = 3 * k + n + 2 by ring] at h4
  have hti : ∀ i, t i = ∑ j, βhat * vhat i * (1 + δ₂ i) * (1 + δ₁ i) * (vhat j + dx j) * b j := by
    intro i
    rw [hteq i, hweq i, hseq, dotProduct]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.add_apply]
    ring
  have := norm_sub_le_of_forall_rounds_sub_sum (K := 3 * k + n + 2) (hlt _ (by omega)) hc hti
    hy hP
  rwa [show 3 * k + n + 2 + 1 = 3 * k + n + 3 by ring] at this


/-! ### Orthogonal transformations of vectors -/

/-- An orthogonal matrix preserves the Euclidean norm. -/
theorem norm_toLp_mulVec_of_mem_orthogonalGroup {Q : Matrix ι ι ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup ι ℝ) (x : ι → ℝ) :
    ‖(toLp 2 (Q *ᵥ x) : EuclideanSpace ℝ ι)‖ = ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ :=
  norm_toLp_mulVec_of_mem_unitaryGroup hQ x

/-- `Q (Qᵀ x) = x` for an orthogonal `Q`. -/
theorem mulVec_transpose_mulVec_of_mem_orthogonalGroup {Q : Matrix ι ι ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup ι ℝ) (x : ι → ℝ) : Q *ᵥ (Qᵀ *ᵥ x) = x := by
  rw [mulVec_mulVec, (mem_orthogonalGroup_iff _ _).1 hQ, one_mulVec]

/-- The transpose of an orthogonal matrix is orthogonal. -/
theorem transpose_mem_orthogonalGroup {Q : Matrix ι ι ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup ι ℝ) : Qᵀ ∈ Matrix.orthogonalGroup ι ℝ := by
  rw [mem_orthogonalGroup_iff, transpose_transpose]
  exact (mem_orthogonalGroup_iff' _ _).1 hQ

/-- `(1 + ε)^r - 1 ≤ γ_r(ε) = r ε / (1 - r ε)` for `0 ≤ ε` and `r ε < 1`
([higham2002accuracy] Lemma 3.1 with all the `δ_i` equal to `ε`). -/
theorem one_add_pow_sub_one_le_gamma {ε : ℝ} (hε : 0 ≤ ε) {r : ℕ} (hr : (r : ℝ) * ε < 1) :
    (1 + ε) ^ r - 1 ≤ gamma ε r := by
  have h := abs_prod_one_add_sub_one_le_gamma (u := ε) hε (n := r) hr (δ := fun _ => ε)
    (fun _ => le_of_eq (abs_of_nonneg hε)) (ρ := fun _ => 1) (fun _ => Or.inl rfl)
  simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact (le_abs_self _).trans h

/-! ### [higham2002accuracy] Lemma 19.3: accumulation -/

/-- **A sequence of nearly exact orthogonal transformations of a vector is an exact one of a
nearby vector** ([higham2002accuracy] Lemma 19.3, the core): if `P_k` are orthogonal and
`‖x_{k+1} - P_k x_k‖₂ ≤ ε ‖x_k‖₂` for `k < r`, then `x_r = P_{r-1} ⋯ P_0 (x_0 + Δx)` with
`‖Δx‖₂ ≤ ((1 + ε)^r - 1) ‖x_0‖₂`. -/
theorem exists_eq_prodRev_mulVec_add {P : ℕ → Matrix ι ι ℝ}
    (hP : ∀ k, P k ∈ Matrix.orthogonalGroup ι ℝ) {x : ℕ → ι → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (r : ℕ)
    (hx : ∀ k, k < r → ‖(toLp 2 (x (k + 1) - P k *ᵥ x k) : EuclideanSpace ℝ ι)‖ ≤
      ε * ‖(toLp 2 (x k) : EuclideanSpace ℝ ι)‖) :
    ∃ dx : ι → ℝ, x r = prodRev P r *ᵥ (x 0 + dx) ∧
      ‖(toLp 2 dx : EuclideanSpace ℝ ι)‖ ≤
        ((1 + ε) ^ r - 1) * ‖(toLp 2 (x 0) : EuclideanSpace ℝ ι)‖ := by
  induction r with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨dx, hxr, hdx⟩ := ih fun k hk => hx k (by omega)
    have hQ := prodRev_mem_orthogonalGroup hP (r + 1)
    set e := x (r + 1) - P r *ᵥ x r with he
    have hx0 : 0 ≤ ‖(toLp 2 (x 0) : EuclideanSpace ℝ ι)‖ := norm_nonneg _
    have hpow : 0 ≤ (1 + ε) ^ r := by positivity
    refine ⟨dx + (prodRev P (r + 1))ᵀ *ᵥ e, ?_, ?_⟩
    · calc x (r + 1) = P r *ᵥ x r + e := by rw [he]; abel
        _ = P r *ᵥ (prodRev P r *ᵥ (x 0 + dx)) +
            prodRev P (r + 1) *ᵥ ((prodRev P (r + 1))ᵀ *ᵥ e) := by
          rw [hxr, mulVec_transpose_mulVec_of_mem_orthogonalGroup hQ]
        _ = prodRev P (r + 1) *ᵥ (x 0 + dx) +
            prodRev P (r + 1) *ᵥ ((prodRev P (r + 1))ᵀ *ᵥ e) := by
          rw [mulVec_mulVec]
          rfl
        _ = _ := by
          rw [← mulVec_add]
          congr 1
          abel
    · have h1 : ‖(toLp 2 ((prodRev P (r + 1))ᵀ *ᵥ e) : EuclideanSpace ℝ ι)‖ ≤
          ε * ‖(toLp 2 (x r) : EuclideanSpace ℝ ι)‖ := by
        rw [norm_toLp_mulVec_of_mem_orthogonalGroup (transpose_mem_orthogonalGroup hQ)]
        exact hx r (Nat.lt_succ_self r)
      have h2 : ‖(toLp 2 (x r) : EuclideanSpace ℝ ι)‖ ≤
          (1 + ε) ^ r * ‖(toLp 2 (x 0) : EuclideanSpace ℝ ι)‖ := by
        rw [hxr, norm_toLp_mulVec_of_mem_orthogonalGroup (prodRev_mem_orthogonalGroup hP r),
          WithLp.toLp_add]
        refine (norm_add_le _ _).trans ?_
        linarith
      rw [WithLp.toLp_add]
      refine (norm_add_le _ _).trans ?_
      have h3 : ε * ‖(toLp 2 (x r) : EuclideanSpace ℝ ι)‖ ≤
          ε * ((1 + ε) ^ r * ‖(toLp 2 (x 0) : EuclideanSpace ℝ ι)‖) :=
        mul_le_mul_of_nonneg_left h2 hε
      have h4 : ((1 + ε) ^ (r + 1) - 1) = ((1 + ε) ^ r - 1) + ε * (1 + ε) ^ r := by ring
      rw [h4]
      nlinarith

/-- **[higham2002accuracy] Lemma 19.3, vector form with the constant `r γ̃`**: under
`r ε < 1`, `‖Δx‖₂ ≤ (r ε / (1 - r ε)) ‖x_0‖₂`. -/
theorem exists_eq_prodRev_mulVec_add_gamma {P : ℕ → Matrix ι ι ℝ}
    (hP : ∀ k, P k ∈ Matrix.orthogonalGroup ι ℝ) {x : ℕ → ι → ℝ} {ε : ℝ} (hε : 0 ≤ ε) {r : ℕ}
    (hx : ∀ k, k < r → ‖(toLp 2 (x (k + 1) - P k *ᵥ x k) : EuclideanSpace ℝ ι)‖ ≤
      ε * ‖(toLp 2 (x k) : EuclideanSpace ℝ ι)‖) (hr : (r : ℝ) * ε < 1) :
    ∃ dx : ι → ℝ, x r = prodRev P r *ᵥ (x 0 + dx) ∧
      ‖(toLp 2 dx : EuclideanSpace ℝ ι)‖ ≤ gamma ε r * ‖(toLp 2 (x 0) : EuclideanSpace ℝ ι)‖ := by
  obtain ⟨dx, h1, h2⟩ := exists_eq_prodRev_mulVec_add hP hε r hx
  exact ⟨dx, h1, h2.trans (mul_le_mul_of_nonneg_right (one_add_pow_sub_one_le_gamma hε hr)
    (norm_nonneg _))⟩

section Matrix

open scoped Matrix.Norms.Frobenius

variable {κ : Type*}

/-- **[higham2002accuracy] Lemma 19.3, matrix form**: if each column of `A_{k+1}` is within
`ε` (relative, Euclidean) of `P_k` applied to the corresponding column of `A_k`, then
`A_r = P_{r-1} ⋯ P_0 (A_0 + ΔA)` with `‖Δa_j‖₂ ≤ ((1 + ε)^r - 1) ‖a_j‖₂` for every column. -/
theorem exists_eq_prodRev_mul_add {P : ℕ → Matrix ι ι ℝ}
    (hP : ∀ k, P k ∈ Matrix.orthogonalGroup ι ℝ) {A : ℕ → Matrix ι κ ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (r : ℕ) (hA : ∀ k, k < r → ∀ j,
      ‖(toLp 2 ((A (k + 1) - P k * A k).col j) : EuclideanSpace ℝ ι)‖ ≤
        ε * ‖(toLp 2 ((A k).col j) : EuclideanSpace ℝ ι)‖) :
    ∃ ΔA : Matrix ι κ ℝ, A r = prodRev P r * (A 0 + ΔA) ∧
      ∀ j, ‖(toLp 2 (ΔA.col j) : EuclideanSpace ℝ ι)‖ ≤
        ((1 + ε) ^ r - 1) * ‖(toLp 2 ((A 0).col j) : EuclideanSpace ℝ ι)‖ := by
  have hcol : ∀ j, ∃ dx : ι → ℝ, (A r).col j = prodRev P r *ᵥ ((A 0).col j + dx) ∧
      ‖(toLp 2 dx : EuclideanSpace ℝ ι)‖ ≤
        ((1 + ε) ^ r - 1) * ‖(toLp 2 ((A 0).col j) : EuclideanSpace ℝ ι)‖ := fun j =>
    exists_eq_prodRev_mulVec_add hP hε (x := fun k => (A k).col j) r fun k hk => by
      have := hA k hk j
      rwa [show (A (k + 1) - P k * A k).col j = (A (k + 1)).col j - P k *ᵥ (A k).col j from by
        ext i; simp [col_apply, mul_apply, mulVec, dotProduct]] at this
  choose dx hdx hdxn using hcol
  refine ⟨Matrix.of fun i j => dx j i, ?_, fun j => hdxn j⟩
  ext i j
  have := congrFun (hdx j) i
  rw [col_apply] at this
  rw [this, mul_apply, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [col_apply]


/-- Orthogonal equivalence preserves the Frobenius norm. -/
theorem frobenius_norm_orthogonal_mul_mul_orthogonal [Fintype κ] [DecidableEq κ]
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}
    (hU : U ∈ Matrix.orthogonalGroup ι ℝ) (A : Matrix ι κ ℝ)
    (hV : V ∈ Matrix.orthogonalGroup κ ℝ) : ‖U * A * V‖ = ‖A‖ :=
  frobenius_norm_unitary_mul_mul_unitary hU A hV

/-- `Q (Qᵀ A) = A` for an orthogonal `Q`. -/
theorem mul_transpose_mul_of_mem_orthogonalGroup {Q : Matrix ι ι ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup ι ℝ) (A : Matrix ι κ ℝ) : Q * (Qᵀ * A) = A := by
  rw [← Matrix.mul_assoc, (mem_orthogonalGroup_iff _ _).1 hQ, Matrix.one_mul]

/-- `(A Qᵀ) Q = A` for an orthogonal `Q`. -/
theorem mul_transpose_mul_of_mem_orthogonalGroup' {Q : Matrix ι ι ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup ι ℝ) (A : Matrix κ ι ℝ) : A * Qᵀ * Q = A := by
  rw [Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hQ, Matrix.mul_one]

variable [Fintype κ] [DecidableEq κ]

/-- **Two-sided accumulation for rectangular matrices** ([higham2002accuracy] §19.10, the
two-sided analogue of Lemma 19.3, in the Frobenius norm): if `L_k` (on the rows) and `R_k` (on
the columns) are orthogonal and `‖A_{k+1} - L_k A_k R_k‖_F ≤ ε ‖A_k‖_F` for `k < r`, then
`A_r = (L_{r-1} ⋯ L_0) (A_0 + E) (R_0 ⋯ R_{r-1})` with `‖E‖_F ≤ ((1 + ε)^r - 1) ‖A_0‖_F`.
[golub2013matrix] (5.1.11) is an instance. -/
theorem exists_eq_prodRev_mul_add_mul_prodFwd_rect {L : ℕ → Matrix ι ι ℝ}
    {R : ℕ → Matrix κ κ ℝ} (hL : ∀ k, L k ∈ Matrix.orthogonalGroup ι ℝ)
    (hR : ∀ k, R k ∈ Matrix.orthogonalGroup κ ℝ) {A : ℕ → Matrix ι κ ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (r : ℕ) (hA : ∀ k, k < r → ‖A (k + 1) - L k * A k * R k‖ ≤ ε * ‖A k‖) :
    ∃ E : Matrix ι κ ℝ, A r = prodRev L r * (A 0 + E) * prodFwd R r ∧
      ‖E‖ ≤ ((1 + ε) ^ r - 1) * ‖A 0‖ := by
  induction r with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨E, hAr, hE⟩ := ih fun k hk => hA k (by omega)
    have hLr := prodRev_mem_orthogonalGroup hL (r + 1)
    have hRr := prodFwd_mem_orthogonalGroup hR (r + 1)
    set F := A (r + 1) - L r * A r * R r with hF
    have hA0 : 0 ≤ ‖A 0‖ := norm_nonneg _
    have hpow : 0 ≤ (1 + ε) ^ r := by positivity
    refine ⟨E + (prodRev L (r + 1))ᵀ * F * (prodFwd R (r + 1))ᵀ, ?_, ?_⟩
    · have hFeq : prodRev L (r + 1) * ((prodRev L (r + 1))ᵀ * F * (prodFwd R (r + 1))ᵀ) *
          prodFwd R (r + 1) = F := by
        simp only [Matrix.mul_assoc]
        rw [(mem_orthogonalGroup_iff' _ _).1 hRr, Matrix.mul_one,
          mul_transpose_mul_of_mem_orthogonalGroup hLr]
      calc A (r + 1) = L r * A r * R r + F := by rw [hF]; abel
        _ = L r * (prodRev L r * (A 0 + E) * prodFwd R r) * R r + F := by rw [hAr]
        _ = prodRev L (r + 1) * (A 0 + E) * prodFwd R (r + 1) +
            prodRev L (r + 1) * ((prodRev L (r + 1))ᵀ * F * (prodFwd R (r + 1))ᵀ) *
              prodFwd R (r + 1) := by
          rw [hFeq, prodRev_succ, prodFwd_succ]
          simp only [Matrix.mul_assoc]
        _ = _ := by
          simp only [Matrix.mul_add, Matrix.add_mul]
          abel
    · have h1 : ‖(prodRev L (r + 1))ᵀ * F * (prodFwd R (r + 1))ᵀ‖ ≤ ε * ‖A r‖ := by
        rw [frobenius_norm_orthogonal_mul_mul_orthogonal (transpose_mem_orthogonalGroup hLr) _
          (transpose_mem_orthogonalGroup hRr)]
        exact hA r (Nat.lt_succ_self r)
      have h2 : ‖A r‖ ≤ (1 + ε) ^ r * ‖A 0‖ := by
        rw [hAr, frobenius_norm_orthogonal_mul_mul_orthogonal (prodRev_mem_orthogonalGroup hL r)
          _ (prodFwd_mem_orthogonalGroup hR r)]
        refine (norm_add_le _ _).trans ?_
        linarith
      refine (norm_add_le _ _).trans ?_
      have h3 : ε * ‖A r‖ ≤ ε * ((1 + ε) ^ r * ‖A 0‖) := mul_le_mul_of_nonneg_left h2 hε
      have h4 : ((1 + ε) ^ (r + 1) - 1) = ((1 + ε) ^ r - 1) + ε * (1 + ε) ^ r := by ring
      rw [h4]
      nlinarith

/-- **Two-sided accumulation** ([higham2002accuracy] §19.10, the two-sided analogue of Lemma
19.3, in the Frobenius norm): if `L_k`, `R_k` are orthogonal and
`‖A_{k+1} - L_k A_k R_k‖_F ≤ ε ‖A_k‖_F` for `k < r`, then
`A_r = (L_{r-1} ⋯ L_0) (A_0 + E) (R_0 ⋯ R_{r-1})` with `‖E‖_F ≤ ((1 + ε)^r - 1) ‖A_0‖_F`: the
square case of `exists_eq_prodRev_mul_add_mul_prodFwd_rect`. -/
theorem exists_eq_prodRev_mul_add_mul_prodFwd {L R : ℕ → Matrix ι ι ℝ}
    (hL : ∀ k, L k ∈ Matrix.orthogonalGroup ι ℝ) (hR : ∀ k, R k ∈ Matrix.orthogonalGroup ι ℝ)
    {A : ℕ → Matrix ι ι ℝ} {ε : ℝ} (hε : 0 ≤ ε) (r : ℕ)
    (hA : ∀ k, k < r → ‖A (k + 1) - L k * A k * R k‖ ≤ ε * ‖A k‖) :
    ∃ E : Matrix ι ι ℝ, A r = prodRev L r * (A 0 + E) * prodFwd R r ∧
      ‖E‖ ≤ ((1 + ε) ^ r - 1) * ‖A 0‖ :=
  exists_eq_prodRev_mul_add_mul_prodFwd_rect hL hR hε r hA

/-- **Two-sided accumulation by symmetric orthogonal transformations** (reflectors): with
`L_k = R_k = P_k` symmetric and orthogonal, `A_r = Qᵀ (A_0 + E) Q` for the orthogonal
`Q = P_0 ⋯ P_{r-1}`. -/
theorem exists_eq_transpose_mul_add_mul_prodFwd {P : ℕ → Matrix ι ι ℝ}
    (hP : ∀ k, P k ∈ Matrix.orthogonalGroup ι ℝ) (hPs : ∀ k, (P k)ᵀ = P k)
    {A : ℕ → Matrix ι ι ℝ} {ε : ℝ} (hε : 0 ≤ ε) (r : ℕ)
    (hA : ∀ k, k < r → ‖A (k + 1) - P k * A k * P k‖ ≤ ε * ‖A k‖) :
    ∃ E : Matrix ι ι ℝ, A r = (prodFwd P r)ᵀ * (A 0 + E) * prodFwd P r ∧
      ‖E‖ ≤ ((1 + ε) ^ r - 1) * ‖A 0‖ := by
  obtain ⟨E, h1, h2⟩ := exists_eq_prodRev_mul_add_mul_prodFwd hP hP hε r hA
  refine ⟨E, ?_, h2⟩
  rw [h1, transpose_prodFwd]
  congr 2
  exact congrArg (fun Q => prodRev Q r) (funext hPs).symm

/-- **Two-sided accumulation with the reflector of each step chosen** ([higham2002accuracy]
Lemma 19.3, two-sided, §19.10): if every step `k < r` has an exact symmetric orthogonal `P` with
`‖A_{k+1} - P A_k P‖_F ≤ ε ‖A_k‖_F`, then `A_r = Qᵀ (A_0 + E) Q` for an orthogonal `Q` and
`‖E‖_F ≤ ((1 + ε)^r - 1) ‖A_0‖_F`. The lemma every Householder reduction ends with, once its step
bound is proved. -/
theorem exists_eq_transpose_mul_add_mul_of_forall_step {A : ℕ → Matrix ι ι ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (r : ℕ)
    (h : ∀ k, k < r → ∃ P ∈ Matrix.orthogonalGroup ι ℝ, Pᵀ = P ∧
      ‖A (k + 1) - P * A k * P‖ ≤ ε * ‖A k‖) :
    ∃ Q ∈ Matrix.orthogonalGroup ι ℝ, ∃ E : Matrix ι ι ℝ,
      A r = Qᵀ * (A 0 + E) * Q ∧ ‖E‖ ≤ ((1 + ε) ^ r - 1) * ‖A 0‖ := by
  have h' : ∀ k, ∃ P ∈ Matrix.orthogonalGroup ι ℝ, Pᵀ = P ∧
      (k < r → ‖A (k + 1) - P * A k * P‖ ≤ ε * ‖A k‖) := fun k => by
    by_cases hk : k < r
    · obtain ⟨P, hP, hPs, hb⟩ := h k hk
      exact ⟨P, hP, hPs, fun _ => hb⟩
    · exact ⟨1, one_mem _, by simp, fun h => absurd h hk⟩
  choose P hP hPs hb using h'
  obtain ⟨E, hE, hEn⟩ := exists_eq_transpose_mul_add_mul_prodFwd hP hPs hε r hb
  exact ⟨prodFwd P r, prodFwd_mem_orthogonalGroup hP r, E, hE, hEn⟩

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- `(B - M A).col q = B.col q - M (A.col q)`. -/
theorem col_sub_mul (B : Matrix ι κ ℝ) (M : Matrix ι ι ℝ) (A : Matrix ι κ ℝ) (q : κ) :
    (B - M * A).col q = B.col q - M *ᵥ A.col q := by
  ext i
  simp [col_apply, mul_apply, mulVec, dotProduct]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- `(B - A M).row r = B.row r - Mᵀ (A.row r)`. -/
theorem row_sub_mul (B : Matrix κ ι ℝ) (A : Matrix κ ι ℝ) (M : Matrix ι ι ℝ) (r : κ) :
    (B - A * M).row r = B.row r - Mᵀ *ᵥ A.row r := by
  ext j
  simp only [row_apply, Matrix.sub_apply, Pi.sub_apply]
  rw [show (A * M) r j = (A r ᵥ* M) j from rfl, ← mulVec_transpose]
  rfl

omit [DecidableEq κ] in
/-- **The left application of a computed reflector to a matrix**, [golub2013matrix] §5.1.4's
premultiplication `A - (β v)(vᵀ A)`: if every column of `B` is a computed
`RoundsHouseholderApplyScaled m β̂ v̂` of the corresponding column of `A`, then columnwise
`‖(B - P A)_q‖₂ ≤ ε ‖a_q‖₂` and `‖B - P A‖_F ≤ ε ‖A‖_F` for `P = 1 - β v vᵀ` and
`ε = 3 γ_{3k+n+3}`. -/
theorem frobenius_norm_sub_le_of_forall_roundsHouseholderApplyScaled_col {m : RoundingModel ℝ}
    {k : ℕ} (hcard : ((3 * k + Fintype.card ι + 3 : ℕ) : ℝ) * m.u < 1) {β βhat : ℝ}
    {v vhat : ι → ℝ} (hβ : IsRelPert m.u k β βhat) (hv : ∀ i, IsRelPert m.u k (v i) (vhat i))
    (hP : |β| * (v ⬝ᵥ v) ≤ 2) {A B : Matrix ι κ ℝ}
    (h : ∀ q, RoundsHouseholderApplyScaled m βhat vhat (A.col q) (B.col q)) :
    (∀ q, ‖(toLp 2 ((B - (1 - β • vecMulVec v v) * A).col q) : EuclideanSpace ℝ ι)‖ ≤
      3 * gamma m.u (3 * k + Fintype.card ι + 3) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ ι)‖) ∧
    ‖B - (1 - β • vecMulVec v v) * A‖ ≤ 3 * gamma m.u (3 * k + Fintype.card ι + 3) * ‖A‖ := by
  have hcol : ∀ q, ‖(toLp 2 ((B - (1 - β • vecMulVec v v) * A).col q) : EuclideanSpace ℝ ι)‖ ≤
      3 * gamma m.u (3 * k + Fintype.card ι + 3) *
        ‖(toLp 2 (A.col q) : EuclideanSpace ℝ ι)‖ := fun q => by
    rw [col_sub_mul]
    exact norm_sub_le_of_roundsHouseholderApplyScaled hcard hβ hv hP (h q)
  exact ⟨hcol, frobenius_norm_le_of_forall_col_le
    (by have := gamma_nonneg m.u_nonneg hcard; positivity) hcol⟩

omit [DecidableEq κ] in
/-- **The right application of a computed reflector to a matrix**, [golub2013matrix] §5.1.4's
postmultiplication `A - (A v)(β v)ᵀ`: if every row of `B` is a computed
`RoundsHouseholderApplyScaled m β̂ v̂` of the corresponding row of `A`, then rowwise
`‖(B - A P)_r‖₂ ≤ ε ‖a_r‖₂` and `‖B - A P‖_F ≤ ε ‖A‖_F` for `P = 1 - β v vᵀ` (symmetric, so a
row of `A P` is `P` applied to the row) and `ε = 3 γ_{3k+n+3}`. -/
theorem frobenius_norm_sub_le_of_forall_roundsHouseholderApplyScaled_row {m : RoundingModel ℝ}
    {k : ℕ} (hcard : ((3 * k + Fintype.card ι + 3 : ℕ) : ℝ) * m.u < 1) {β βhat : ℝ}
    {v vhat : ι → ℝ} (hβ : IsRelPert m.u k β βhat) (hv : ∀ i, IsRelPert m.u k (v i) (vhat i))
    (hP : |β| * (v ⬝ᵥ v) ≤ 2) {A B : Matrix κ ι ℝ}
    (h : ∀ r, RoundsHouseholderApplyScaled m βhat vhat (A.row r) (B.row r)) :
    (∀ r, ‖(toLp 2 ((B - A * (1 - β • vecMulVec v v)).row r) : EuclideanSpace ℝ ι)‖ ≤
      3 * gamma m.u (3 * k + Fintype.card ι + 3) * ‖(toLp 2 (A.row r) : EuclideanSpace ℝ ι)‖) ∧
    ‖B - A * (1 - β • vecMulVec v v)‖ ≤ 3 * gamma m.u (3 * k + Fintype.card ι + 3) * ‖A‖ := by
  have hrow : ∀ r, ‖(toLp 2 ((B - A * (1 - β • vecMulVec v v)).row r) : EuclideanSpace ℝ ι)‖ ≤
      3 * gamma m.u (3 * k + Fintype.card ι + 3) *
        ‖(toLp 2 (A.row r) : EuclideanSpace ℝ ι)‖ := fun r => by
    rw [row_sub_mul, transpose_one_sub_smul_vecMulVec]
    exact norm_sub_le_of_roundsHouseholderApplyScaled hcard hβ hv hP (h r)
  exact ⟨hrow, frobenius_norm_le_of_forall_row_le
    (by have := gamma_nonneg m.u_nonneg hcard; positivity) hrow⟩

end Matrix

/-! ### The Householder reduction to Hessenberg form in floating-point arithmetic -/

section Hessenberg

open scoped Matrix.Norms.Frobenius

variable {N : ℕ}

/-- The tail of column `k` of `A` below the pivot `k + 1`: the vector `x` from which the
reflector `P_(k)` of the Householder reduction is built ([quarteroni2000numerical] (5.45)). -/
def hessenbergTailCol (A : Matrix (Fin N) (Fin N) ℝ) {k : ℕ} (hk : k + 1 < N) : Fin N → ℝ :=
  fun i => if k + 1 ≤ (i : ℕ) then A i ⟨k, by omega⟩ else 0

/-- The reflector of step `k` is the reflector of the unit axis of the tail of column `k`. -/
theorem hessenbergReflector_eq_householder (A : Matrix (Fin N) (Fin N) ℝ) {k : ℕ}
    (hk : k + 1 < N) :
    hessenbergReflector A k =
      householder (householderVec (hessenbergTailCol A hk) ⟨k + 1, hk⟩) := by
  rw [hessenbergReflector_of_lt A (by omega), householderTail_of_lt _ hk]
  rfl

/-- The reflector of step `k` is symmetric. -/
theorem transpose_hessenbergReflector (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    (hessenbergReflector A k)ᵀ = hessenbergReflector A k := by
  have h := (isHermitian_hessenbergReflector A k).eq
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- **One step of the Householder reduction to Hessenberg form in floating-point arithmetic**
([quarteroni2000numerical] §5.6.2, Program 29, step `k`; [higham2002accuracy] Theorem 19.4's
conventions). `RoundsHessenbergStep m hk A B` says that `B` is an admissible computed value of
`P_(k)ᵀ A P_(k)`: the reflector data `(v̂, β̂)` are computed from the tail of column `k` of `A`
below the pivot `k + 1` (`RoundsHouseholderVector`); the columns `j ≥ k` of `A` are updated by
`RoundsHouseholderApply`, the entries of column `k` in the rows `≥ k + 2` — the ones the
reflector annihilates — being set to zero explicitly, and the columns `j < k` (already zero
below the first subdiagonal, so fixed by the reflector) are left alone, giving `C`; then every
row of `C` is updated by `RoundsHouseholderApply`, its entries in the columns `≤ k`, which the
reflector fixes exactly, being left alone. -/
def RoundsHessenbergStep (m : RoundingModel ℝ) {k : ℕ} (hk : k + 1 < N)
    (A B : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ (vhat : Fin N → ℝ) (βhat : ℝ) (C : Matrix (Fin N) (Fin N) ℝ),
    RoundsHouseholderVector m (hessenbergTailCol A hk) ⟨k + 1, hk⟩ vhat βhat ∧
    (∀ j : Fin N, (j : ℕ) < k → C.col j = A.col j) ∧
    (∀ j : Fin N, k ≤ (j : ℕ) → ∃ y, RoundsHouseholderApply m βhat vhat (A.col j) y ∧
      ∀ i, C i j = if (j : ℕ) = k ∧ k + 2 ≤ (i : ℕ) then 0 else y i) ∧
    ∀ i : Fin N, ∃ z, RoundsHouseholderApply m βhat vhat (C.row i) z ∧
      ∀ j, B i j = if (j : ℕ) ≤ k then C i j else z j

/-- **The Householder reduction to Hessenberg form in floating-point arithmetic**
([quarteroni2000numerical] §5.6.2, Program 29): `Â_0 = A` and `Â_{k+1}` is a computed step
`RoundsHessenbergStep` from `Â_k`, for the `n - 2` steps `k < n - 2`; the computed Hessenberg
matrix is `Ĥ = Â_{n-2}`. -/
def RoundsHessenbergReduce (m : RoundingModel ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (Ahat : ℕ → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  Ahat 0 = A ∧ ∀ k (hk : k < N - 2),
    RoundsHessenbergStep m (show k + 1 < N by omega) (Ahat k) (Ahat (k + 1))

/-- A computed step keeps the Hessenberg structure of the columns already reduced and adds
column `k`: if `A` vanishes below the first subdiagonal in the columns `j < k`, so does `B` in
the columns `j < k + 1`. -/
theorem RoundsHessenbergStep.apply_eq_zero {m : RoundingModel ℝ} {k : ℕ} {hk : k + 1 < N}
    {A B : Matrix (Fin N) (Fin N) ℝ} (h : RoundsHessenbergStep m hk A B)
    (hA : ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → A i j = 0) (i j : Fin N)
    (hj : (j : ℕ) < k + 1) (hij : (j : ℕ) + 1 < (i : ℕ)) : B i j = 0 := by
  obtain ⟨vhat, βhat, C, -, hlt, hge, hrow⟩ := h
  obtain ⟨z, -, hB⟩ := hrow i
  rw [hB j, ite_eq_left (by omega)]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
  · have := congrFun (hlt j hjk) i
    rw [col_apply, col_apply] at this
    rw [this]
    exact hA i j hjk hij
  · obtain ⟨y, -, hC⟩ := hge j (le_of_eq hjk.symm)
    rw [hC i, ite_eq_left ⟨hjk, by omega⟩]

/-- The reflector data of a step, related to the exact reflector of the computed matrix
([higham2002accuracy] Lemma 19.1 read for the tail column): the computed `(v̂, β̂)` are relative
perturbations of order `4n + 8` of the exact `(v, β)` with
`hessenbergReflector A k = 1 - β v vᵀ`, `|β| ‖v‖₂² ≤ 2`, and `v` vanishing on the coordinates
`≤ k`. -/
theorem exists_isRelPert_hessenbergReflector {m : RoundingModel ℝ}
    (hcard : ((4 * N + 8 : ℕ) : ℝ) * m.u < 1) {A : Matrix (Fin N) (Fin N) ℝ} {k : ℕ}
    (hk : k + 1 < N) {vhat : Fin N → ℝ} {βhat : ℝ}
    (h : RoundsHouseholderVector m (hessenbergTailCol A hk) ⟨k + 1, hk⟩ vhat βhat) :
    ∃ (v : Fin N → ℝ) (β : ℝ), hessenbergReflector A k = 1 - β • vecMulVec v v ∧
      IsRelPert m.u (4 * N + 8) β βhat ∧ (∀ j, IsRelPert m.u (4 * N + 8) (v j) (vhat j)) ∧
      |β| * (v ⬝ᵥ v) ≤ 2 ∧ ∀ j : Fin N, (j : ℕ) ≤ k → v j = 0 := by
  have hcardι : ((4 * Fintype.card (Fin N) + 8 : ℕ) : ℝ) * m.u < 1 := by
    simpa [Fintype.card_fin] using hcard
  obtain ⟨hβ, hvi, hvj⟩ := h.isRelPert hcardι
  simp only [Fintype.card_fin] at hβ hvi
  set x := hessenbergTailCol A hk with hx
  set v := householderAxis x ⟨k + 1, hk⟩ with hv
  have hu0 := m.u_nonneg
  refine ⟨v, 2 / (v ⬝ᵥ v), ?_, hβ, fun j => ?_, ?_, fun j hj => ?_⟩
  · rw [hessenbergReflector_eq_householder A hk, householder_householderVec_eq]
  · rcases eq_or_ne j ⟨k + 1, hk⟩ with rfl | hj
    · exact hvi.mono hu0 (by omega) hcard
    · rw [hvj j hj]
      exact (IsRelPert.refl _ _).mono hu0 (Nat.zero_le _) hcard
  · have hvv : 0 ≤ v ⬝ᵥ v := by rw [dotProduct_self_eq_norm_sq]; positivity
    rcases eq_or_lt_of_le hvv with h0 | hpos
    · rw [← h0]; simp
    · rw [abs_of_pos (by positivity), div_mul_cancel₀ _ hpos.ne']
  · have hne : j ≠ ⟨k + 1, hk⟩ := fun e => by
      have := congrArg (fun i : Fin N => (i : ℕ)) e
      simp at this
      omega
    rw [hv, householderAxis_apply_of_ne x hne, hx, hessenbergTailCol, ite_eq_right (by omega)]


/-- **The backward error of one computed step of the Householder reduction**: if `A` vanishes
below the first subdiagonal in the columns `j < k` and `(13 n + 27) u < 1`, a computed step `B`
from `A` satisfies `‖B - P_k A P_k‖_F ≤ ((1 + ε)² - 1) ‖A‖_F` with `ε = 3 γ_{13n+27}` and
`P_k = hessenbergReflector A k` the **exact** reflector of the computed matrix `A`. The column
sweep is [higham2002accuracy] Lemma 19.2 column by column (with the annihilated entries handled
as in Theorem 19.4), the row sweep the same row by row, and the two combine through the
orthogonal invariance of the Frobenius norm. -/
theorem RoundsHessenbergStep.frobenius_norm_sub_le {m : RoundingModel ℝ}
    (hcard : ((13 * N + 27 : ℕ) : ℝ) * m.u < 1) {k : ℕ} {hk : k + 1 < N}
    {A B : Matrix (Fin N) (Fin N) ℝ} (h : RoundsHessenbergStep m hk A B)
    (hA : ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → A i j = 0) :
    ‖B - hessenbergReflector A k * A * hessenbergReflector A k‖ ≤
      ((1 + 3 * gamma m.u (13 * N + 27)) ^ 2 - 1) * ‖A‖ := by
  obtain ⟨vhat, βhat, C, hvec, hlt, hge, hrow⟩ := h
  set P := hessenbergReflector A k with hP_def
  set ε := 3 * gamma m.u (13 * N + 27) with hε_def
  have hu0 := m.u_nonneg
  have hcard4 : ((4 * N + 8 : ℕ) : ℝ) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu0).trans_lt hcard
  obtain ⟨v, β, hPeq, hβ, hv, hβv, hvsupp⟩ :=
    exists_isRelPert_hessenbergReflector hcard4 hk hvec
  have hPeq' : P = 1 - β • vecMulVec v v := by rw [hP_def]; exact hPeq
  have hε0 : 0 ≤ ε := by
    have := gamma_nonneg hu0 hcard
    positivity
  have hcard' : ((3 * (4 * N + 8) + Fintype.card (Fin N) + 3 : ℕ) : ℝ) * m.u < 1 := by
    rw [Fintype.card_fin, show 3 * (4 * N + 8) + N + 3 = 13 * N + 27 by ring]
    exact hcard
  -- Lemma 19.2 for every application of the computed reflector
  have happly : ∀ b y, RoundsHouseholderApply m βhat vhat b y →
      ‖(toLp 2 (y - P *ᵥ b) : EuclideanSpace ℝ (Fin N))‖ ≤
        ε * ‖(toLp 2 b : EuclideanSpace ℝ (Fin N))‖ := fun b y hy => by
    have := norm_sub_le_of_roundsHouseholderApply hcard' hβ hv hβv hy
    rwa [Fintype.card_fin, show 3 * (4 * N + 8) + N + 3 = 13 * N + 27 by ring, ← hPeq'] at this
  have hPorth : P ∈ Matrix.orthogonalGroup (Fin N) ℝ := hessenbergReflector_mem_unitaryGroup A k
  have hPsymm : Pᵀ = P := transpose_hessenbergReflector A k
  -- the reflector fixes the coordinates `≤ k` and the vectors supported there
  have hfix : ∀ (w : Fin N → ℝ) (j : Fin N), (j : ℕ) ≤ k → (P *ᵥ w) j = w j := fun w j hj => by
    rw [hPeq', one_sub_smul_vecMulVec_mulVec_apply, hvsupp j hj]
    ring
  have hfixvec : ∀ w : Fin N → ℝ, (∀ r : Fin N, k + 1 ≤ (r : ℕ) → w r = 0) → P *ᵥ w = w :=
    fun w hw => by
    rw [hPeq']
    ext j
    rw [one_sub_smul_vecMulVec_mulVec_apply]
    have hvw : v ⬝ᵥ w = 0 := Finset.sum_eq_zero fun r _ => by
      rcases le_or_gt (r : ℕ) k with hr | hr
      · rw [hvsupp r hr, zero_mul]
      · rw [hw r hr, mul_zero]
    rw [hvw]
    ring
  -- the reflector annihilates column `k` below the first subdiagonal
  have hann : ∀ i : Fin N, k + 2 ≤ (i : ℕ) → (P *ᵥ A.col ⟨k, by omega⟩) i = 0 := fun i hi => by
    rw [hP_def, hessenbergReflector_of_lt A (by omega)]
    exact householder_householderTail_mulVec_apply_of_gt _ (by omega)
  -- the column sweep
  have hcol : ∀ j, ‖(toLp 2 ((C - P * A).col j) : EuclideanSpace ℝ (Fin N))‖ ≤
      ε * ‖(toLp 2 (A.col j) : EuclideanSpace ℝ (Fin N))‖ := fun j => by
    have hcolj : (C - P * A).col j = C.col j - P *ᵥ A.col j := by
      ext i
      simp [col_apply, mul_apply, mulVec, dotProduct]
    rw [hcolj]
    rcases lt_or_ge (j : ℕ) k with hj | hj
    · rw [hlt j hj, hfixvec (A.col j) (fun r hr => hA r j hj (by omega)), sub_self]
      simp only [WithLp.toLp_zero, norm_zero]
      positivity
    · obtain ⟨y, hy, hC⟩ := hge j hj
      refine (norm_toLp_le_of_abs_le fun i => ?_).trans (happly _ _ hy)
      simp only [Pi.sub_apply, col_apply]
      rw [hC i]
      split_ifs with hij
      · obtain ⟨hjk, hik⟩ := hij
        have hjk' : j = ⟨k, by omega⟩ := Fin.ext hjk
        rw [hjk', hann i hik]
        simp
      · exact le_rfl
  have hCPA : ‖C - P * A‖ ≤ ε * ‖A‖ := frobenius_norm_le_of_forall_col_le hε0 hcol
  -- the row sweep
  have hrowb : ∀ i, ‖(toLp 2 ((B - C * P).row i) : EuclideanSpace ℝ (Fin N))‖ ≤
      ε * ‖(toLp 2 (C.row i) : EuclideanSpace ℝ (Fin N))‖ := fun i => by
    obtain ⟨z, hz, hB⟩ := hrow i
    have hrowi : (B - C * P).row i = B.row i - P *ᵥ C.row i := by
      ext j
      simp only [row_apply, Matrix.sub_apply]
      rw [show (C * P) i j = (C i ᵥ* P) j from rfl, ← mulVec_transpose, hPsymm]
      rfl
    rw [hrowi]
    refine (norm_toLp_le_of_abs_le fun j => ?_).trans (happly _ _ hz)
    simp only [Pi.sub_apply, row_apply]
    rw [hB j]
    split_ifs with hj
    · rw [hfix _ j hj]
      simp
    · exact le_rfl
  have hBCP : ‖B - C * P‖ ≤ ε * ‖C‖ := frobenius_norm_le_of_forall_row_le hε0 hrowb
  -- combine
  have hPA : ‖P * A‖ = ‖A‖ := by
    simpa using frobenius_norm_orthogonal_mul_mul_orthogonal hPorth A (one_mem _)
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hC : ‖C‖ ≤ (1 + ε) * ‖A‖ := by
    calc ‖C‖ = ‖P * A + (C - P * A)‖ := by congr 1; abel
      _ ≤ ‖P * A‖ + ‖C - P * A‖ := norm_add_le _ _
      _ ≤ ‖A‖ + ε * ‖A‖ := by rw [hPA]; linarith
      _ = (1 + ε) * ‖A‖ := by ring
  have hsplit : B - P * A * P = (B - C * P) + (C - P * A) * P := by
    rw [Matrix.sub_mul]
    abel
  have h2 : ‖(C - P * A) * P‖ = ‖C - P * A‖ := by
    simpa using frobenius_norm_orthogonal_mul_mul_orthogonal (one_mem _) (C - P * A) hPorth
  calc ‖B - P * A * P‖ ≤ ‖B - C * P‖ + ‖(C - P * A) * P‖ := by
        rw [hsplit]
        exact norm_add_le _ _
    _ ≤ ε * ‖C‖ + ε * ‖A‖ := by rw [h2]; linarith
    _ ≤ ε * ((1 + ε) * ‖A‖) + ε * ‖A‖ := by gcongr
    _ = ((1 + ε) ^ 2 - 1) * ‖A‖ := by ring

/-- **(5.46) of [quarteroni2000numerical], with the constants explicit** (Wilkinson's backward
error bound for the Householder reduction to Hessenberg form, [higham2002accuracy] §19.10): if
`(13 n + 27) u < 1` and `2 (n - 2) ε < 1` for `ε = 3 γ_{13n+27}`, the computed Hessenberg matrix
`Ĥ = Â_{n-2}` of `RoundsHessenbergReduce` satisfies `Ĥ = Qᵀ (A + E) Q` for the orthogonal
`Q = P_0 ⋯ P_{n-3}`, `P_k` the exact reflector of the computed `Â_k`, with
`‖E‖_F ≤ γ_{2(n-2)}(ε) ‖A‖_F = (2 (n - 2) ε / (1 - 2 (n - 2) ε)) ‖A‖_F`, which is
`c n² u ‖A‖_F` for `u` small. The `2 (n - 2)` counts the column and the row sweep of each of the
`n - 2` steps. -/
theorem exists_roundsHessenbergReduce_eq {m : RoundingModel ℝ}
    (hcard : ((13 * N + 27 : ℕ) : ℝ) * m.u < 1)
    (hr : ((2 * (N - 2) : ℕ) : ℝ) * (3 * gamma m.u (13 * N + 27)) < 1)
    {A : Matrix (Fin N) (Fin N) ℝ} {Ahat : ℕ → Matrix (Fin N) (Fin N) ℝ}
    (h : RoundsHessenbergReduce m A Ahat) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∃ E : Matrix (Fin N) (Fin N) ℝ,
      Ahat (N - 2) = Qᵀ * (A + E) * Q ∧
        ‖E‖ ≤ gamma (3 * gamma m.u (13 * N + 27)) (2 * (N - 2)) * ‖A‖ := by
  obtain ⟨h0, hstep⟩ := h
  set ε := 3 * gamma m.u (13 * N + 27) with hε_def
  have hε0 : 0 ≤ ε := by
    have := gamma_nonneg m.u_nonneg hcard
    positivity
  set P : ℕ → Matrix (Fin N) (Fin N) ℝ := fun k => hessenbergReflector (Ahat k) k with hP_def
  have hPorth : ∀ k, P k ∈ Matrix.orthogonalGroup (Fin N) ℝ := fun k =>
    hessenbergReflector_mem_unitaryGroup _ k
  have hPsymm : ∀ k, (P k)ᵀ = P k := fun k => transpose_hessenbergReflector _ k
  -- the Hessenberg structure of the computed iterates
  have hhess : ∀ k, k ≤ N - 2 → ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) →
      Ahat k i j = 0 := by
    intro k
    induction k with
    | zero => intro _ i j hj; omega
    | succ k ih =>
      intro hk i j hj hij
      exact (hstep k (by omega)).apply_eq_zero (ih (by omega)) i j hj hij
  -- the per-step bound
  have hA : ∀ k, k < N - 2 → ‖Ahat (k + 1) - P k * Ahat k * P k‖ ≤ ((1 + ε) ^ 2 - 1) * ‖Ahat k‖ :=
    fun k hk => (hstep k hk).frobenius_norm_sub_le hcard (hhess k (by omega))
  have hε'0 : 0 ≤ (1 + ε) ^ 2 - 1 := by nlinarith
  obtain ⟨E, hE, hEn⟩ := exists_eq_transpose_mul_add_mul_prodFwd hPorth hPsymm hε'0 (N - 2) hA
  refine ⟨prodFwd P (N - 2), prodFwd_mem_orthogonalGroup hPorth _, E, by rw [hE, h0], ?_⟩
  rw [h0] at hEn
  refine hEn.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hpow : (1 + ((1 + ε) ^ 2 - 1)) ^ (N - 2) = (1 + ε) ^ (2 * (N - 2)) := by
    rw [add_sub_cancel, pow_mul]
  rw [hpow]
  exact one_add_pow_sub_one_le_gamma hε0 hr

end Hessenberg

/-! ### Reflectors acting on a block of coordinates -/

section Block

open scoped Matrix.Norms.Frobenius

variable {p : ι → Prop} [DecidablePred p]

/-- A vector on the coordinates `{i // p i}`, extended by zero to all of `ι`. -/
private def extendByZero (p : ι → Prop) [DecidablePred p] (v : {i // p i} → ℝ) : ι → ℝ :=
  fun i => if h : p i then v ⟨i, h⟩ else 0

omit [Fintype ι] [DecidableEq ι] in
private theorem extendByZero_apply (v : {i // p i} → ℝ) (a : {i // p i}) :
    extendByZero p v a = v a := by
  simp [extendByZero, a.2]

omit [Fintype ι] [DecidableEq ι] in
private theorem extendByZero_apply_of_not (v : {i // p i} → ℝ) {r : ι} (hr : ¬ p r) :
    extendByZero p v r = 0 := by
  simp [extendByZero, hr]

omit [DecidableEq ι] in
private theorem extendByZero_dotProduct (v : {i // p i} → ℝ) (w : ι → ℝ) :
    extendByZero p v ⬝ᵥ w = v ⬝ᵥ fun a : {i // p i} => w a := by
  rw [dotProduct, ← Fintype.sum_subtype_add_sum_subtype p]
  have h2 : ∑ a : {i // ¬ p i}, extendByZero p v a * w a = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [extendByZero_apply_of_not v a.2, zero_mul]
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun a _ => by rw [extendByZero_apply]

/-- The reflector of the extended vector acts on the block as the reflector of the vector. -/
private theorem one_sub_smul_vecMulVec_extendByZero_mulVec_apply (β : ℝ)
    (v : {i // p i} → ℝ) (w : ι → ℝ) (a : {i // p i}) :
    ((1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) *ᵥ w) (a : ι) =
      ((1 - β • vecMulVec v v) *ᵥ fun b : {i // p i} => w b) a := by
  rw [one_sub_smul_vecMulVec_mulVec_apply, one_sub_smul_vecMulVec_mulVec_apply,
    extendByZero_apply, extendByZero_dotProduct]

/-- The reflector of the extended vector fixes the coordinates off the block. -/
private theorem one_sub_smul_vecMulVec_extendByZero_mulVec_apply_of_not (β : ℝ)
    (v : {i // p i} → ℝ) (w : ι → ℝ) {r : ι} (hr : ¬ p r) :
    ((1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) *ᵥ w) r = w r := by
  rw [one_sub_smul_vecMulVec_mulVec_apply, extendByZero_apply_of_not v hr]
  ring

/-- The extension of an orthogonal reflector of the block by the identity is orthogonal. -/
private theorem one_sub_smul_vecMulVec_extendByZero_mem_orthogonalGroup {β : ℝ}
    {v : {i // p i} → ℝ} (h : (1 - β • vecMulVec v v) ∈ Matrix.orthogonalGroup {i // p i} ℝ) :
    (1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) ∈ Matrix.orthogonalGroup ι ℝ := by
  rw [mem_orthogonalGroup_iff, transpose_one_sub_smul_vecMulVec,
    one_sub_smul_vecMulVec_mul_self] at h ⊢
  have h0 : (β * (β * (v ⬝ᵥ v) - 2)) • vecMulVec v v = 0 := by simpa using h
  have hvv : extendByZero p v ⬝ᵥ extendByZero p v = v ⬝ᵥ v := by
    rw [extendByZero_dotProduct]
    exact congrArg (v ⬝ᵥ ·) (funext fun a => extendByZero_apply v a)
  have h1 : (β * (β * (extendByZero p v ⬝ᵥ extendByZero p v) - 2)) •
      vecMulVec (extendByZero p v) (extendByZero p v) = 0 := by
    rw [hvv]
    ext a b
    simp only [Matrix.smul_apply, vecMulVec_apply, Matrix.zero_apply, smul_eq_mul]
    by_cases ha : p a
    · by_cases hb : p b
      · have := congrFun₂ h0 ⟨a, ha⟩ ⟨b, hb⟩
        simp only [Matrix.smul_apply, vecMulVec_apply, Matrix.zero_apply, smul_eq_mul] at this
        rw [extendByZero_apply v ⟨a, ha⟩, extendByZero_apply v ⟨b, hb⟩]
        exact this
      · rw [extendByZero_apply_of_not v hb]
        ring
    · rw [extendByZero_apply_of_not v ha]
      ring
  rw [h1, add_zero]

omit [DecidableEq ι] in
/-- The Euclidean norm of a restriction is at most the norm. -/
private theorem norm_toLp_restrict_le (w : ι → ℝ) :
    ‖(toLp 2 (fun a : {i // p i} => w a) : EuclideanSpace ℝ {i // p i})‖ ≤
      ‖(toLp 2 w : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)

omit [DecidableEq ι] in
/-- A vector vanishing off the block has the norm of its restriction. -/
private theorem norm_toLp_eq_restrict {d : ι → ℝ} (h : ∀ r, ¬ p r → d r = 0) :
    ‖(toLp 2 d : EuclideanSpace ℝ ι)‖ =
      ‖(toLp 2 (fun a : {i // p i} => d a) : EuclideanSpace ℝ {i // p i})‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Fintype.sum_subtype_add_sum_subtype p]
  have h2 : ∑ a : {i // ¬ p i}, ‖(toLp 2 d : EuclideanSpace ℝ ι) a‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun a _ => by simp [h a a.2]
  rw [h2, add_zero]

/-- **An update of a block of coordinates, against the extended reflector**: if `z` agrees with
`w` off the block and, on the block, is entrywise at least as close to `P (w|_block)` as a vector
`y` with `‖y - P (w|_block)‖₂ ≤ ε ‖w|_block‖₂`, then `‖z - P' w‖₂ ≤ ε ‖w‖₂` for the extension
`P'` of `P = 1 - β v vᵀ` by the identity. -/
private theorem norm_sub_one_sub_smul_vecMulVec_extendByZero_mulVec_le {β ε : ℝ}
    (hε : 0 ≤ ε) {v : {i // p i} → ℝ} {w z : ι → ℝ} {y : {i // p i} → ℝ}
    (hout : ∀ r, ¬ p r → z r = w r)
    (hin : ∀ a : {i // p i},
      |z (a : ι) - ((1 - β • vecMulVec v v) *ᵥ fun b : {i // p i} => w b) a| ≤
      |y a - ((1 - β • vecMulVec v v) *ᵥ fun b : {i // p i} => w b) a|)
    (hy : ‖(toLp 2 (y - (1 - β • vecMulVec v v) *ᵥ fun b : {i // p i} => w b) :
      EuclideanSpace ℝ {i // p i})‖ ≤
        ε * ‖(toLp 2 (fun b : {i // p i} => w b) : EuclideanSpace ℝ {i // p i})‖) :
    ‖(toLp 2 (z - (1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) *ᵥ w) :
      EuclideanSpace ℝ ι)‖ ≤ ε * ‖(toLp 2 w : EuclideanSpace ℝ ι)‖ := by
  rw [norm_toLp_eq_restrict fun r hr => by
    rw [Pi.sub_apply, one_sub_smul_vecMulVec_extendByZero_mulVec_apply_of_not β v w hr, hout r hr,
      sub_self]]
  refine (norm_toLp_le_of_abs_le fun a => ?_).trans
    (hy.trans (mul_le_mul_of_nonneg_left (norm_toLp_restrict_le w) hε))
  rw [Pi.sub_apply, one_sub_smul_vecMulVec_extendByZero_mulVec_apply]
  exact hin a

omit [Fintype ι] in
/-- The extended reflector is the identity on the rows off the block. -/
private theorem one_sub_smul_vecMulVec_extendByZero_apply_of_not (β : ℝ)
    (v : {i // p i} → ℝ) {r : ι} (hr : ¬ p r) (j : ι) :
    (1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) r j = (1 : Matrix ι ι ℝ) r j := by
  simp [vecMulVec_apply, extendByZero_apply_of_not v hr]

/-- Left multiplication by the extended reflector fixes the rows off the block. -/
private theorem one_sub_smul_vecMulVec_extendByZero_mul_apply_of_not (β : ℝ)
    (v : {i // p i} → ℝ) (M : Matrix ι ι ℝ) {r : ι} (hr : ¬ p r) (j : ι) :
    ((1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) * M) r j = M r j :=
  one_sub_smul_vecMulVec_extendByZero_mulVec_apply_of_not β v (fun b => M b j) hr

/-- Left multiplication by the extended reflector acts on the rows of the block. -/
private theorem one_sub_smul_vecMulVec_extendByZero_mul_apply (β : ℝ) (v : {i // p i} → ℝ)
    (M : Matrix ι ι ℝ) (a : {i // p i}) (j : ι) :
    ((1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) * M) (a : ι) j =
      ((1 - β • vecMulVec v v) *ᵥ fun b : {i // p i} => M b j) a :=
  one_sub_smul_vecMulVec_extendByZero_mulVec_apply β v (fun b => M b j) a

/-- Right multiplication by the extended reflector fixes the columns off the block. -/
private theorem mul_one_sub_smul_vecMulVec_extendByZero_apply_of_not (β : ℝ)
    (v : {i // p i} → ℝ) (M : Matrix ι ι ℝ) (i : ι) {r : ι} (hr : ¬ p r) :
    (M * (1 - β • vecMulVec (extendByZero p v) (extendByZero p v))) i r = M i r := by
  change (M * (1 - β • vecMulVec (extendByZero p v) (extendByZero p v)))ᵀ r i = Mᵀ r i
  rw [transpose_mul, transpose_one_sub_smul_vecMulVec]
  exact one_sub_smul_vecMulVec_extendByZero_mul_apply_of_not β v Mᵀ hr i

/-- Right multiplication by the extended reflector acts on the columns of the block. -/
private theorem mul_one_sub_smul_vecMulVec_extendByZero_apply (β : ℝ) (v : {i // p i} → ℝ)
    (M : Matrix ι ι ℝ) (i : ι) (a : {i // p i}) :
    (M * (1 - β • vecMulVec (extendByZero p v) (extendByZero p v))) i (a : ι) =
      ((1 - β • vecMulVec v v) *ᵥ fun b : {i // p i} => M i b) a := by
  change (M * (1 - β • vecMulVec (extendByZero p v) (extendByZero p v)))ᵀ (a : ι) i = _
  rw [transpose_mul, transpose_one_sub_smul_vecMulVec]
  exact one_sub_smul_vecMulVec_extendByZero_mul_apply β v Mᵀ a i

/-- A matrix supported on the block has the Frobenius norm of its block. -/
private theorem frobenius_norm_eq_submatrix {M : Matrix ι ι ℝ}
    (h : ∀ i j, ¬ (p i ∧ p j) → M i j = 0) :
    ‖M‖ = ‖M.submatrix (Subtype.val : {i // p i} → ι) (Subtype.val : {i // p i} → ι)‖ := by
  have hsq : ‖M‖ ^ 2 =
      ‖M.submatrix (Subtype.val : {i // p i} → ι) (Subtype.val : {i // p i} → ι)‖ ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq,
      ← Fintype.sum_subtype_add_sum_subtype p]
    have h2 : ∑ r : {i // ¬ p i}, ∑ j, ‖M r j‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun j _ => by
        rw [h r j fun h => r.2 h.1]
        simp
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Fintype.sum_subtype_add_sum_subtype p]
    have h3 : ∑ s : {i // ¬ p i}, ‖M a s‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun s _ => by
        rw [h a s fun h => s.2 h.2]
        simp
    rw [h3, add_zero]
    rfl
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- The Frobenius norm of a principal block is at most that of the matrix. -/
private theorem frobenius_norm_submatrix_le (M : Matrix ι ι ℝ) :
    ‖M.submatrix (Subtype.val : {i // p i} → ι) (Subtype.val : {i // p i} → ι)‖ ≤ ‖M‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq,
    ← Fintype.sum_subtype_add_sum_subtype p]
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun a _ => ?_)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun j => ‖M a j‖ ^ 2)]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)

/-- Conjugation by the extended reflector, off the block in both indices. -/
private theorem conj_extendByZero_apply_of_not_of_not (β : ℝ) (v : {i // p i} → ℝ)
    (M : Matrix ι ι ℝ) {i j : ι} (hi : ¬ p i) (hj : ¬ p j) :
    ((1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) * M *
      (1 - β • vecMulVec (extendByZero p v) (extendByZero p v))) i j = M i j := by
  rw [mul_one_sub_smul_vecMulVec_extendByZero_apply_of_not β v _ i hj,
    one_sub_smul_vecMulVec_extendByZero_mul_apply_of_not β v M hi j]

/-- Conjugation by the extended reflector, a row of the block and a column off it. -/
private theorem conj_extendByZero_apply_of_not_right (β : ℝ) (v : {i // p i} → ℝ)
    (M : Matrix ι ι ℝ) (a : {i // p i}) {j : ι} (hj : ¬ p j) :
    ((1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) * M *
      (1 - β • vecMulVec (extendByZero p v) (extendByZero p v))) (a : ι) j =
      ((1 - β • vecMulVec v v) *ᵥ fun b : {i // p i} => M b j) a := by
  rw [mul_one_sub_smul_vecMulVec_extendByZero_apply_of_not β v _ _ hj,
    one_sub_smul_vecMulVec_extendByZero_mul_apply β v M a j]

/-- Conjugation by the extended reflector, a row off the block and a column of it. -/
private theorem conj_extendByZero_apply_of_not_left (β : ℝ) (v : {i // p i} → ℝ)
    (M : Matrix ι ι ℝ) {i : ι} (hi : ¬ p i) (b : {i // p i}) :
    ((1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) * M *
      (1 - β • vecMulVec (extendByZero p v) (extendByZero p v))) i (b : ι) =
      ((1 - β • vecMulVec v v) *ᵥ fun c : {i // p i} => M i c) b := by
  rw [mul_one_sub_smul_vecMulVec_extendByZero_apply β v _ i b]
  congr 1
  funext c
  exact one_sub_smul_vecMulVec_extendByZero_mul_apply_of_not β v M hi c

/-- Conjugation by the extended reflector on the block is conjugation of the block. -/
private theorem conj_extendByZero_apply (β : ℝ) (v : {i // p i} → ℝ) (M : Matrix ι ι ℝ)
    (a b : {i // p i}) :
    ((1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) * M *
      (1 - β • vecMulVec (extendByZero p v) (extendByZero p v))) (a : ι) (b : ι) =
      ((1 - β • vecMulVec v v) *
        M.submatrix (Subtype.val : {i // p i} → ι) (Subtype.val : {i // p i} → ι) *
        (1 - β • vecMulVec v v)) a b := by
  rw [mul_one_sub_smul_vecMulVec_extendByZero_apply β v _ (a : ι) b]
  have hc : (fun c : {i // p i} =>
      ((1 - β • vecMulVec (extendByZero p v) (extendByZero p v)) * M) (a : ι) (c : ι)) =
      fun c : {i // p i} => ((1 - β • vecMulVec v v) *ᵥ fun d : {i // p i} => M d c) a :=
    funext fun c => one_sub_smul_vecMulVec_extendByZero_mul_apply β v M a c
  rw [hc]
  have hs : ∀ c, (1 - β • vecMulVec v v) c b = (1 - β • vecMulVec v v) b c := fun c =>
    congrFun (congrFun (transpose_one_sub_smul_vecMulVec β v) b) c
  simp only [mulVec, dotProduct, Matrix.mul_apply, submatrix_apply]
  exact Finset.sum_congr rfl fun c _ => by rw [hs c]; ring

omit [Fintype ι] in
/-- The entries of `δ (e_a e_bᵀ + e_b e_aᵀ)` for `a ≠ b`. -/
private theorem smul_vecMulVec_single_add_apply {a b : ι} (h : b ≠ a) (δ : ℝ) (i j : ι) :
    (δ • (vecMulVec (Pi.single a (1 : ℝ)) (Pi.single b 1) +
      vecMulVec (Pi.single b (1 : ℝ)) (Pi.single a 1))) i j =
      if i = a ∧ j = b then δ else if i = b ∧ j = a then δ else 0 := by
  simp only [Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> by_cases h3 : i = b <;>
    by_cases h4 : j = a <;> simp_all

/-- The Euclidean norm of a standard basis vector is one. -/
private theorem norm_toLp_single_one (a : ι) :
    ‖(toLp 2 (Pi.single a (1 : ℝ)) : EuclideanSpace ℝ ι)‖ = 1 := by
  have h : ‖(toLp 2 (Pi.single a (1 : ℝ)) : EuclideanSpace ℝ ι)‖ ^ 2 = 1 ^ 2 := by
    rw [← dotProduct_self_eq_norm_sq]
    simp
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h

/-- `‖δ (e_a e_bᵀ + e_b e_aᵀ)‖_F ≤ 2 |δ|`. -/
private theorem frobenius_norm_smul_vecMulVec_single_add_le (δ : ℝ) (a b : ι) :
    ‖δ • (vecMulVec (Pi.single a (1 : ℝ)) (Pi.single b 1) +
      vecMulVec (Pi.single b (1 : ℝ)) (Pi.single a 1))‖ ≤ 2 * |δ| := by
  rw [norm_smul, Real.norm_eq_abs]
  have e1 := frobenius_norm_vecMulVec_le (Pi.single a (1 : ℝ)) (Pi.single b 1)
  have e2 := frobenius_norm_vecMulVec_le (Pi.single b (1 : ℝ)) (Pi.single a 1)
  rw [norm_toLp_single_one, norm_toLp_single_one] at e1 e2
  have := norm_add_le (vecMulVec (Pi.single a (1 : ℝ)) (Pi.single b 1))
    (vecMulVec (Pi.single b (1 : ℝ)) (Pi.single a 1))
  have hδ := abs_nonneg δ
  nlinarith

omit [DecidableEq ι] in
/-- The computed Euclidean norm `fl(√fl(xᵀx))` against `‖x‖₂`: if `n ≤ N` for `n = card κ` and
`(2N + 2) u < 1`, then `|ν̂ - ‖x‖₂| ≤ γ_{N+1} ‖x‖₂`, and so `≤ γ_{N+1} a` for any `a ≥ ‖x‖₂`. -/
private theorem abs_rounds_sqrt_sub_norm_le {κ : Type*} [Fintype κ] {m : RoundingModel ℝ}
    {N : ℕ} (hN : Fintype.card κ ≤ N) (hcard : ((2 * N + 2 : ℕ) : ℝ) * m.u < 1) {x : κ → ℝ}
    {σ ν : ℝ} (hσ : RoundsDot m x x σ) (hν : m.Rounds (√σ) ν) {a : ℝ}
    (hxa : ‖(toLp 2 x : EuclideanSpace ℝ κ)‖ ≤ a) :
    |ν - ‖(toLp 2 x : EuclideanSpace ℝ κ)‖| ≤ gamma m.u (N + 1) * a := by
  set n := Fintype.card κ
  have hu0 := m.u_nonneg
  have hlt : ∀ j : ℕ, j ≤ 2 * N + 2 → ((j : ℕ) : ℝ) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hu0).trans_lt hcard
  have hu1 : m.u < 1 := by simpa using hlt 1 (by omega)
  have hxx : x ⬝ᵥ x = ‖(toLp 2 x : EuclideanSpace ℝ κ)‖ ^ 2 := dotProduct_self_eq_norm_sq x
  have h1 : IsRelPert m.u n (x ⬝ᵥ x) σ := by
    refine isRelPert_of_abs_sub_le (gamma_nonneg hu0 (hlt n (by omega))) ?_
    have := abs_sub_le_of_roundsDot hu1 (hlt n (by omega)) hσ
    have e : |x| ⬝ᵥ |x| = x ⬝ᵥ x := by simp only [dotProduct, Pi.abs_apply, abs_mul_abs_self]
    rw [e] at this
    rwa [abs_of_nonneg (show (0 : ℝ) ≤ x ⬝ᵥ x by rw [hxx]; positivity)]
  have h2 := h1.sqrt (gamma_lt_one hu0 (by
    have := hlt (2 * n) (by omega)
    push_cast at this
    linarith)).le (by rw [hxx]; positivity)
  rw [hxx, Real.sqrt_sq (norm_nonneg _)] at h2
  have h3 := (h2.rounds hu1 (hlt _ (by omega)) hν).abs_sub_le
  rw [abs_of_nonneg (norm_nonneg _)] at h3
  exact h3.trans (mul_le_mul (gamma_mono hu0 (by omega) (hlt _ (by omega))) hxa (norm_nonneg _)
    (gamma_nonneg hu0 (hlt _ (by omega))))

end Block

/-! ### The symmetric rank-two update of the tridiagonalization -/

section SymmRankTwo

open scoped Matrix.Norms.Frobenius

/-- **The symmetric rank-two update in floating-point arithmetic** ([golub2013matrix] §8.3.1,
Algorithm 8.3.1): for computed reflector data `(β, v)` and a symmetric `B`,
`RoundsSymmRankTwoUpdate m β v B B'` says that `p̂_i = fl(β fl(B_i ⬝ v))` (the inner product a
`RoundsDot`), `ŝ = fl(p̂ ⬝ v)`, `t̂ = fl(fl(β ŝ) / 2)`, `ŵ_i = fl(p̂_i - fl(t̂ v_i))`, and every
entry of `B'` is `fl(fl(B_rs - fl(v_r ŵ_s)) - fl(ŵ_r v_s))` for `(r, s)` the entry itself or its
mirror image, `B'` being symmetric: one triangle is computed and mirrored, as the book says
(which triangle does not matter). -/
def RoundsSymmRankTwoUpdate (m : RoundingModel ℝ) (β : ℝ) (v : ι → ℝ) (B B' : Matrix ι ι ℝ) :
    Prop :=
  ∃ (phat what : ι → ℝ) (shat that : ℝ),
    (∀ i, ∃ r, RoundsDot m (B i) v r ∧ m.Rounds (β * r) (phat i)) ∧
    RoundsDot m phat v shat ∧
    (∃ t₁, m.Rounds (β * shat) t₁ ∧ m.Rounds (t₁ / 2) that) ∧
    (∀ i, ∃ t, m.Rounds (that * v i) t ∧ m.Rounds (phat i - t) (what i)) ∧
    (∀ i j, ∃ r s, (r = i ∧ s = j ∨ r = j ∧ s = i) ∧ ∃ a b c : ℝ, m.Rounds (v r * what s) a ∧
      m.Rounds (B r s - a) b ∧ m.Rounds (what r * v s) c ∧ m.Rounds (b - c) (B' i j)) ∧
    ∀ i j, B' j i = B' i j

/-- The two-sided reflection as a symmetric rank-two update ([golub2013matrix] §8.3.1):
`(1 - β v vᵀ) B (1 - β v vᵀ) = B - v wᵀ - w vᵀ` for a symmetric `B`, `p = β B v` and
`w = p - (β (vᵀ p) / 2) v`, whatever `β`. (Over `ℝ`; the planned `StarRing` form is
`Matrix.conj_one_sub_smul_vecMulVec_eq_sub` of `Numlib/LinearAlgebra/Matrix/QR`.) -/
private theorem one_sub_smul_vecMulVec_mul_mul_eq {B : Matrix ι ι ℝ} (hB : Bᵀ = B) (β : ℝ)
    (v : ι → ℝ) :
    (1 - β • vecMulVec v v) * B * (1 - β • vecMulVec v v) =
      B - vecMulVec v (β • (B *ᵥ v) - (β * (v ⬝ᵥ β • (B *ᵥ v)) / 2) • v) -
        vecMulVec (β • (B *ᵥ v) - (β * (v ⬝ᵥ β • (B *ᵥ v)) / 2) • v) v := by
  have hvB : v ᵥ* B = B *ᵥ v := by
    conv_lhs => rw [← hB]
    exact vecMul_transpose B v
  have h1 : vecMulVec v v * B = vecMulVec v (B *ᵥ v) := by rw [vecMulVec_mul, hvB]
  have h2 : B * vecMulVec v v = vecMulVec (B *ᵥ v) v := mul_vecMulVec B v v
  have h3 : vecMulVec v (B *ᵥ v) * vecMulVec v v = ((B *ᵥ v) ⬝ᵥ v) • vecMulVec v v := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, h1, h2, h3, vecMulVec_sub, sub_vecMulVec, vecMulVec_smul, smul_vecMulVec,
    dotProduct_smul, smul_eq_mul, dotProduct_comm v (B *ᵥ v)]
  module

/-- `|∑ y - ∑ x| ≤ γ_K ∑ |x|` when every `y j` is a relative perturbation of order `K` of
`x j`. -/
private theorem abs_sum_sub_sum_le {κ : Type*} [Fintype κ] {u : ℝ} {K : ℕ} {x y : κ → ℝ}
    (h : ∀ j, IsRelPert u K (x j) (y j)) : |∑ j, y j - ∑ j, x j| ≤ gamma u K * ∑ j, |x j| := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => (h j).abs_sub_le)

/-- One entry of the computed symmetric rank-two update against its exact value: with `v̂`
perturbations of order `k` of `v` and `ŵ` within `γ_g W` of `w`, `|w| ≤ W`,
`|fl(fl(B_rs - fl(v̂_r ŵ_s)) - fl(ŵ_r v̂_s)) - (B_rs - v_r w_s - w_r v_s)|` is at most
`γ_{g+k+3} (|B_rs| + |v_r| W_s + W_r |v_s|)`. -/
private theorem abs_rounds_sub_sub_sub_le {m : RoundingModel ℝ} {k g : ℕ}
    (hcard : ((g + k + 3 : ℕ) : ℝ) * m.u < 1)
    {vr vs vhr vhs wr ws whr whs Wr Ws Brs a b c e : ℝ}
    (hvr : IsRelPert m.u k vr vhr) (hvs : IsRelPert m.u k vs vhs)
    (hwr : |whr - wr| ≤ gamma m.u g * Wr) (hws : |whs - ws| ≤ gamma m.u g * Ws)
    (hwr' : |wr| ≤ Wr) (hws' : |ws| ≤ Ws)
    (ha : m.Rounds (vhr * whs) a) (hb : m.Rounds (Brs - a) b) (hc : m.Rounds (whr * vhs) c)
    (he : m.Rounds (b - c) e) :
    |e - (Brs - vr * ws - wr * vs)| ≤
      gamma m.u (g + k + 3) * (|Brs| + |vr| * Ws + Wr * |vs|) := by
  have hu0 := m.u_nonneg
  have hlt : ∀ j : ℕ, j ≤ g + k + 3 → ((j : ℕ) : ℝ) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hu0).trans_lt hcard
  have hu1 : m.u < 1 := by simpa using hlt 1 (by omega)
  have hγ : ∀ j : ℕ, j ≤ g + k + 3 → 0 ≤ gamma m.u j := fun j hj => gamma_nonneg hu0 (hlt j hj)
  set G := gamma m.u g with hG_def
  set G' := gamma m.u (k + 1 + g) with hG'_def
  set H := gamma m.u (g + k + 3) with hH_def
  have hG0 : 0 ≤ G := hγ g (by omega)
  have hG'0 : 0 ≤ G' := hγ _ (by omega)
  have hγk : 0 ≤ gamma m.u (k + 1) := hγ _ (by omega)
  have hWr : 0 ≤ Wr := (abs_nonneg _).trans hwr'
  have hWs : 0 ≤ Ws := (abs_nonneg _).trans hws'
  have hG' : gamma m.u (k + 1) + G + gamma m.u (k + 1) * G ≤ G' :=
    gamma_add_gamma_add_mul_le hu0 (hlt _ (by omega))
  -- a perturbed `v` times a perturbed `w`, rounded once
  have hprod : ∀ {vv vh ww wh WW δ : ℝ}, IsRelPert m.u k vv vh → |wh - ww| ≤ G * WW →
      |ww| ≤ WW → |δ| ≤ m.u → |vh * (1 + δ) * wh - vv * ww| ≤ G' * (|vv| * WW) := by
    intro vv vh ww wh WW δ hvv hww hww' hδ
    obtain ⟨θ, hθ, hθe⟩ := hvv.mul_one_add hu0 hu1 (hlt (k + 1) (by omega)) hδ
    have hWW : 0 ≤ WW := (abs_nonneg _).trans hww'
    rw [hθe, show vv * (1 + θ) * wh - vv * ww = vv * (θ * ww + (1 + θ) * (wh - ww)) by ring,
      abs_mul]
    have h1θ : |1 + θ| ≤ 1 + gamma m.u (k + 1) :=
      (abs_add_le 1 θ).trans (by rw [abs_one]; linarith)
    have h1 : |θ * ww + (1 + θ) * (wh - ww)| ≤
        gamma m.u (k + 1) * WW + (1 + gamma m.u (k + 1)) * (G * WW) := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul hθ hww' (abs_nonneg _) hγk
      · rw [abs_mul]
        exact mul_le_mul h1θ hww (abs_nonneg _) (by linarith)
    calc |vv| * |θ * ww + (1 + θ) * (wh - ww)|
        ≤ |vv| * (gamma m.u (k + 1) * WW + (1 + gamma m.u (k + 1)) * (G * WW)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = (gamma m.u (k + 1) + G + gamma m.u (k + 1) * G) * (|vv| * WW) := by ring
      _ ≤ G' * (|vv| * WW) := mul_le_mul_of_nonneg_right hG' (by positivity)
  obtain ⟨δa, hδa, haeq⟩ := ha.exists_delta
  obtain ⟨δb, hδb, hbeq⟩ := hb.exists_delta
  obtain ⟨δc, hδc, hceq⟩ := hc.exists_delta
  obtain ⟨δd, hδd, heeq⟩ := he.exists_delta
  have hα : |a - vr * ws| ≤ G' * (|vr| * Ws) := by
    rw [haeq, show vhr * whs * (1 + δa) = vhr * (1 + δa) * whs by ring]
    exact hprod hvr hws hws' hδa
  have hω : |c - wr * vs| ≤ G' * (|vs| * Wr) := by
    rw [hceq, show whr * vhs * (1 + δc) = vhs * (1 + δc) * whr by ring,
      show wr * vs = vs * wr by ring]
    exact hprod hvs hwr hwr' hδc
  have hαsz : |a| ≤ (1 + G') * (|vr| * Ws) := by
    have : |vr * ws| ≤ |vr| * Ws := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hws' (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub a (vr * ws)
    linarith
  have hωsz : |c| ≤ (1 + G') * (|vs| * Wr) := by
    have : |wr * vs| ≤ |vs| * Wr := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left hwr' (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub c (wr * vs)
    linarith
  have hη : |(1 + δb) * (1 + δd) - 1| ≤ gamma m.u 2 :=
    abs_one_add_mul_one_add_sub_one_le_gamma hu0 hu1 (k := 1) (hlt 2 (by omega))
      (hδb.trans (le_gamma_one hu0 hu1)) hδd
  rw [heeq, hbeq, show ((Brs - a) * (1 + δb) - c) * (1 + δd) - (Brs - vr * ws - wr * vs) =
      (Brs - a) * ((1 + δb) * (1 + δd) - 1) - (a - vr * ws) - (c - wr * vs) - c * δd by ring]
  have hX : |Brs - a| ≤ |Brs| + (1 + G') * (|vr| * Ws) := (abs_sub _ _).trans (by linarith)
  have e1 : |(Brs - a) * ((1 + δb) * (1 + δd) - 1)| ≤
      (|Brs| + (1 + G') * (|vr| * Ws)) * gamma m.u 2 := by
    rw [abs_mul]
    exact mul_le_mul hX hη (abs_nonneg _) (by positivity)
  have e2 : |c * δd| ≤ (1 + G') * (|vs| * Wr) * m.u := by
    rw [abs_mul]
    exact mul_le_mul hωsz hδd (abs_nonneg _) (by positivity)
  have hγ2 : gamma m.u 2 ≤ H := gamma_mono hu0 (by omega) hcard
  have h2G' : gamma m.u 2 + G' + gamma m.u 2 * G' ≤ H := by
    have := gamma_add_gamma_add_mul_le hu0 (j := 2) (k := k + 1 + g) (hlt _ (by omega))
    rwa [show 2 + (k + 1 + g) = g + k + 3 by ring] at this
  have huG' : G' * (1 + m.u) + m.u ≤ H :=
    (gamma_mul_one_add_add_le hu0 hu1 (k := k + 1 + g) (hlt _ (by omega))).trans
      (gamma_mono hu0 (by omega) hcard)
  have hP0 : 0 ≤ |vr| * Ws := by positivity
  have hR0 : 0 ≤ |vs| * Wr := by positivity
  have t1 : gamma m.u 2 * |Brs| ≤ H * |Brs| := mul_le_mul_of_nonneg_right hγ2 (abs_nonneg _)
  have t2 : (gamma m.u 2 + G' + gamma m.u 2 * G') * (|vr| * Ws) ≤ H * (|vr| * Ws) :=
    mul_le_mul_of_nonneg_right h2G' hP0
  have t3 : (G' * (1 + m.u) + m.u) * (|vs| * Wr) ≤ H * (|vs| * Wr) :=
    mul_le_mul_of_nonneg_right huG' hR0
  calc |(Brs - a) * ((1 + δb) * (1 + δd) - 1) - (a - vr * ws) - (c - wr * vs) - c * δd|
      ≤ |(Brs - a) * ((1 + δb) * (1 + δd) - 1)| + |a - vr * ws| + |c - wr * vs| + |c * δd| :=
        (abs_sub _ _).trans (add_le_add_left ((abs_sub _ _).trans
          (add_le_add_left (abs_sub _ _) _)) _)
    _ ≤ (|Brs| + (1 + G') * (|vr| * Ws)) * gamma m.u 2 + G' * (|vr| * Ws) +
        G' * (|vs| * Wr) + (1 + G') * (|vs| * Wr) * m.u := by linarith
    _ = gamma m.u 2 * |Brs| + (gamma m.u 2 + G' + gamma m.u 2 * G') * (|vr| * Ws) +
        (G' * (1 + m.u) + m.u) * (|vs| * Wr) := by ring
    _ ≤ H * |Brs| + H * (|vr| * Ws) + H * (|vs| * Wr) := by linarith
    _ = H * (|Brs| + |vr| * Ws + Wr * |vs|) := by ring

/-- A Frobenius bound from an entrywise one: `|E_ij| ≤ c (|B_ij| + x_i y_j + y_i x_j)` with `x, y`
nonnegative gives `‖E‖_F ≤ c (‖B‖_F + 2 ‖x‖₂ ‖y‖₂)`. -/
private theorem frobenius_norm_le_of_forall_abs_le_add_vecMulVec {E B : Matrix ι ι ℝ}
    {x y : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (h : ∀ i j, |E i j| ≤ c * (|B i j| + x i * y j + y i * x j)) :
    ‖E‖ ≤ c * (‖B‖ + 2 * (‖(toLp 2 x : EuclideanSpace ℝ ι)‖ *
      ‖(toLp 2 y : EuclideanSpace ℝ ι)‖)) := by
  set M := B.map abs + vecMulVec x y + vecMulVec y x with hM_def
  have hMe : ∀ i j, M i j = |B i j| + x i * y j + y i * x j := fun i j => by
    simp [hM_def, vecMulVec_apply]
  have hM : ∀ i j, |E i j| ≤ c * |M i j| := fun i j => by
    have h0 : 0 ≤ |B i j| + x i * y j + y i * x j := by
      have := hx i; have := hy j; have := hx j; have := hy i
      positivity
    rw [hMe, abs_of_nonneg h0]
    exact h i j
  refine (frobenius_norm_le_of_forall_abs_le hc hM).trans (mul_le_mul_of_nonneg_left ?_ hc)
  calc ‖M‖ ≤ ‖B.map abs‖ + ‖vecMulVec x y‖ + ‖vecMulVec y x‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ‖B‖ + ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ * ‖(toLp 2 y : EuclideanSpace ℝ ι)‖ +
        ‖(toLp 2 y : EuclideanSpace ℝ ι)‖ * ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ := by
      rw [frobenius_norm_map_eq B abs fun a => by simp]
      gcongr
      · exact frobenius_norm_vecMulVec_le _ _
      · exact frobenius_norm_vecMulVec_le _ _
    _ = _ := by ring

/-- The error of `ŵ_i = fl(p̂_i - τ̂_i)` in the symmetric rank-two update: with
`|p̂ - p| ≤ γ_A X`, `|τ̂ - τ| ≤ γ_C Y`, `|p| ≤ X`, `|τ| ≤ Y`, `γ_A ≤ γ_C` and one more rounding
`δ`, the error against `p - τ` is at most `(γ_C (1 + u) + u) (X + Y)`. -/
private theorem abs_sub_mul_one_add_sub_le {u γA γC X Y ph p τh τ δ : ℝ} (hγA : 0 ≤ γA)
    (hAC : γA ≤ γC) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hp : |ph - p| ≤ γA * X) (hτ : |τh - τ| ≤ γC * Y)
    (hpX : |p| ≤ X) (hτY : |τ| ≤ Y) (hδ : |δ| ≤ u) :
    |(ph - τh) * (1 + δ) - (p - τ)| ≤ (γC * (1 + u) + u) * (X + Y) := by
  have hu : 0 ≤ u := (abs_nonneg _).trans hδ
  have hγC : 0 ≤ γC := hγA.trans hAC
  have h4 : γA * X ≤ γC * X := mul_le_mul_of_nonneg_right hAC hX
  have hph : |ph| ≤ (1 + γC) * X := by
    have := abs_sub_abs_le_abs_sub ph p
    linarith
  have hτh : |τh| ≤ (1 + γC) * Y := by
    have := abs_sub_abs_le_abs_sub τh τ
    linarith
  have h3 : |(ph - τh) * δ| ≤ (1 + γC) * (X + Y) * u := by
    rw [abs_mul]
    exact mul_le_mul ((abs_sub _ _).trans (by linarith)) hδ (abs_nonneg _) (by positivity)
  rw [show (ph - τh) * (1 + δ) - (p - τ) = (ph - p) - (τh - τ) + (ph - τh) * δ by ring]
  calc |ph - p - (τh - τ) + (ph - τh) * δ|
      ≤ |ph - p| + |τh - τ| + |(ph - τh) * δ| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ γC * X + γC * Y + (1 + γC) * (X + Y) * u := by linarith
    _ = (γC * (1 + u) + u) * (X + Y) := by ring

/-- The size estimate of the symmetric rank-two update: if `b ‖x‖² ≤ 2` (here `b = |β|`),
`‖B v‖ ≤ ‖B‖ ‖v‖`, `Q ≤ ‖v‖² ‖B‖` and `‖W‖ ≤ b ‖B v‖ + b² Q ‖v‖ / 2`, then `‖v‖ ‖W‖ ≤ 4 ‖B‖`. -/
private theorem mul_le_four_mul_of_le {b x NB bv Q wn : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hNB : 0 ≤ NB) (hbx : b * x ^ 2 ≤ 2) (hbv : bv ≤ NB * x) (hQ : Q ≤ x * (NB * x))
    (hwn : wn ≤ b * bv + b * b * Q / 2 * x) : x * wn ≤ 4 * NB := by
  set y := b * x ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : x * wn ≤ x * (b * bv) + b * b * x * x / 2 * Q := by
    have := mul_le_mul_of_nonneg_left hwn hx
    linarith
  have h2 : x * (b * bv) ≤ y * NB := by
    have := mul_le_mul_of_nonneg_left hbv (mul_nonneg hx hb)
    rw [hy]
    linarith
  have h3 : b * b * x * x / 2 * Q ≤ y ^ 2 * NB / 2 := by
    have := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ b * b * x * x / 2)
    rw [hy]
    linarith
  have h4 : y ^ 2 ≤ 4 := by nlinarith
  have h5 : y * NB ≤ 2 * NB := mul_le_mul_of_nonneg_right hbx hNB
  have h6 : y ^ 2 * NB ≤ 4 * NB := mul_le_mul_of_nonneg_right h4 hNB
  linarith

/-- **Backward error of the computed symmetric rank-two update** ([golub2013matrix] §8.3.1): if
`(β̂, v̂)` are relative perturbations of order `k` of exact data `(β, v)` with `|β| ‖v‖₂² ≤ 2`,
`B` is symmetric, `(6k + 2n + 8) u < 1` and `RoundsSymmRankTwoUpdate m β̂ v̂ B B'`, then `B'` is
symmetric and `‖B' - P B P‖_F ≤ 9 γ_{6k+2n+8} ‖B‖_F` for `P = 1 - β v vᵀ`. Entrywise,
`|B'_ij - (P B P)_ij| ≤ γ (|B_ij| + |v_i| W_j + W_i |v_j|)` with `W_i = |β| (|B||v|)_i +
|β|² (|v|ᵀ|B||v|) |v_i| / 2` bounding `w` and its computed value, and `‖v‖₂ ‖W‖₂ ≤ 4 ‖B‖_F`
because `|β| ‖v‖₂² ≤ 2`. -/
theorem frobenius_norm_sub_le_of_roundsSymmRankTwoUpdate {m : RoundingModel ℝ} {k : ℕ}
    (hcard : ((6 * k + 2 * Fintype.card ι + 8 : ℕ) : ℝ) * m.u < 1) {β βhat : ℝ}
    {v vhat : ι → ℝ} (hβ : IsRelPert m.u k β βhat) (hv : ∀ i, IsRelPert m.u k (v i) (vhat i))
    (hP : |β| * (v ⬝ᵥ v) ≤ 2) {B B' : Matrix ι ι ℝ} (hB : Bᵀ = B)
    (h : RoundsSymmRankTwoUpdate m βhat vhat B B') :
    B'ᵀ = B' ∧ ‖B' - (1 - β • vecMulVec v v) * B * (1 - β • vecMulVec v v)‖ ≤
      9 * gamma m.u (6 * k + 2 * Fintype.card ι + 8) * ‖B‖ := by
  obtain ⟨phat, what, shat, that, hp, hs, ⟨t₁, ht₁, ht⟩, hw, hent, hsym⟩ := h
  refine ⟨Matrix.ext fun i j => hsym i j, ?_⟩
  set n := Fintype.card ι with hn_def
  set L := 6 * k + 2 * n + 8 with hL_def
  have hu0 := m.u_nonneg
  have hlt : ∀ j : ℕ, j ≤ L → ((j : ℕ) : ℝ) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hu0).trans_lt hcard
  have hu1 : m.u < 1 := by simpa using hlt 1 (by omega)
  have hγ : ∀ j : ℕ, j ≤ L → 0 ≤ gamma m.u j := fun j hj => gamma_nonneg hu0 (hlt j hj)
  -- `p̂_i`, as a sum of perturbed exact terms
  have hpc : ∀ i, ∃ c : ι → ℝ, phat i = ∑ j, c j ∧
      ∀ j, IsRelPert m.u (2 * k + n + 1) (β * B i j * v j) (c j) := fun i => by
    obtain ⟨r, hr, hpr⟩ := hp i
    obtain ⟨d, hd, hreq⟩ := exists_roundsDot_eq_dotProduct_add hu1 (hlt n (by omega)) hr
    obtain ⟨δ, hδ, hpeq⟩ := hpr.exists_delta
    refine ⟨fun j => βhat * (B i j + d j) * vhat j * (1 + δ), ?_, fun j => ?_⟩
    · rw [hpeq, hreq, dotProduct, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply]
      ring
    · have hBd : IsRelPert m.u n (B i j) (B i j + d j) :=
        isRelPert_of_abs_sub_le (hγ n (by omega)) (by rw [add_sub_cancel_left]; exact hd j)
      have h1 := hβ.mul hu0 (k := k) (j := n) (hlt _ (by omega)) hBd
      have h2 := h1.mul hu0 (k := k + n) (j := k) (hlt _ (by omega)) (hv j)
      have h3 := h2.mul_one_add hu0 hu1 (hlt (k + n + k + 1) (by omega)) hδ
      rwa [show k + n + k + 1 = 2 * k + n + 1 by ring] at h3
  choose c hc_sum hc_rel using hpc
  -- `ŝ`
  obtain ⟨e, he_sum, he_rel⟩ : ∃ e : ι → ι → ℝ, shat = ∑ a, ∑ b, e a b ∧
      ∀ a b, IsRelPert m.u (3 * k + 2 * n + 1) (β * B a b * v b * v a) (e a b) := by
    obtain ⟨d, hd, hseq⟩ := exists_roundsDot_eq_dotProduct_add hu1 (hlt n (by omega)) hs
    have hθ : ∀ a, IsRelPert m.u n (phat a) (phat a + d a) := fun a =>
      isRelPert_of_abs_sub_le (hγ n (by omega)) (by rw [add_sub_cancel_left]; exact hd a)
    choose θ hθb hθe using hθ
    refine ⟨fun a b => c a b * (vhat a * (1 + θ a)), ?_, fun a b => ?_⟩
    · rw [hseq, dotProduct]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Pi.add_apply, hθe a, hc_sum a, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    · have hva : IsRelPert m.u (k + n) (v a) (vhat a * (1 + θ a)) :=
        (hv a).trans hu0 (hlt _ (by omega)) ⟨θ a, hθb a, rfl⟩
      have := (hc_rel a b).mul hu0 (k := 2 * k + n + 1) (j := k + n) (hlt _ (by omega)) hva
      rwa [show 2 * k + n + 1 + (k + n) = 3 * k + 2 * n + 1 by ring] at this
  -- `t̂`
  obtain ⟨δ₁, hδ₁, ht₁eq⟩ := ht₁.exists_delta
  obtain ⟨δ₂, hδ₂, hteq⟩ := ht.exists_delta
  set f := βhat * (1 + δ₁) * (1 + δ₂) / 2 with hf_def
  have hf : IsRelPert m.u (k + 2) (β / 2) f := by
    obtain ⟨θ, hθ, hθe⟩ := (hβ.mul_one_add hu0 hu1 (hlt (k + 1) (by omega)) hδ₁).mul_one_add
      hu0 hu1 (hlt (k + 1 + 1) (by omega)) hδ₂
    exact ⟨θ, hθ, by rw [hf_def, hθe]; ring⟩
  have hts : that = f * shat := by rw [hteq, ht₁eq, hf_def]; ring
  -- `τ̂_i = fl(t̂ v̂_i)` and `ŵ_i`
  choose τ hτ hwhat using hw
  choose δ₃ hδ₃ hτeq using fun i => (hτ i).exists_delta
  choose δ₄ hδ₄ hweq using fun i => (hwhat i).exists_delta
  have hτrel : ∀ i a b, IsRelPert m.u (5 * k + 2 * n + 4)
      (β / 2 * (β * B a b * v b * v a) * v i) (f * e a b * (vhat i * (1 + δ₃ i))) :=
    fun i a b => by
    have h1 := hf.mul hu0 (k := k + 2) (j := 3 * k + 2 * n + 1) (hlt _ (by omega)) (he_rel a b)
    have h2 := (hv i).mul_one_add hu0 hu1 (hlt (k + 1) (by omega)) (hδ₃ i)
    have h3 := h1.mul hu0 (k := k + 2 + (3 * k + 2 * n + 1)) (j := k + 1) (hlt _ (by omega)) h2
    rwa [show k + 2 + (3 * k + 2 * n + 1) + (k + 1) = 5 * k + 2 * n + 4 by ring] at h3
  have hτsum : ∀ i, τ i = ∑ a, ∑ b, f * e a b * (vhat i * (1 + δ₃ i)) := fun i => by
    rw [hτeq i, hts, he_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  -- the exact quantities and their sizes
  set p : ι → ℝ := fun i => ∑ j, β * B i j * v j with hp_def
  set tv : ι → ℝ := fun i => ∑ a, ∑ b, β / 2 * (β * B a b * v b * v a) * v i with htv_def
  set w : ι → ℝ := fun i => p i - tv i with hw_def
  set Bv : ι → ℝ := fun i => ∑ j, |B i j| * |v j| with hBv_def
  set Q : ℝ := ∑ a, |v a| * Bv a with hQ_def
  set W : ι → ℝ := fun i => |β| * Bv i + |β| * |β| * Q / 2 * |v i| with hW_def
  have hBv0 : ∀ i, 0 ≤ Bv i := fun i => Finset.sum_nonneg fun j _ => by positivity
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (hBv0 a)
  have hW0 : ∀ i, 0 ≤ W i := fun i => by have := hBv0 i; positivity
  have hpabs : ∀ i, ∑ j, |β * B i j * v j| = |β| * Bv i := fun i => by
    rw [hBv_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [abs_mul, abs_mul]; ring
  have htabs : ∀ i, ∑ a, ∑ b, |β / 2 * (β * B a b * v b * v a) * v i| =
      |β| * |β| * Q / 2 * |v i| := fun i => by
    rw [hQ_def, hBv_def]
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_div, abs_two]
    ring
  set γA := gamma m.u (2 * k + n + 1) with hγA_def
  set γC := gamma m.u (5 * k + 2 * n + 4) with hγC_def
  have hγAC : γA ≤ γC := gamma_mono hu0 (by omega) (hlt _ (by omega))
  have hγA0 : 0 ≤ γA := hγ _ (by omega)
  have hperr : ∀ i, |phat i - p i| ≤ γA * (|β| * Bv i) := fun i => by
    rw [hc_sum i, ← hpabs i]
    exact abs_sum_sub_sum_le (hc_rel i)
  have hpsz : ∀ i, |p i| ≤ |β| * Bv i := fun i => by
    rw [← hpabs i]
    exact Finset.abs_sum_le_sum_abs _ _
  have hτerr : ∀ i, |τ i - tv i| ≤ γC * (|β| * |β| * Q / 2 * |v i|) := fun i => by
    rw [hτsum i, ← htabs i, Finset.mul_sum, htv_def]
    simp only
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    exact (abs_sum_sub_sum_le (hτrel i a)).trans_eq rfl
  have htsz : ∀ i, |tv i| ≤ |β| * |β| * Q / 2 * |v i| := fun i => by
    rw [← htabs i]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _)
  set g := 5 * k + 2 * n + 5 with hg_def
  have hwerr : ∀ i, |what i - w i| ≤ gamma m.u g * W i := fun i => by
    rw [hweq i]
    have hstep : γC * (1 + m.u) + m.u ≤ gamma m.u g :=
      gamma_mul_one_add_add_le hu0 hu1 (hlt _ (by omega))
    have hX0 : 0 ≤ |β| * Bv i := by have := hBv0 i; positivity
    exact (abs_sub_mul_one_add_sub_le hγA0 hγAC hX0 (by have := hQ0; positivity) (hperr i)
      (hτerr i) (hpsz i) (htsz i) (hδ₄ i)).trans (mul_le_mul_of_nonneg_right hstep (hW0 i))
  have hwsz : ∀ i, |w i| ≤ W i := fun i =>
    (abs_sub _ _).trans (add_le_add (hpsz i) (htsz i))
  -- every entry
  have hentry : ∀ i j, |B' i j - (B i j - v i * w j - w i * v j)| ≤
      gamma m.u L * (|B i j| + |v i| * W j + W i * |v j|) := fun i j => by
    obtain ⟨r, s, hrs, a, b, c', ha, hb, hc, hbij⟩ := hent i j
    have key := abs_rounds_sub_sub_sub_le (k := k) (g := g) (hlt _ (by omega)) (hv r) (hv s)
      (hwerr r) (hwerr s) (hwsz r) (hwsz s) ha hb hc hbij
    rw [show g + k + 3 = L by omega] at key
    rcases hrs with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · rwa [hr, hs] at key
    · rw [hr, hs] at key
      have hBji : B j i = B i j := congrFun (congrFun hB i) j
      rw [hBji] at key
      convert key using 2
      · ring
      · ring
  -- the Frobenius norm
  have hPBP : (1 - β • vecMulVec v v) * B * (1 - β • vecMulVec v v) =
      B - vecMulVec v w - vecMulVec w v := by
    rw [one_sub_smul_vecMulVec_mul_mul_eq hB]
    have hweq' : β • (B *ᵥ v) - (β * (v ⬝ᵥ β • (B *ᵥ v)) / 2) • v = w := by
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hw_def, hp_def, htv_def, mulVec,
        dotProduct, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [hweq']
  have hE : ‖B' - (1 - β • vecMulVec v v) * B * (1 - β • vecMulVec v v)‖ ≤
      gamma m.u L * (‖B‖ + 2 * (‖(toLp 2 (fun i => |v i|) : EuclideanSpace ℝ ι)‖ *
        ‖(toLp 2 W : EuclideanSpace ℝ ι)‖)) := by
    rw [hPBP]
    refine frobenius_norm_le_of_forall_abs_le_add_vecMulVec (hγ L le_rfl)
      (fun i => abs_nonneg _) hW0 fun i j => ?_
    simp only [Matrix.sub_apply, vecMulVec_apply]
    convert hentry i j using 2
  refine hE.trans ?_
  -- the sizes: `‖v‖₂ ‖W‖₂ ≤ 4 ‖B‖_F`
  set x := ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ with hx_def
  have hx0 : 0 ≤ x := norm_nonneg _
  have hvabs : ‖(toLp 2 (fun i => |v i|) : EuclideanSpace ℝ ι)‖ = x := norm_toLp_abs v
  have hbx : |β| * x ^ 2 ≤ 2 := by rw [hx_def, ← dotProduct_self_eq_norm_sq]; exact hP
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  have hBvn : ‖(toLp 2 Bv : EuclideanSpace ℝ ι)‖ ≤ ‖B‖ * x := by
    have h1 := frobenius_norm_mulVec_le (B.map abs) (fun i => |v i|)
    rw [frobenius_norm_map_eq B abs fun a => by simp] at h1
    rw [← hvabs]
    exact h1
  have hQle : Q ≤ x * (‖B‖ * x) := by
    have h1 := abs_dotProduct_abs_le (fun i => |v i|) Bv
    have h2 : |(fun i => |v i|)| ⬝ᵥ |Bv| = Q := by
      rw [hQ_def, dotProduct]
      exact Finset.sum_congr rfl fun a _ => by
        simp only [Pi.abs_apply, abs_abs, abs_of_nonneg (hBv0 a)]
    rw [h2, hvabs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hBvn hx0)
  have hWn : ‖(toLp 2 W : EuclideanSpace ℝ ι)‖ ≤
      |β| * ‖(toLp 2 Bv : EuclideanSpace ℝ ι)‖ + |β| * |β| * Q / 2 * x := by
    have := norm_toLp_le_of_abs_le_add (z := W) (b := Bv) (v := v) (abs_nonneg β)
      (by positivity : 0 ≤ |β| * |β| * Q / 2) fun i => by
        rw [abs_of_nonneg (hW0 i), abs_of_nonneg (hBv0 i)]
    exact this
  have hxW : x * ‖(toLp 2 W : EuclideanSpace ℝ ι)‖ ≤ 4 * ‖B‖ :=
    mul_le_four_mul_of_le (abs_nonneg β) hx0 hB0 hbx hBvn hQle hWn
  rw [hvabs]
  have hγL := hγ L le_rfl
  calc gamma m.u L * (‖B‖ + 2 * (x * ‖(toLp 2 W : EuclideanSpace ℝ ι)‖))
      ≤ gamma m.u L * (9 * ‖B‖) := mul_le_mul_of_nonneg_left (by linarith) hγL
    _ = 9 * gamma m.u L * ‖B‖ := by ring

end SymmRankTwo

/-! ### The Householder reductions, for any reflector formula -/

section Pert

open scoped Matrix.Norms.Frobenius

variable {N : ℕ}

/-- **One step of the Householder reduction to Hessenberg form, in [golub2013matrix]'s
association and for any reflector-vector formula** (Algorithm 7.4.2, step `k`). With the active
rows `T = {i // k + 1 ≤ i}` and `x` the tail of column `k` on `T`: the computed reflector data
`(v̂, β̂)` are `IsReflectorPert` data for `x`; every column `j ≥ k` of `A` is updated on `T` by
`RoundsHouseholderApplyScaled`, the entries of column `k` in the rows `≥ k + 2` being set to zero
(the book stores the vector there; those entries are never read again), giving `C`, equal to `A`
in the rows outside `T` and in the columns `< k`; then every row of `C` is updated on the columns
of `T` by `RoundsHouseholderApplyScaled`, giving `B`, equal to `C` in the columns outside `T`. Rows
and columns outside `T` are not re-rounded, since the program never touches them. -/
def RoundsHessenbergStepPert (m : RoundingModel ℝ) (K : ℕ) {k : ℕ} (hk : k + 1 < N)
    (A B : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ (c : ℝ) (vhat : {i : Fin N // k + 1 ≤ (i : ℕ)} → ℝ) (βhat : ℝ)
    (C : Matrix (Fin N) (Fin N) ℝ),
    IsReflectorPert m.u K (fun i : {i : Fin N // k + 1 ≤ (i : ℕ)} => A i ⟨k, by omega⟩)
      ⟨⟨k + 1, hk⟩, le_rfl⟩ c vhat βhat ∧
    (∀ j : Fin N, k ≤ (j : ℕ) → ∃ y : {i : Fin N // k + 1 ≤ (i : ℕ)} → ℝ,
      RoundsHouseholderApplyScaled m βhat vhat
        (fun i : {i : Fin N // k + 1 ≤ (i : ℕ)} => A i j) y ∧
      ∀ i : {i : Fin N // k + 1 ≤ (i : ℕ)},
        C i j = if (j : ℕ) = k ∧ k + 2 ≤ (i : ℕ) then 0 else y i) ∧
    (∀ i j : Fin N, ((i : ℕ) < k + 1 ∨ (j : ℕ) < k) → C i j = A i j) ∧
    (∀ i : Fin N, ∃ z : {i : Fin N // k + 1 ≤ (i : ℕ)} → ℝ,
      RoundsHouseholderApplyScaled m βhat vhat
        (fun j : {i : Fin N // k + 1 ≤ (i : ℕ)} => C i j) z ∧
      ∀ j : {i : Fin N // k + 1 ≤ (i : ℕ)}, B i j = z j) ∧
    (∀ i j : Fin N, (j : ℕ) < k + 1 → B i j = C i j)

/-- **The Householder reduction to Hessenberg form, for any reflector formula**:
`Â_0 = A` and `Â_{k+1}` is a computed step `RoundsHessenbergStepPert` from `Â_k` for the
`N - 2` steps `k < N - 2`. -/
def RoundsHessenbergReducePert (m : RoundingModel ℝ) (K : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (Ahat : ℕ → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  Ahat 0 = A ∧ ∀ k (hk : k < N - 2),
    RoundsHessenbergStepPert m K (show k + 1 < N by omega) (Ahat k) (Ahat (k + 1))

/-- A computed step keeps the reduced columns: if `A` vanishes below the first subdiagonal in the
columns `j < k`, then `B` does in the columns `j < k + 1`. -/
theorem RoundsHessenbergStepPert.apply_eq_zero {m : RoundingModel ℝ} {K k : ℕ}
    {hk : k + 1 < N} {A B : Matrix (Fin N) (Fin N) ℝ} (h : RoundsHessenbergStepPert m K hk A B)
    (hA : ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → A i j = 0) (i j : Fin N)
    (hj : (j : ℕ) < k + 1) (hij : (j : ℕ) + 1 < (i : ℕ)) : B i j = 0 := by
  obtain ⟨c, vhat, βhat, C, -, hcol, hCA, -, hBC⟩ := h
  rw [hBC i j hj]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
  · rw [hCA i j (Or.inr hjk)]
    exact hA i j hjk hij
  · obtain ⟨y, -, hC⟩ := hcol j hjk.ge
    have := hC ⟨i, by omega⟩
    rw [ite_eq_left ⟨hjk, by simp; omega⟩] at this
    exact this

/-- **The backward error of one computed step of the Householder Hessenberg reduction, for any
reflector formula**: if `(3K + N + 3) u < 1` and `A` vanishes below the first subdiagonal in the
columns `< k`, there is a symmetric orthogonal `P`, the identity on the rows (and columns) `≤ k`
— the exact reflector of `IsReflectorPert`, extended by the identity — with
`‖B - P A P‖_F ≤ ((1 + ε)² - 1) ‖A‖_F`, `ε = 3 γ_{3K+N+3}`: Lemma 19.2 of [higham2002accuracy]
(`norm_sub_le_of_roundsHouseholderApplyScaled`) on each column and each row of the active block,
combined through the orthogonal invariance of the Frobenius norm. -/
theorem RoundsHessenbergStepPert.frobenius_norm_sub_le {m : RoundingModel ℝ} {K : ℕ}
    (hcard : ((3 * K + N + 3 : ℕ) : ℝ) * m.u < 1) {k : ℕ} {hk : k + 1 < N}
    {A B : Matrix (Fin N) (Fin N) ℝ} (h : RoundsHessenbergStepPert m K hk A B)
    (hA : ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → A i j = 0) :
    ∃ P ∈ Matrix.orthogonalGroup (Fin N) ℝ, Pᵀ = P ∧
      (∀ i j : Fin N, (i : ℕ) < k + 1 → P i j = (1 : Matrix (Fin N) (Fin N) ℝ) i j) ∧
      ‖B - P * A * P‖ ≤ ((1 + 3 * gamma m.u (3 * K + N + 3)) ^ 2 - 1) * ‖A‖ := by
  obtain ⟨c, vhat, βhat, C, ⟨v, β, hPorth, hPx, hβv, hβ, hv⟩, hcol, hCA, hrow, hBC⟩ := h
  set P := 1 - β • vecMulVec (extendByZero (fun i : Fin N => k + 1 ≤ (i : ℕ)) v)
    (extendByZero (fun i : Fin N => k + 1 ≤ (i : ℕ)) v) with hP_def
  set ε := 3 * gamma m.u (3 * K + N + 3) with hε_def
  have hu0 := m.u_nonneg
  have hε0 : 0 ≤ ε := by
    have := gamma_nonneg hu0 hcard
    positivity
  have hPo : P ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
    one_sub_smul_vecMulVec_extendByZero_mem_orthogonalGroup hPorth
  have hPs : Pᵀ = P := transpose_one_sub_smul_vecMulVec _ _
  have hTcard : Fintype.card {i : Fin N // k + 1 ≤ (i : ℕ)} ≤ N :=
    (Fintype.card_subtype_le _).trans (by simp)
  have hcardT :
      ((3 * K + Fintype.card {i : Fin N // k + 1 ≤ (i : ℕ)} + 3 : ℕ) : ℝ) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu0).trans_lt hcard
  have happly : ∀ b y : {i : Fin N // k + 1 ≤ (i : ℕ)} → ℝ,
      RoundsHouseholderApplyScaled m βhat vhat b y →
      ‖(toLp 2 (y - (1 - β • vecMulVec v v) *ᵥ b) :
        EuclideanSpace ℝ {i : Fin N // k + 1 ≤ (i : ℕ)})‖ ≤
        ε * ‖(toLp 2 b : EuclideanSpace ℝ {i : Fin N // k + 1 ≤ (i : ℕ)})‖ := fun b y hy =>
    (norm_sub_le_of_roundsHouseholderApplyScaled hcardT hβ hv hβv hy).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (gamma_mono hu0 (by omega) hcard) (by norm_num)) (norm_nonneg _))
  -- the column sweep
  have hcolb : ∀ j, ‖(toLp 2 ((C - P * A).col j) : EuclideanSpace ℝ (Fin N))‖ ≤
      ε * ‖(toLp 2 (A.col j) : EuclideanSpace ℝ (Fin N))‖ := fun j => by
    rw [col_sub_mul]
    rcases lt_or_ge (j : ℕ) k with hj | hj
    · have hzero : (fun b : {i : Fin N // k + 1 ≤ (i : ℕ)} => A.col j b) = 0 := funext fun b => by
        rw [col_apply, hA b j hj (by have := b.2; omega), Pi.zero_apply]
      refine norm_sub_one_sub_smul_vecMulVec_extendByZero_mulVec_le hε0 (y := 0)
        (fun r _ => hCA r j (Or.inr hj)) (fun a => ?_) ?_
      · change |C a j - _| ≤ _
        rw [hCA a j (Or.inr hj), hA a j hj (by have := a.2; omega), hzero]
        simp
      · rw [hzero]
        simp
    · obtain ⟨y, hy, hCy⟩ := hcol j hj
      refine norm_sub_one_sub_smul_vecMulVec_extendByZero_mulVec_le hε0 (y := y)
        (fun r hr => hCA r j (Or.inl (not_le.1 hr))) (fun a => ?_) (happly _ _ hy)
      rw [col_apply, hCy a]
      split_ifs with hc
      · have hjk : j = ⟨k, by omega⟩ := Fin.ext hc.1
        have hx : (fun b : {i : Fin N // k + 1 ≤ (i : ℕ)} => A.col j b) =
            fun b : {i : Fin N // k + 1 ≤ (i : ℕ)} => A b ⟨k, by omega⟩ := by
          funext b
          simp only [col_apply]
          exact congrArg (A b) hjk
        have hne : a ≠ ⟨⟨k + 1, hk⟩, le_rfl⟩ := fun e => by
          have := congrArg (fun b : {i : Fin N // k + 1 ≤ (i : ℕ)} => ((b : Fin N) : ℕ)) e
          simp only at this
          omega
        rw [hx, hPx, Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]
        simp
      · exact le_rfl
  have hCPA : ‖C - P * A‖ ≤ ε * ‖A‖ := frobenius_norm_le_of_forall_col_le hε0 hcolb
  -- the row sweep
  have hrowb : ∀ i, ‖(toLp 2 ((B - C * P).row i) : EuclideanSpace ℝ (Fin N))‖ ≤
      ε * ‖(toLp 2 (C.row i) : EuclideanSpace ℝ (Fin N))‖ := fun i => by
    rw [row_sub_mul, hPs]
    obtain ⟨z, hz, hBz⟩ := hrow i
    refine norm_sub_one_sub_smul_vecMulVec_extendByZero_mulVec_le hε0 (y := z)
      (fun r hr => hBC i r (not_le.1 hr)) (fun a => ?_) (happly _ _ hz)
    rw [row_apply, hBz a]
  have hBCP : ‖B - C * P‖ ≤ ε * ‖C‖ := frobenius_norm_le_of_forall_row_le hε0 hrowb
  -- combine
  refine ⟨P, hPo, hPs, fun i j hi =>
    one_sub_smul_vecMulVec_extendByZero_apply_of_not β v (not_le.2 hi) j, ?_⟩
  clear_value P
  have hPA : ‖P * A‖ = ‖A‖ := by
    simpa using frobenius_norm_orthogonal_mul_mul_orthogonal hPo A (one_mem _)
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hC : ‖C‖ ≤ (1 + ε) * ‖A‖ := by
    calc ‖C‖ = ‖P * A + (C - P * A)‖ := by congr 1; abel
      _ ≤ ‖P * A‖ + ‖C - P * A‖ := norm_add_le _ _
      _ ≤ ‖A‖ + ε * ‖A‖ := by rw [hPA]; linarith
      _ = (1 + ε) * ‖A‖ := by ring
  have hsplit : B - P * A * P = (B - C * P) + (C - P * A) * P := by
    rw [Matrix.sub_mul]
    abel
  have h2 : ‖(C - P * A) * P‖ = ‖C - P * A‖ := by
    simpa using frobenius_norm_orthogonal_mul_mul_orthogonal (one_mem _) (C - P * A) hPo
  calc ‖B - P * A * P‖ ≤ ‖B - C * P‖ + ‖(C - P * A) * P‖ := by
        rw [hsplit]
        exact norm_add_le _ _
    _ ≤ ε * ‖C‖ + ε * ‖A‖ := by rw [h2]; linarith
    _ ≤ ε * ((1 + ε) * ‖A‖) + ε * ‖A‖ := by gcongr
    _ = ((1 + ε) ^ 2 - 1) * ‖A‖ := by ring

/-- **Backward stability of the Householder Hessenberg reduction, for any reflector formula**
([golub2013matrix] §7.4.3, citing Wilkinson; [higham2002accuracy] Theorem 19.4): if
`(3K + N + 3) u < 1` and `2 (N - 2) ε < 1` for `ε = 3 γ_{3K+N+3}`, the computed
`Ĥ = Â_{N-2}` of `RoundsHessenbergReducePert` is upper Hessenberg and `Ĥ = Qᵀ (A + E) Q` with `Q`
orthogonal and `‖E‖_F ≤ γ_{2(N-2)}(ε) ‖A‖_F`, the book's `c n² u ‖A‖_F` with `c` explicit. -/
theorem exists_roundsHessenbergReducePert_eq {m : RoundingModel ℝ} {K : ℕ}
    (hcard : ((3 * K + N + 3 : ℕ) : ℝ) * m.u < 1)
    (hr : ((2 * (N - 2) : ℕ) : ℝ) * (3 * gamma m.u (3 * K + N + 3)) < 1)
    {A : Matrix (Fin N) (Fin N) ℝ} {Ahat : ℕ → Matrix (Fin N) (Fin N) ℝ}
    (h : RoundsHessenbergReducePert m K A Ahat) :
    (Ahat (N - 2)).IsUpperHessenberg ∧ ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ,
      ∃ E : Matrix (Fin N) (Fin N) ℝ, Ahat (N - 2) = Qᵀ * (A + E) * Q ∧
        ‖E‖ ≤ gamma (3 * gamma m.u (3 * K + N + 3)) (2 * (N - 2)) * ‖A‖ := by
  obtain ⟨h0, hstep⟩ := h
  set ε := 3 * gamma m.u (3 * K + N + 3) with hε_def
  have hε0 : 0 ≤ ε := by
    have := gamma_nonneg m.u_nonneg hcard
    positivity
  have hhess : ∀ k, k ≤ N - 2 → ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) →
      Ahat k i j = 0 := by
    intro k
    induction k with
    | zero => intro _ i j hj; omega
    | succ k ih =>
      intro hk i j hj hij
      exact (hstep k (by omega)).apply_eq_zero (ih (by omega)) i j hj hij
  refine ⟨fun i j ⟨l, hjl, hli⟩ => hhess (N - 2) le_rfl i j (by omega) (by
    have := Fin.lt_def.1 hjl
    have := Fin.lt_def.1 hli
    omega), ?_⟩
  have hε'0 : 0 ≤ (1 + ε) ^ 2 - 1 := by nlinarith
  obtain ⟨Q, hQ, E, hE, hEn⟩ := exists_eq_transpose_mul_add_mul_of_forall_step hε'0 (N - 2)
    fun k hk => by
      obtain ⟨P, hP, hPs, -, hb⟩ := (hstep k hk).frobenius_norm_sub_le hcard (hhess k hk.le)
      exact ⟨P, hP, hPs, hb⟩
  refine ⟨Q, hQ, E, by rw [hE, h0], ?_⟩
  rw [h0] at hEn
  refine hEn.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hpow : (1 + ((1 + ε) ^ 2 - 1)) ^ (N - 2) = (1 + ε) ^ (2 * (N - 2)) := by
    rw [add_sub_cancel, pow_mul]
  rw [hpow]
  exact one_add_pow_sub_one_le_gamma hε0 hr

/-- **One step of the Householder tridiagonalization of a symmetric matrix, for any reflector
formula** ([golub2013matrix] Algorithm 8.3.1, step `k`). With `T = {i // k + 1 ≤ i}` and `x` the
tail of column `k` on `T`: the computed `(v̂, β̂)` are `IsReflectorPert` data for `x` with the
target `+‖x‖₂` (the book's sign); the subdiagonal entry is the freshly computed norm,
`ν̂ = fl(√σ̂)` with `σ̂ = fl(xᵀx)` a `RoundsDot`, stored at `(k + 1, k)` and `(k, k + 1)` (the
book's `A(k+1, k) = ‖A(k+1:n, k)‖₂`, not the `μ` inside `house`, which `house` does not return); the
entries `(i, k)`, `(k, i)` for `i ≥ k + 2` are zero (the book leaves the vector there; they are
never read again); the trailing block `B(T, T)` is a `RoundsSymmRankTwoUpdate` of `A(T, T)`; and
every other entry — the rows and columns `< k` and the entry `(k, k)` — is copied from `A`. -/
def RoundsTridiagonalizeStepPert (m : RoundingModel ℝ) (K : ℕ) {k : ℕ} (hk : k + 1 < N)
    (A B : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ (vhat : {i : Fin N // k + 1 ≤ (i : ℕ)} → ℝ) (βhat σhat νhat : ℝ),
    IsReflectorPert m.u K (fun i : {i : Fin N // k + 1 ≤ (i : ℕ)} => A i ⟨k, by omega⟩)
      ⟨⟨k + 1, hk⟩, le_rfl⟩
      ‖(toLp 2 (fun i : {i : Fin N // k + 1 ≤ (i : ℕ)} => A i ⟨k, by omega⟩) :
        EuclideanSpace ℝ {i : Fin N // k + 1 ≤ (i : ℕ)})‖ vhat βhat ∧
    RoundsDot m (fun i : {i : Fin N // k + 1 ≤ (i : ℕ)} => A i ⟨k, by omega⟩)
      (fun i : {i : Fin N // k + 1 ≤ (i : ℕ)} => A i ⟨k, by omega⟩) σhat ∧
    m.Rounds (√σhat) νhat ∧
    B ⟨k + 1, hk⟩ ⟨k, by omega⟩ = νhat ∧ B ⟨k, by omega⟩ ⟨k + 1, hk⟩ = νhat ∧
    (∀ i : Fin N, k + 2 ≤ (i : ℕ) → B i ⟨k, by omega⟩ = 0 ∧ B ⟨k, by omega⟩ i = 0) ∧
    RoundsSymmRankTwoUpdate m βhat vhat
      (A.submatrix (Subtype.val : {i : Fin N // k + 1 ≤ (i : ℕ)} → Fin N) Subtype.val)
      (B.submatrix (Subtype.val : {i : Fin N // k + 1 ≤ (i : ℕ)} → Fin N) Subtype.val) ∧
    ∀ i j : Fin N, ((i : ℕ) < k ∨ (j : ℕ) < k ∨ ((i : ℕ) = k ∧ (j : ℕ) = k)) → B i j = A i j

/-- **The Householder tridiagonalization of a symmetric matrix, for any reflector formula**:
`Â_0 = A` and `Â_{k+1}` is a computed step `RoundsTridiagonalizeStepPert` from `Â_k` for the
`N - 2` steps `k < N - 2`. -/
def RoundsTridiagonalizePert (m : RoundingModel ℝ) (K : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (Ahat : ℕ → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  Ahat 0 = A ∧ ∀ k (hk : k < N - 2),
    RoundsTridiagonalizeStepPert m K (show k + 1 < N by omega) (Ahat k) (Ahat (k + 1))

/-- A computed tridiagonalization step of a symmetric matrix is symmetric: the trailing block is
mirrored, the two subdiagonal entries are both `ν̂`, the entries of row and column `k` beyond are
both zero, and the rest is copied from the symmetric `A`. -/
theorem RoundsTridiagonalizeStepPert.transpose_eq {m : RoundingModel ℝ} {K k : ℕ}
    {hk : k + 1 < N} {A B : Matrix (Fin N) (Fin N) ℝ}
    (h : RoundsTridiagonalizeStepPert m K hk A B) (hAs : Aᵀ = A) : Bᵀ = B := by
  obtain ⟨vhat, βhat, σhat, νhat, -, -, -, hB1, hB2, hB0, hupd, hcopy⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, hBTs⟩ := hupd
  ext i j
  rw [transpose_apply]
  have hA' : A j i = A i j := congrFun (congrFun hAs i) j
  rcases lt_or_ge (i : ℕ) k with hi | hi
  · rw [hcopy i j (Or.inl hi), hcopy j i (Or.inr (Or.inl hi)), hA']
  rcases lt_or_ge (j : ℕ) k with hj | hj
  · rw [hcopy i j (Or.inr (Or.inl hj)), hcopy j i (Or.inl hj), hA']
  rcases eq_or_lt_of_le hi with hi | hi <;> rcases eq_or_lt_of_le hj with hj | hj
  · rw [hcopy i j (Or.inr (Or.inr ⟨hi.symm, hj.symm⟩)),
      hcopy j i (Or.inr (Or.inr ⟨hj.symm, hi.symm⟩)), hA']
  · have hi' : i = ⟨k, by omega⟩ := Fin.ext hi.symm
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with hj' | hj'
    · have hj'' : j = ⟨k + 1, hk⟩ := Fin.ext hj'.symm
      rw [hi', hj'', hB1, hB2]
    · rw [hi', (hB0 j hj').1, (hB0 j hj').2]
  · have hj' : j = ⟨k, by omega⟩ := Fin.ext hj.symm
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hi) with hi' | hi'
    · have hi'' : i = ⟨k + 1, hk⟩ := Fin.ext hi'.symm
      rw [hj', hi'', hB1, hB2]
    · rw [hj', (hB0 i hi').1, (hB0 i hi').2]
  · exact hBTs ⟨i, hi⟩ ⟨j, hj⟩

/-- A computed tridiagonalization step keeps the reduced columns: if `A` vanishes below the first
subdiagonal in the columns `< k`, then `B` does in the columns `< k + 1`. -/
theorem RoundsTridiagonalizeStepPert.apply_eq_zero {m : RoundingModel ℝ} {K k : ℕ}
    {hk : k + 1 < N} {A B : Matrix (Fin N) (Fin N) ℝ}
    (h : RoundsTridiagonalizeStepPert m K hk A B)
    (hA : ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → A i j = 0) (i j : Fin N)
    (hj : (j : ℕ) < k + 1) (hij : (j : ℕ) + 1 < (i : ℕ)) : B i j = 0 := by
  obtain ⟨vhat, βhat, σhat, νhat, -, -, -, -, -, hB0, -, hcopy⟩ := h
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
  · rw [hcopy i j (Or.inr (Or.inl hjk))]
    exact hA i j hjk hij
  · have : j = ⟨k, by omega⟩ := Fin.ext hjk
    rw [this]
    exact (hB0 i (by omega)).1

/-- **One computed step of the Householder tridiagonalization**: for a symmetric `A` vanishing
below the first subdiagonal in the columns `< k` and `(6K + 2N + 8) u < 1`, there is a symmetric
orthogonal `P` (the exact reflector of the step, extended by the identity) with
`‖B - P A P‖_F ≤ (9 γ_{6K+2N+8} + 2 γ_{N+1}) ‖A‖_F`: the trailing block by
`frobenius_norm_sub_le_of_roundsSymmRankTwoUpdate`, the two subdiagonal entries by the error of
the computed norm (`P x = ‖x‖₂ e_{k+1}` against `ν̂`), everything else exact. -/
theorem RoundsTridiagonalizeStepPert.frobenius_norm_sub_le {m : RoundingModel ℝ} {K : ℕ}
    (hcard : ((6 * K + 2 * N + 8 : ℕ) : ℝ) * m.u < 1) {k : ℕ} {hk : k + 1 < N}
    {A B : Matrix (Fin N) (Fin N) ℝ} (h : RoundsTridiagonalizeStepPert m K hk A B)
    (hAs : Aᵀ = A) (hA : ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → A i j = 0) :
    ∃ P ∈ Matrix.orthogonalGroup (Fin N) ℝ, Pᵀ = P ∧
      ‖B - P * A * P‖ ≤ (9 * gamma m.u (6 * K + 2 * N + 8) + 2 * gamma m.u (N + 1)) * ‖A‖ := by
  obtain ⟨vhat, βhat, σhat, νhat, ⟨v, β, hPorth, hPx, hβv, hβ, hv⟩, hσ, hν, hB1, hB2, hB0,
    hupd, hcopy⟩ := h
  have hu0 := m.u_nonneg
  have hTcard : Fintype.card {i : Fin N // k + 1 ≤ (i : ℕ)} ≤ N :=
    (Fintype.card_subtype_le _).trans (by simp)
  have hAT : (A.submatrix (Subtype.val : {i : Fin N // k + 1 ≤ (i : ℕ)} → Fin N)
      (Subtype.val : {i : Fin N // k + 1 ≤ (i : ℕ)} → Fin N))ᵀ =
        A.submatrix Subtype.val Subtype.val := by
    rw [transpose_submatrix, hAs]
  have hcardT : ((6 * K + 2 * Fintype.card {i : Fin N // k + 1 ≤ (i : ℕ)} + 8 : ℕ) : ℝ) *
      m.u < 1 := (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu0).trans_lt hcard
  obtain ⟨-, hBT⟩ := frobenius_norm_sub_le_of_roundsSymmRankTwoUpdate hcardT hβ hv hβv hAT hupd
  set kk : Fin N := ⟨k, by omega⟩ with hkk
  set k1 : Fin N := ⟨k + 1, hk⟩ with hk1
  have hkkv : (kk : ℕ) = k := rfl
  have hk1v : (k1 : ℕ) = k + 1 := rfl
  have hkT : ¬ k + 1 ≤ (kk : ℕ) := by omega
  have hkk1 : kk ≠ k1 := fun h => by
    have := congrArg Fin.val h
    omega
  -- the exact reflector, extended by the identity
  set P := 1 - β • vecMulVec (extendByZero (fun i : Fin N => k + 1 ≤ (i : ℕ)) v)
    (extendByZero (fun i : Fin N => k + 1 ≤ (i : ℕ)) v) with hP_def
  have hPo : P ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
    one_sub_smul_vecMulVec_extendByZero_mem_orthogonalGroup hPorth
  refine ⟨P, hPo, transpose_one_sub_smul_vecMulVec _ _, ?_⟩
  set x : {i : Fin N // k + 1 ≤ (i : ℕ)} → ℝ := fun i => A i kk with hx_def
  set nx := ‖(toLp 2 x : EuclideanSpace ℝ {i : Fin N // k + 1 ≤ (i : ℕ)})‖ with hnx
  -- the reflected column `k` and the reduced columns `< k`, on the block
  have hcolk : ∀ a : {i : Fin N // k + 1 ≤ (i : ℕ)},
      ((1 - β • vecMulVec v v) *ᵥ fun b : {i : Fin N // k + 1 ≤ (i : ℕ)} => A b kk) a =
        if (a : Fin N) = k1 then nx else 0 := fun a => by
    rw [show (fun b : {i : Fin N // k + 1 ≤ (i : ℕ)} => A b kk) = x from rfl, hPx,
      Pi.smul_apply, smul_eq_mul]
    by_cases ha : (a : Fin N) = k1
    · rw [ite_eq_left ha, show a = ⟨k1, le_rfl⟩ from Subtype.ext ha, Pi.single_eq_same, mul_one]
    · rw [ite_eq_right ha, Pi.single_eq_of_ne (fun h => ha (congrArg Subtype.val h)), mul_zero]
  have hcollt : ∀ (a : {i : Fin N // k + 1 ≤ (i : ℕ)}) (j : Fin N), (j : ℕ) < k →
      ((1 - β • vecMulVec v v) *ᵥ fun b : {i : Fin N // k + 1 ≤ (i : ℕ)} => A b j) a = 0 :=
    fun a j hj => by
    have : (fun b : {i : Fin N // k + 1 ≤ (i : ℕ)} => A b j) = 0 := funext fun b => by
      rw [hA b j hj (by have := b.2; omega), Pi.zero_apply]
    rw [this, mulVec_zero, Pi.zero_apply]
  -- the error splits into the trailing block and the two subdiagonal entries
  set δ := νhat - nx with hδ_def
  set D₂ : Matrix (Fin N) (Fin N) ℝ := δ • (vecMulVec (Pi.single k1 1) (Pi.single kk 1) +
    vecMulVec (Pi.single kk 1) (Pi.single k1 1)) with hD₂_def
  have hD₂e : ∀ i j, D₂ i j =
      if i = k1 ∧ j = kk then δ else if i = kk ∧ j = k1 then δ else 0 := fun i j =>
    smul_vecMulVec_single_add_apply hkk1 δ i j
  set D₁ := B - P * A * P - D₂ with hD₁_def
  have hD₁out : ∀ i j : Fin N, ¬ (k + 1 ≤ (i : ℕ) ∧ k + 1 ≤ (j : ℕ)) → D₁ i j = 0 :=
    fun i j hij => by
    rw [hD₁_def, Matrix.sub_apply, Matrix.sub_apply, hD₂e]
    by_cases hi : k + 1 ≤ (i : ℕ)
    · have hj : ¬ k + 1 ≤ (j : ℕ) := fun hj => hij ⟨hi, hj⟩
      have hik : i ≠ kk := fun h => hkT (h ▸ hi)
      rw [show (P * A * P) i j = _ from
        conj_extendByZero_apply_of_not_right β v A ⟨i, hi⟩ hj]
      rcases lt_or_ge (j : ℕ) k with hjk | hjk
      · have hjkk : j ≠ kk := fun h => by rw [h] at hjk; omega
        rw [hcollt ⟨i, hi⟩ j hjk, hcopy i j (Or.inr (Or.inl hjk)), hA i j hjk (by omega)]
        simp only [hjkk, hik, and_false, false_and, ite_false]
        ring
      · have hjk' : j = kk := Fin.ext (by omega)
        rw [hjk', hcolk ⟨i, hi⟩]
        by_cases hik1 : i = k1
        · rw [ite_eq_left hik1, hik1, hB1, ite_eq_left ⟨rfl, rfl⟩, hδ_def]
          ring
        · have hi2 : k + 2 ≤ (i : ℕ) := by
            have : (i : ℕ) ≠ k + 1 := fun h => hik1 (Fin.ext h)
            omega
          rw [ite_eq_right hik1, (hB0 i hi2).1]
          simp only [hik1, hik, false_and, ite_false]
          ring
    · by_cases hj : k + 1 ≤ (j : ℕ)
      · have hjk : j ≠ kk := fun h => hkT (h ▸ hj)
        rw [show (P * A * P) i j = _ from
          conj_extendByZero_apply_of_not_left β v A hi ⟨j, hj⟩]
        have hAi : (fun c : {i : Fin N // k + 1 ≤ (i : ℕ)} => A i c) =
            fun c : {i : Fin N // k + 1 ≤ (i : ℕ)} => A c i :=
          funext fun c => (congrFun (congrFun hAs i) c).symm
        rw [hAi]
        rcases lt_or_ge (i : ℕ) k with hik | hik
        · have hikk : i ≠ kk := fun h => by rw [h] at hik; omega
          rw [hcollt ⟨j, hj⟩ i hik, hcopy i j (Or.inl hik),
            ← congrFun (congrFun hAs i) j, transpose_apply, hA j i hik (by omega)]
          simp only [hikk, hjk, and_false, false_and, ite_false]
          ring
        · have hik' : i = kk := Fin.ext (by omega)
          rw [hik', hcolk ⟨j, hj⟩]
          by_cases hjk1 : j = k1
          · rw [ite_eq_left hjk1, hjk1, hB2, ite_eq_right (fun h => hkk1 h.1),
              ite_eq_left ⟨rfl, rfl⟩, hδ_def]
            ring
          · have hj2 : k + 2 ≤ (j : ℕ) := by
              have : (j : ℕ) ≠ k + 1 := fun h => hjk1 (Fin.ext h)
              omega
            rw [ite_eq_right hjk1, (hB0 j hj2).2]
            simp only [hjk1, hjk, and_false, ite_false]
            ring
      · rw [conj_extendByZero_apply_of_not_of_not β v A hi hj]
        have hc : (i : ℕ) < k ∨ (j : ℕ) < k ∨ ((i : ℕ) = k ∧ (j : ℕ) = k) := by omega
        have hi1 : i ≠ k1 := fun h => by rw [h] at hi; omega
        have hj1 : j ≠ k1 := fun h => by rw [h] at hj; omega
        rw [hcopy i j hc]
        simp only [hi1, hj1, and_false, false_and, ite_false]
        ring
  have hD₁in : D₁.submatrix (Subtype.val : {i : Fin N // k + 1 ≤ (i : ℕ)} → Fin N)
      (Subtype.val : {i : Fin N // k + 1 ≤ (i : ℕ)} → Fin N) =
        B.submatrix Subtype.val Subtype.val -
          (1 - β • vecMulVec v v) * A.submatrix Subtype.val Subtype.val *
            (1 - β • vecMulVec v v) := by
    ext a b
    have ha : (a : Fin N) ≠ kk := fun h => hkT (h ▸ a.2)
    have hb : (b : Fin N) ≠ kk := fun h => hkT (h ▸ b.2)
    rw [submatrix_apply, hD₁_def, Matrix.sub_apply, Matrix.sub_apply, hD₂e,
      conj_extendByZero_apply β v A a b]
    simp only [ha, hb, and_false, false_and, ite_false, sub_zero, Matrix.sub_apply,
      submatrix_apply]
  -- the computed norm
  have hxA : nx ≤ ‖A‖ := by
    refine (norm_toLp_restrict_le (p := fun i : Fin N => k + 1 ≤ (i : ℕ)) (A.col kk)).trans ?_
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [frobenius_norm_sq_eq_sum_col]
    exact Finset.single_le_sum (f := fun j => ‖(toLp 2 (A.col j) : EuclideanSpace ℝ _)‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ kk)
  have hδb : |δ| ≤ gamma m.u (N + 1) * ‖A‖ :=
    abs_rounds_sqrt_sub_norm_le hTcard
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu0).trans_lt hcard) hσ hν hxA
  have hD₂n : ‖D₂‖ ≤ 2 * |δ| := frobenius_norm_smul_vecMulVec_single_add_le δ k1 kk
  have hD₁n : ‖D₁‖ ≤ 9 * gamma m.u (6 * K + 2 * N + 8) * ‖A‖ := by
    rw [frobenius_norm_eq_submatrix (p := fun i : Fin N => k + 1 ≤ (i : ℕ)) hD₁out, hD₁in]
    refine hBT.trans (mul_le_mul (mul_le_mul_of_nonneg_left
      (gamma_mono hu0 (by omega) hcard) (by norm_num)) (frobenius_norm_submatrix_le A)
      (norm_nonneg _) (by have := gamma_nonneg hu0 hcard; positivity))
  calc ‖B - P * A * P‖ = ‖D₁ + D₂‖ := by rw [hD₁_def, sub_add_cancel]
    _ ≤ ‖D₁‖ + ‖D₂‖ := norm_add_le _ _
    _ ≤ 9 * gamma m.u (6 * K + 2 * N + 8) * ‖A‖ + 2 * (gamma m.u (N + 1) * ‖A‖) := by
        linarith
    _ = _ := by ring

/-- **The backward stability of the Householder tridiagonalization, for any reflector formula**
([golub2013matrix] §8.3.1 after Algorithm 8.3.1, citing Wilkinson; [higham2002accuracy]
Theorem 19.4 for the two-sided form): for a symmetric `A`, `(6K + 2N + 8) u < 1` and
`(N - 2) ε < 1` with `ε = 9 γ_{6K+2N+8} + 2 γ_{N+1}`, the computed `T̂ = Â_{N-2}` of
`RoundsTridiagonalizePert` is symmetric tridiagonal and `T̂ = Qᵀ (A + E) Q` with `Q` orthogonal,
`E` symmetric and `‖E‖_F ≤ γ_{N-2}(ε) ‖A‖_F`, the book's `c u ‖A‖_F` with `c` explicit. -/
theorem exists_roundsTridiagonalizePert_eq {m : RoundingModel ℝ} {K : ℕ}
    (hcard : ((6 * K + 2 * N + 8 : ℕ) : ℝ) * m.u < 1)
    (hr : ((N - 2 : ℕ) : ℝ) *
      (9 * gamma m.u (6 * K + 2 * N + 8) + 2 * gamma m.u (N + 1)) < 1)
    {A : Matrix (Fin N) (Fin N) ℝ} (hAs : Aᵀ = A) {Ahat : ℕ → Matrix (Fin N) (Fin N) ℝ}
    (h : RoundsTridiagonalizePert m K A Ahat) :
    (Ahat (N - 2))ᵀ = Ahat (N - 2) ∧ (Ahat (N - 2)).IsTridiagonal ∧
      ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∃ E : Matrix (Fin N) (Fin N) ℝ, Eᵀ = E ∧
        Ahat (N - 2) = Qᵀ * (A + E) * Q ∧
        ‖E‖ ≤ gamma (9 * gamma m.u (6 * K + 2 * N + 8) + 2 * gamma m.u (N + 1)) (N - 2) * ‖A‖ := by
  obtain ⟨h0, hstep⟩ := h
  set ε := 9 * gamma m.u (6 * K + 2 * N + 8) + 2 * gamma m.u (N + 1) with hε_def
  have hu0 := m.u_nonneg
  have hε0 : 0 ≤ ε := by
    have := gamma_nonneg hu0 hcard
    have := gamma_nonneg hu0 ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega : N + 1 ≤
      6 * K + 2 * N + 8)) hu0).trans_lt hcard)
    positivity
  have hinv : ∀ k, k ≤ N - 2 → (Ahat k)ᵀ = Ahat k ∧ ∀ i j : Fin N, (j : ℕ) < k →
      (j : ℕ) + 1 < (i : ℕ) → Ahat k i j = 0 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨h0 ▸ hAs, fun i j hj => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨hs, hz⟩ := ih (by omega)
      exact ⟨(hstep k (by omega)).transpose_eq hs, (hstep k (by omega)).apply_eq_zero hz⟩
  obtain ⟨hsN, hzN⟩ := hinv (N - 2) le_rfl
  have hlow : ∀ i j : Fin N, (j : ℕ) + 1 < (i : ℕ) → Ahat (N - 2) i j = 0 := fun i j hij =>
    hzN i j (by omega) hij
  refine ⟨hsN, fun i j hij => ?_, ?_⟩
  · rcases hij with ⟨l, hjl, hli⟩ | ⟨l, hil, hlj⟩
    · exact hlow i j (by have := Fin.lt_def.1 hjl; have := Fin.lt_def.1 hli; omega)
    · rw [← congrFun (congrFun hsN i) j, transpose_apply]
      exact hlow j i (by have := Fin.lt_def.1 hil; have := Fin.lt_def.1 hlj; omega)
  obtain ⟨Q, hQ, E, hE, hEn⟩ := exists_eq_transpose_mul_add_mul_of_forall_step hε0 (N - 2)
    fun k hk => by
      exact (hstep k hk).frobenius_norm_sub_le hcard (hinv k hk.le).1 (hinv k hk.le).2
  rw [h0] at hE hEn
  have hEs : Eᵀ = E := by
    have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hQ
    have hAE : A + E = Q * Ahat (N - 2) * Qᵀ := by
      rw [hE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_assoc,
        hQQ, Matrix.mul_one]
    have hsym : (A + E)ᵀ = A + E := by
      rw [hAE, transpose_mul, transpose_mul, transpose_transpose, hsN, Matrix.mul_assoc]
    rw [transpose_add, hAs] at hsym
    exact add_left_cancel hsym
  refine ⟨Q, hQ, E, hEs, hE, hEn.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
  exact one_add_pow_sub_one_le_gamma hε0 hr

end Pert

/-! ### Triangular solves with a matrix right-hand side -/

section TwoSided

open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **The forward error of a triangular solve with a matrix right-hand side**: if every column
of `Y` is computed by forward substitution from the corresponding column of `A` with the lower
triangular `T` (nonzero diagonal, `n u < 1`), then `‖Y - T⁻¹ A‖_F ≤ γ_n ‖T⁻¹‖_F ‖T‖_F ‖Y‖_F`.
Column by column this is [higham2002accuracy] Theorem 8.5, `(T + ΔT_j) y_j = a_j` with
`|ΔT_j| ≤ γ_n |T|`, solved for `y_j - T⁻¹ a_j = -T⁻¹ ΔT_j y_j`; the perturbation `ΔT_j` depends
on the column, which is why the result is a forward bound with the condition number
`‖T⁻¹‖_F ‖T‖_F` and not a single backward perturbation of `T`. -/
theorem frobenius_norm_sub_le_of_forall_roundsForwardSubst_col {m : RoundingModel ℝ}
    (hu : m.u < 1) (hcard : (Fintype.card n : ℝ) * m.u < 1) {T : Matrix n n ℝ}
    (hT : T.IsLowerTriangular) (hd : ∀ i, T i i ≠ 0) {A Y : Matrix n n ℝ}
    (h : ∀ j, RoundsForwardSubst m T (A.col j) (Y.col j)) :
    ‖Y - T⁻¹ * A‖ ≤ gamma m.u (Fintype.card n) * ‖T⁻¹‖ * ‖T‖ * ‖Y‖ := by
  have hγ := gamma_nonneg m.u_nonneg hcard
  have hTu : IsUnit T.det :=
    (isUnit_iff_isUnit_det T).1 ((isUnit_iff_forall_diag_ne_zero_of_isLowerTriangular hT).2 hd)
  refine frobenius_norm_le_of_forall_col_le (by positivity) fun j => ?_
  obtain ⟨ΔT, hΔ, hTy⟩ := exists_roundsForwardSubst_eq hu hcard hT hd (h j)
  have hΔn : ‖ΔT‖ ≤ gamma m.u (Fintype.card n) * ‖T‖ := frobenius_norm_le_of_forall_abs_le hγ hΔ
  have hcol : (Y - T⁻¹ * A).col j = -(T⁻¹ *ᵥ (ΔT *ᵥ Y.col j)) := by
    have h1 : T *ᵥ Y.col j + ΔT *ᵥ Y.col j = A.col j := by
      rw [← add_mulVec]; exact hTy
    have h2 : T⁻¹ *ᵥ (T *ᵥ Y.col j) = Y.col j := by
      rw [mulVec_mulVec, nonsing_inv_mul T hTu, one_mulVec]
    have h3 : (T⁻¹ * A).col j = T⁻¹ *ᵥ A.col j := by
      ext i; simp [col_apply, mul_apply, mulVec, dotProduct]
    have h4 : (Y - T⁻¹ * A).col j = Y.col j - (T⁻¹ * A).col j := by
      ext i; simp [col_apply]
    rw [h4, h3, ← h1, mulVec_add, h2]
    abel
  rw [hcol, WithLp.toLp_neg, norm_neg]
  calc ‖(toLp 2 (T⁻¹ *ᵥ (ΔT *ᵥ Y.col j)) : EuclideanSpace ℝ n)‖
      ≤ ‖T⁻¹‖ * ‖(toLp 2 (ΔT *ᵥ Y.col j) : EuclideanSpace ℝ n)‖ := frobenius_norm_mulVec_le _ _
    _ ≤ ‖T⁻¹‖ * (‖ΔT‖ * ‖(toLp 2 (Y.col j) : EuclideanSpace ℝ n)‖) :=
        mul_le_mul_of_nonneg_left (frobenius_norm_mulVec_le _ _) (norm_nonneg _)
    _ ≤ ‖T⁻¹‖ * ((gamma m.u (Fintype.card n) * ‖T‖) *
          ‖(toLp 2 (Y.col j) : EuclideanSpace ℝ n)‖) := by gcongr
    _ = gamma m.u (Fintype.card n) * ‖T⁻¹‖ * ‖T‖ * ‖(toLp 2 (Y.col j) : EuclideanSpace ℝ n)‖ := by
        ring


/-- The row form of `frobenius_norm_sub_le_of_forall_roundsForwardSubst_col`: if every row of
`C` is computed by forward substitution from the corresponding row of `Y` with the lower
triangular `T`, then `C ≈ Y T⁻ᵀ` with `‖C - Y T⁻ᵀ‖_F ≤ γ_n ‖T⁻¹‖_F ‖T‖_F ‖C‖_F`. -/
theorem frobenius_norm_sub_le_of_forall_roundsForwardSubst_row {m : RoundingModel ℝ}
    (hu : m.u < 1) (hcard : (Fintype.card n : ℝ) * m.u < 1) {T : Matrix n n ℝ}
    (hT : T.IsLowerTriangular) (hd : ∀ i, T i i ≠ 0) {Y C : Matrix n n ℝ}
    (h : ∀ i, RoundsForwardSubst m T (Y.row i) (C.row i)) :
    ‖C - Y * T⁻¹ᵀ‖ ≤ gamma m.u (Fintype.card n) * ‖T⁻¹‖ * ‖T‖ * ‖C‖ := by
  have := frobenius_norm_sub_le_of_forall_roundsForwardSubst_col hu hcard hT hd (A := Yᵀ)
    (Y := Cᵀ) fun j => h j
  rwa [← frobenius_norm_transpose, transpose_sub, transpose_transpose, transpose_mul,
    transpose_transpose, frobenius_norm_transpose C] at this

/-- **The two-sided triangular solve `C = H⁻ᵀ A H⁻¹` in floating-point arithmetic** (step 2 of
the QR–Cholesky algorithm of [quarteroni2000numerical] §5.9.2, with `H` the computed Cholesky
factor of `B`): `Y` solves `Hᵀ Y = A` column by column by forward substitution, and `C` solves
`C H = Y`, that is `Hᵀ Cᵀ = Yᵀ`, row by row by forward substitution. -/
def RoundsTwoSidedSolve (m : RoundingModel ℝ) (H A C : Matrix n n ℝ) : Prop :=
  ∃ Y : Matrix n n ℝ, (∀ j, RoundsForwardSubst m Hᵀ (A.col j) (Y.col j)) ∧
    ∀ i, RoundsForwardSubst m Hᵀ (Y.row i) (C.row i)

/-- **The forward error of the two-sided triangular solve** `Ĉ = fl(H⁻ᵀ A H⁻¹)`: for an upper
triangular `H` with nonzero diagonal, `n u < 1` and `θ = γ_n ‖H⁻¹‖_F ‖H‖_F < 1`,

`‖Ĉ - H⁻ᵀ A H⁻¹‖_F ≤ (2 θ / (1 - θ)²) ‖H⁻¹‖_F² ‖A‖_F`.

With `H` the Cholesky factor of `B`, `‖H⁻¹‖₂² = ‖B⁻¹‖₂`, so this is the
`u ‖A‖ ‖B⁻¹‖` of [quarteroni2000numerical] §5.9.2 *times the condition number* `κ(H)` hidden
in `θ`: the error of computing `C` is governed by `κ(H) = κ(B)^{1/2}` and not by `‖B⁻¹‖` alone,
which is the precise form of the book's "may become unstable if `B` is ill-conditioned". Each
solve is [higham2002accuracy] Theorem 8.5 column by column
(`frobenius_norm_sub_le_of_forall_roundsForwardSubst_col`, `…_row`), the two are combined by
`Ĉ - H⁻ᵀ A H⁻¹ = (Ĉ - Y H⁻¹) + (Y - H⁻ᵀ A) H⁻¹`, and the sizes of `Y` and `Ĉ` are bounded
through `‖Y‖ ≤ ‖H⁻¹‖ ‖A‖ / (1 - θ)`, `‖Ĉ‖ ≤ ‖H⁻¹‖ ‖Y‖ / (1 - θ)`. -/
theorem frobenius_norm_sub_le_of_roundsTwoSidedSolve {m : RoundingModel ℝ} (hu : m.u < 1)
    (hcard : (Fintype.card n : ℝ) * m.u < 1) {H : Matrix n n ℝ} (hH : H.IsUpperTriangular)
    (hd : ∀ i, H i i ≠ 0) {A C : Matrix n n ℝ} (h : RoundsTwoSidedSolve m H A C)
    (hθ : gamma m.u (Fintype.card n) * ‖H⁻¹‖ * ‖H‖ < 1) :
    ‖C - H⁻¹ᵀ * A * H⁻¹‖ ≤
      2 * (gamma m.u (Fintype.card n) * ‖H⁻¹‖ * ‖H‖) /
        (1 - gamma m.u (Fintype.card n) * ‖H⁻¹‖ * ‖H‖) ^ 2 * (‖H⁻¹‖ ^ 2 * ‖A‖) := by
  obtain ⟨Y, hY, hC⟩ := h
  set θ := gamma m.u (Fintype.card n) * ‖H⁻¹‖ * ‖H‖ with hθ_def
  have hγ := gamma_nonneg m.u_nonneg hcard
  have hθ0 : 0 ≤ θ := by positivity
  have h1θ : 0 < 1 - θ := by linarith
  have hTl : Hᵀ.IsLowerTriangular := fun i j hij => by
    rw [transpose_apply]
    exact hH (i := j) (j := i) (OrderDual.toDual_lt_toDual.1 hij)
  have hdT : ∀ i, Hᵀ i i ≠ 0 := fun i => by rw [transpose_apply]; exact hd i
  have hinvT : Hᵀ⁻¹ = H⁻¹ᵀ := (transpose_nonsing_inv H).symm
  have hnormT : ‖H⁻¹ᵀ‖ = ‖H⁻¹‖ := frobenius_norm_transpose H⁻¹
  have hnormH : ‖Hᵀ‖ = ‖H‖ := frobenius_norm_transpose H
  -- the two solves
  have h1 : ‖Y - H⁻¹ᵀ * A‖ ≤ θ * ‖Y‖ := by
    have := frobenius_norm_sub_le_of_forall_roundsForwardSubst_col hu hcard hTl hdT hY
    rwa [hinvT, hnormT, hnormH] at this
  have h2 : ‖C - Y * H⁻¹‖ ≤ θ * ‖C‖ := by
    have := frobenius_norm_sub_le_of_forall_roundsForwardSubst_row hu hcard hTl hdT hC
    rwa [hinvT, transpose_transpose, hnormT, hnormH] at this
  -- the sizes of `Y` and `C`
  have hHi : 0 ≤ ‖H⁻¹‖ := norm_nonneg _
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hYle : ‖Y‖ ≤ ‖H⁻¹‖ * ‖A‖ + θ * ‖Y‖ := by
    calc ‖Y‖ = ‖H⁻¹ᵀ * A + (Y - H⁻¹ᵀ * A)‖ := by congr 1; abel
      _ ≤ ‖H⁻¹ᵀ * A‖ + ‖Y - H⁻¹ᵀ * A‖ := norm_add_le _ _
      _ ≤ ‖H⁻¹‖ * ‖A‖ + θ * ‖Y‖ := by
          have := frobenius_norm_mul H⁻¹ᵀ A
          rw [hnormT] at this
          linarith
  have hCle : ‖C‖ ≤ ‖Y‖ * ‖H⁻¹‖ + θ * ‖C‖ := by
    calc ‖C‖ = ‖Y * H⁻¹ + (C - Y * H⁻¹)‖ := by congr 1; abel
      _ ≤ ‖Y * H⁻¹‖ + ‖C - Y * H⁻¹‖ := norm_add_le _ _
      _ ≤ ‖Y‖ * ‖H⁻¹‖ + θ * ‖C‖ := by linarith [frobenius_norm_mul Y H⁻¹]
  set S := ‖H⁻¹‖ ^ 2 * ‖A‖ with hS_def
  set Z := ‖Y‖ * ‖H⁻¹‖ with hZ_def
  have hS0 : 0 ≤ S := by positivity
  have hY'' : (1 - θ) * Z ≤ S := by
    have := mul_le_mul_of_nonneg_right (show (1 - θ) * ‖Y‖ ≤ ‖H⁻¹‖ * ‖A‖ by linarith) hHi
    rw [hZ_def, hS_def]
    linarith
  have hC'' : (1 - θ) * ‖C‖ ≤ Z := by rw [hZ_def]; linarith
  -- combine
  have hsplit : C - H⁻¹ᵀ * A * H⁻¹ = (C - Y * H⁻¹) + (Y - H⁻¹ᵀ * A) * H⁻¹ := by
    rw [Matrix.sub_mul]
    abel
  have hE : ‖C - H⁻¹ᵀ * A * H⁻¹‖ ≤ θ * ‖C‖ + θ * Z := by
    calc ‖C - H⁻¹ᵀ * A * H⁻¹‖ ≤ ‖C - Y * H⁻¹‖ + ‖(Y - H⁻¹ᵀ * A) * H⁻¹‖ := by
          rw [hsplit]
          exact norm_add_le _ _
      _ ≤ θ * ‖C‖ + ‖Y - H⁻¹ᵀ * A‖ * ‖H⁻¹‖ :=
          add_le_add h2 (frobenius_norm_mul _ _)
      _ ≤ θ * ‖C‖ + θ * Z := by
          have := mul_le_mul_of_nonneg_right h1 hHi
          rw [hZ_def]
          linarith
  -- `(1 - θ)² ‖E‖ ≤ θ (1 - θ) [(1 - θ) ‖C‖] + θ (1 - θ) [(1 - θ) Z] ≤ 2 θ S`
  have hsq : 0 < (1 - θ) ^ 2 := by positivity
  have hθ1θ : 0 ≤ θ * (1 - θ) := mul_nonneg hθ0 h1θ.le
  have e1 : (1 - θ) ^ 2 * ‖C - H⁻¹ᵀ * A * H⁻¹‖ ≤ (1 - θ) ^ 2 * (θ * ‖C‖ + θ * Z) :=
    mul_le_mul_of_nonneg_left hE hsq.le
  have e2 : (1 - θ) ^ 2 * (θ * ‖C‖ + θ * Z) =
      θ * (1 - θ) * ((1 - θ) * ‖C‖) + θ * (1 - θ) * ((1 - θ) * Z) := by ring
  have e3 : θ * (1 - θ) * ((1 - θ) * ‖C‖) ≤ θ * (1 - θ) * Z :=
    mul_le_mul_of_nonneg_left hC'' hθ1θ
  have e4 : θ * (1 - θ) * Z ≤ θ * S := by
    have := mul_le_mul_of_nonneg_left hY'' hθ0
    linarith
  have e5 : θ * (1 - θ) * ((1 - θ) * Z) ≤ θ * (1 - θ) * S :=
    mul_le_mul_of_nonneg_left hY'' hθ1θ
  have e6 : θ * (1 - θ) * S ≤ θ * S := by
    have h7 : θ * (1 - θ) ≤ θ := by
      have := sq_nonneg θ
      linarith
    exact mul_le_mul_of_nonneg_right h7 hS0
  rw [div_mul_eq_mul_div, le_div_iff₀ hsq]
  linarith

end TwoSided

end FloatingPoint
