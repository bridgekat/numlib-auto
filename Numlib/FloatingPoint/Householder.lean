import Numlib.FloatingPoint.LU
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
  `exists_eq_transpose_mul_add_mul_prodFwd`. The products are `FloatingPoint.prodRev P r =
  P_{r-1} ⋯ P_0` and `FloatingPoint.prodFwd P r = P_0 ⋯ P_{r-1}`.
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
  condition number of the Cholesky factor as well. The rounding model of the symmetric QR
  iteration itself (Givens rotations, [higham2002accuracy] §19.6) is not here, so the book's
  `λ̂ ∈ σ(H⁻ᵀ A H⁻¹ + E)` stays a surface note.

The scalar calculus of the constants is that of `Numlib/FloatingPoint/Model`; the lemmas
`IsRelPert.mul_one_add`, `IsRelPert.div_one_add`, `IsRelPert.rounds`, `IsRelPert.sqrt`,
`isRelPert_of_abs_sub_le` here extend it by the forms a Householder computation needs (one more
rounding as a multiplication or a division, a square root, a bound turned into a perturbation).
Everything is over `ℝ`, since the statements need the Euclidean and Frobenius norms.
-/

open Finset Matrix WithLp

open scoped Matrix

namespace FloatingPoint

section Scalar

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Rounding `0` gives `0`. -/
theorem RoundingModel.Rounds.eq_zero_of_zero {m : RoundingModel K} {y : K} (h : m.Rounds 0 y) :
    y = 0 := by
  have := m.abs_sub_le h
  rw [sub_zero, abs_zero, mul_zero] at this
  exact abs_nonpos_iff.1 this

/-- A bound `|y - x| ≤ γ_n |x|` is a relative perturbation of order `n`. -/
theorem isRelPert_of_abs_sub_le {u : K} {n : ℕ} (hγ : 0 ≤ gamma u n) {x y : K}
    (h : |y - x| ≤ gamma u n * |x|) : IsRelPert u n x y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [sub_zero, abs_zero, mul_zero] at h
    exact ⟨0, by simpa using hγ, by simp [abs_nonpos_iff.1 h]⟩
  · refine ⟨(y - x) / x, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.2 hx)]
      exact h
    · field_simp
      ring

/-- The error of a relative perturbation, `|y - x| ≤ γ_n |x|`. -/
theorem IsRelPert.abs_sub_le {u : K} {n : ℕ} {x y : K} (h : IsRelPert u n x y) :
    |y - x| ≤ gamma u n * |x| := by
  obtain ⟨θ, hθ, rfl⟩ := h
  rw [show x * (1 + θ) - x = θ * x by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)

omit [IsStrictOrderedRing K] in
/-- A relative perturbation is unchanged by a common factor. -/
theorem IsRelPert.const_mul {u : K} {n : ℕ} {x y : K} (h : IsRelPert u n x y) (c : K) :
    IsRelPert u n (c * x) (c * y) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  exact ⟨θ, hθ, by ring⟩

/-- A relative perturbation of `0` is `0`. -/
theorem IsRelPert.zero {u : K} {n : ℕ} (hγ : 0 ≤ gamma u n) : IsRelPert u n (0 : K) 0 :=
  ⟨0, by simpa using hγ, by simp⟩

/-- Multiplying a relative perturbation of order `k` by one rounding factor `1 + δ`, `|δ| ≤ u`:
order `k + 1`. -/
theorem IsRelPert.mul_one_add {u : K} (hu : 0 ≤ u) (hu1 : u < 1) {k : ℕ}
    (hk : ((k + 1 : ℕ) : K) * u < 1) {x y δ : K} (h : IsRelPert u k x y) (hδ : |δ| ≤ u) :
    IsRelPert u (k + 1) x (y * (1 + δ)) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  exact ⟨(1 + θ) * (1 + δ) - 1, abs_one_add_mul_one_add_sub_one_le_gamma hu hu1 hk hθ hδ,
    by ring⟩

/-- Dividing a relative perturbation of order `k` by one rounding factor `1 + δ`, `|δ| ≤ u`:
order `k + 1`. -/
theorem IsRelPert.div_one_add {u : K} (hu : 0 ≤ u) {k : ℕ}
    (hk : ((k + 1 : ℕ) : K) * u < 1) {x y δ : K} (h : IsRelPert u k x y) (hδ : |δ| ≤ u) :
    IsRelPert u (k + 1) x (y / (1 + δ)) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  refine ⟨(1 + θ) / (1 + δ) - 1, abs_one_add_div_one_add_sub_one_le_gamma hu hk hθ hδ, ?_⟩
  rw [show (1 : K) + ((1 + θ) / (1 + δ) - 1) = (1 + θ) / (1 + δ) by ring, mul_div_assoc]

/-- One more rounding raises the order of a relative perturbation by one. -/
theorem IsRelPert.rounds {m : RoundingModel K} (hu : m.u < 1) {k : ℕ}
    (hk : ((k + 1 : ℕ) : K) * m.u < 1) {x y z : K} (h : IsRelPert m.u k x y)
    (hz : m.Rounds y z) : IsRelPert m.u (k + 1) x z := by
  obtain ⟨δ, hδ, rfl⟩ := hz.exists_delta
  exact h.mul_one_add m.u_nonneg hu hk hδ

end Scalar

/-- `|√(1 + θ) - 1| ≤ |θ|` for `θ ≥ -1`. -/
theorem abs_sqrt_one_add_sub_one_le {θ : ℝ} (h : -1 ≤ θ) : |√(1 + θ) - 1| ≤ |θ| := by
  have h0 : 0 ≤ 1 + θ := by linarith
  have hs : 0 ≤ √(1 + θ) := Real.sqrt_nonneg _
  have hsq : √(1 + θ) ^ 2 = 1 + θ := Real.sq_sqrt h0
  have key : (√(1 + θ) - 1) * (√(1 + θ) + 1) = θ := by nlinarith
  have hpos : 1 ≤ √(1 + θ) + 1 := by linarith
  calc |√(1 + θ) - 1| ≤ |√(1 + θ) - 1| * (√(1 + θ) + 1) :=
        le_mul_of_one_le_right (abs_nonneg _) hpos
    _ = |(√(1 + θ) - 1) * (√(1 + θ) + 1)| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < √(1 + θ) + 1)]
    _ = |θ| := by rw [key]

/-- The square root of a relative perturbation of order `n` is one of order `n`, when `γ_n ≤ 1`.
-/
theorem IsRelPert.sqrt {u : ℝ} {n : ℕ} (hγ : gamma u n ≤ 1) {x y : ℝ} (hx : 0 ≤ x)
    (h : IsRelPert u n x y) : IsRelPert u n (√x) (√y) := by
  obtain ⟨θ, hθ, rfl⟩ := h
  have hθ1 : -1 ≤ θ := by linarith [neg_le_of_abs_le hθ]
  refine ⟨√(1 + θ) - 1, (abs_sqrt_one_add_sub_one_le hθ1).trans hθ, ?_⟩
  rw [Real.sqrt_mul hx, add_sub_cancel]

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


/-! ### The computed application of a reflector -/
/-- **The application of a Householder matrix in floating-point arithmetic**,
[higham2002accuracy] Lemma 19.2: `y = (I - β v vᵀ) b` computed as `b - v (β (vᵀ b))`. -/
def RoundsHouseholderApply (m : RoundingModel ℝ) (β : ℝ) (v b y : ι → ℝ) : Prop :=
  ∃ (s t : ℝ) (w : ι → ℝ), RoundsDot m v b s ∧ m.Rounds (β * s) t ∧
    (∀ i, m.Rounds (v i * t) (w i)) ∧ ∀ i, m.Rounds (b i - w i) (y i)

/-- The entries of `(1 - β v vᵀ) b`. -/
theorem one_sub_smul_vecMulVec_mulVec_apply (β : ℝ) (v b : ι → ℝ) (i : ι) :
    ((1 - β • vecMulVec v v) *ᵥ b) i = b i - β * v i * (v ⬝ᵥ b) := by
  rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul,
    Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

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
  have hγ : ∀ j : ℕ, j ≤ 3 * k + n + 3 → 0 ≤ gamma m.u j := fun j hj =>
    gamma_nonneg hu0 (hlt j hj)
  set γ' := gamma m.u (3 * k + n + 2) with hγ'_def
  set γ := gamma m.u (3 * k + n + 3) with hγ_def
  have hγ'0 : 0 ≤ γ' := hγ _ (by omega)
  have hγ0 : 0 ≤ γ := hγ _ le_rfl
  -- the rounding errors, one by one
  obtain ⟨dx, hdx, hseq⟩ := exists_roundsDot_eq_dotProduct_add hu1 (hlt n (by omega)) hs
  obtain ⟨δ₁, hδ₁, hteq⟩ := ht.exists_delta
  choose δ₂ hδ₂ hweq using fun i => (hw i).exists_delta
  choose δ₃ hδ₃ hyeq using fun i => (hy i).exists_delta
  -- the coefficients of `w i = ∑ j, c i j * b j` are relative perturbations of `β v i v j`
  have hβ' : IsRelPert m.u (k + 1) β (βhat * (1 + δ₁)) :=
    hβ.mul_one_add hu0 hu1 (hlt _ (by omega)) hδ₁
  have hvi' : ∀ i, IsRelPert m.u (k + 1) (v i) (vhat i * (1 + δ₂ i)) := fun i =>
    (hv i).mul_one_add hu0 hu1 (hlt _ (by omega)) (hδ₂ i)
  have hvj' : ∀ j, IsRelPert m.u (k + n) (v j) (vhat j + dx j) := fun j =>
    (hv j).trans hu0 (hlt _ (by omega))
      (isRelPert_of_abs_sub_le (hγ n (by omega)) (by rw [add_sub_cancel_left]; exact hdx j))
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
    calc |βhat * (1 + δ₁) * (vhat i * (1 + δ₂ i)) * (vhat j + dx j) * b j - β * v i * (v j * b j)|
        = |βhat * (1 + δ₁) * (vhat i * (1 + δ₂ i)) * (vhat j + dx j) - β * v i * v j| * |b j| := by
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
  have hstep : γ' * (1 + m.u) + m.u ≤ γ := gamma_mul_one_add_add_le hu0 hu1 hcard
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
  have hug : m.u ≤ γ := (le_gamma_one hu0 hu1).trans (gamma_mono hu0 (by omega) hcard)
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


/-! ### Products of orthogonal transformations -/

/-- `P (r-1) * ⋯ * P 1 * P 0`: the product of the first `r` transformations of a sequence,
each new one multiplying on the left. -/
def prodRev (P : ℕ → Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => 1
  | r + 1 => P r * prodRev P r

/-- `P 0 * P 1 * ⋯ * P (r-1)`: the product of the first `r` transformations of a sequence,
each new one multiplying on the right. -/
def prodFwd (P : ℕ → Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => 1
  | r + 1 => prodFwd P r * P r

/-- The empty product is the identity. -/
@[simp]
theorem prodRev_zero (P : ℕ → Matrix ι ι ℝ) : prodRev P 0 = 1 := rfl

/-- One more transformation on the left. -/
theorem prodRev_succ (P : ℕ → Matrix ι ι ℝ) (r : ℕ) : prodRev P (r + 1) = P r * prodRev P r :=
  rfl

/-- The empty product is the identity. -/
@[simp]
theorem prodFwd_zero (P : ℕ → Matrix ι ι ℝ) : prodFwd P 0 = 1 := rfl

/-- One more transformation on the right. -/
theorem prodFwd_succ (P : ℕ → Matrix ι ι ℝ) (r : ℕ) : prodFwd P (r + 1) = prodFwd P r * P r :=
  rfl

/-- The product of orthogonal matrices is orthogonal. -/
theorem prodRev_mem_orthogonalGroup {P : ℕ → Matrix ι ι ℝ}
    (hP : ∀ k, P k ∈ Matrix.orthogonalGroup ι ℝ) (r : ℕ) :
    prodRev P r ∈ Matrix.orthogonalGroup ι ℝ := by
  induction r with
  | zero => exact one_mem _
  | succ r ih => exact mul_mem (hP r) ih

/-- The product of orthogonal matrices is orthogonal. -/
theorem prodFwd_mem_orthogonalGroup {P : ℕ → Matrix ι ι ℝ}
    (hP : ∀ k, P k ∈ Matrix.orthogonalGroup ι ℝ) (r : ℕ) :
    prodFwd P r ∈ Matrix.orthogonalGroup ι ℝ := by
  induction r with
  | zero => exact one_mem _
  | succ r ih => exact mul_mem ih (hP r)

/-- The transpose of `prodFwd P r` is `prodRev Pᵀ r`. -/
theorem transpose_prodFwd (P : ℕ → Matrix ι ι ℝ) (r : ℕ) :
    (prodFwd P r)ᵀ = prodRev (fun k => (P k)ᵀ) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodFwd_succ, transpose_mul, ih, prodRev_succ]

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


/-- Orthogonal similarity (or equivalence) preserves the Frobenius norm. -/
theorem frobenius_norm_orthogonal_mul_mul_orthogonal {U V : Matrix ι ι ℝ}
    (hU : U ∈ Matrix.orthogonalGroup ι ℝ) (A : Matrix ι ι ℝ)
    (hV : V ∈ Matrix.orthogonalGroup ι ℝ) : ‖U * A * V‖ = ‖A‖ :=
  frobenius_norm_unitary_mul_mul_unitary hU A hV

/-- `Q (Qᵀ A) = A` for an orthogonal `Q`. -/
theorem mul_transpose_mul_of_mem_orthogonalGroup {Q : Matrix ι ι ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup ι ℝ) (A : Matrix ι ι ℝ) : Q * (Qᵀ * A) = A := by
  rw [← Matrix.mul_assoc, (mem_orthogonalGroup_iff _ _).1 hQ, Matrix.one_mul]

/-- `(A Qᵀ) Q = A` for an orthogonal `Q`. -/
theorem mul_transpose_mul_of_mem_orthogonalGroup' {Q : Matrix ι ι ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup ι ℝ) (A : Matrix ι ι ℝ) : A * Qᵀ * Q = A := by
  rw [Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hQ, Matrix.mul_one]

/-- **Two-sided accumulation** ([higham2002accuracy] §19.10, the two-sided analogue of Lemma
19.3, in the Frobenius norm): if `L_k`, `R_k` are orthogonal and
`‖A_{k+1} - L_k A_k R_k‖_F ≤ ε ‖A_k‖_F` for `k < r`, then
`A_r = (L_{r-1} ⋯ L_0) (A_0 + E) (R_0 ⋯ R_{r-1})` with `‖E‖_F ≤ ((1 + ε)^r - 1) ‖A_0‖_F`. -/
theorem exists_eq_prodRev_mul_add_mul_prodFwd {L R : ℕ → Matrix ι ι ℝ}
    (hL : ∀ k, L k ∈ Matrix.orthogonalGroup ι ℝ) (hR : ∀ k, R k ∈ Matrix.orthogonalGroup ι ℝ)
    {A : ℕ → Matrix ι ι ℝ} {ε : ℝ} (hε : 0 ≤ ε) (r : ℕ)
    (hA : ∀ k, k < r → ‖A (k + 1) - L k * A k * R k‖ ≤ ε * ‖A k‖) :
    ∃ E : Matrix ι ι ℝ, A r = prodRev L r * (A 0 + E) * prodFwd R r ∧
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

/-! ### Triangular solves with a matrix right-hand side -/

section TwoSided

open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- An entrywise bound `|A i j| ≤ c |B i j|` gives `‖A‖_F ≤ c ‖B‖_F`. -/
theorem frobenius_norm_le_of_forall_abs_le {A B : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) : ‖A‖ ≤ c * ‖B‖ := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2

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
