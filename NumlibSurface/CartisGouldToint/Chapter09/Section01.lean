import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Cartis–Gould–Toint §9.1: Matrix factorization

Surface file for [cartis2022evaluation] §9.1: Algorithm 9.1.1 computes the secular function
`π(λ)` and its derivatives from a factorization `H + λ M = L D Lᵀ` (9.1.1), justified by
Corollary 9.1.1 through Theorem 8.2.6. The algorithm is deterministic; it is formalized as the
function `algorithm_9_1_1 L D M g : ℕ → ℝ`, `j ↦ π⁽ʲ⁾(λ)`, with its vectors `algS`, `algY`,
`algZ`. Solves with `L`, `D`, `Lᵀ` are written with the matrix inverses. The book's loop bound
`k ≤ ⌈l_max/2⌉` computes a few values past `l_max`; here the output is defined for every `j` and
is read for `j ≤ l_max`.

## Corrections to the source

* The algorithm's right-hand side `L y⁽ᵏ⁺¹⁾ = (k + 1) M s⁽ᵏ⁾` has the opposite sign to (8.2.29), so
  its vectors are `s⁽ᵏ⁾_alg = (-1)ᵏ s⁽ᵏ⁾` (`algS_eq`); the computed values `π⁽ʲ⁾` are unaffected.
  The alternative expression `π⁽²ᵏ⁺¹⁾ = 2 αₖ ⟪s⁽ᵏ⁾, M s⁽ᵏ⁺¹⁾⟫` of Corollary 9.1.1 holds with the
  vectors of Theorem 8.2.6.
* For a Cholesky factorization (`D = I`) the odd derivatives are `π⁽²ᵏ⁺¹⁾ = -βₖ ‖y⁽ᵏ⁺¹⁾‖²`; the
  book's text has `-2 βₖ ‖y⁽ᵏ⁺¹⁾‖²`.
-/

open Matrix
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter09

open CartisGouldToint.Chapter08

variable {n : ℕ}

/-- The vectors `s⁽ᵏ⁾(λ)` of Algorithm 9.1.1 of [cartis2022evaluation]: `s⁽⁰⁾` solves
`L y = -g`, `D z = y`, `Lᵀ s = z`, and `s⁽ᵏ⁺¹⁾` solves `L y = (k + 1) M s⁽ᵏ⁾`, `D z = y`,
`Lᵀ s = z`. -/
noncomputable def algS (L D M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => toEuclideanLin Lᵀ⁻¹ (toEuclideanLin D⁻¹ (toEuclideanLin L⁻¹ (-g)))
  | k + 1 => toEuclideanLin Lᵀ⁻¹ (toEuclideanLin D⁻¹
      (toEuclideanLin L⁻¹ ((k + 1 : ℝ) • toEuclideanLin M (algS L D M g k))))

/-- The vectors `y⁽ᵏ⁺¹⁾(λ)` of Algorithm 9.1.1, solving `L y⁽ᵏ⁺¹⁾ = (k + 1) M s⁽ᵏ⁾`. -/
noncomputable def algY (L D M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin L⁻¹ ((k + 1 : ℝ) • toEuclideanLin M (algS L D M g k))

/-- The vectors `z⁽ᵏ⁺¹⁾(λ)` of Algorithm 9.1.1, solving `D z⁽ᵏ⁺¹⁾ = y⁽ᵏ⁺¹⁾`. -/
noncomputable def algZ (L D M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin D⁻¹ (algY L D M g k)

/-- The coefficients `βₖ = 2 αₖ/(k + 1)` of Algorithm 9.1.1 (with `αₖ = alphaCoeff k`, so that
`αₖ₊₁ = (2k + 3) βₖ`, `alphaCoeff_succ_eq`). -/
noncomputable def algBeta (k : ℕ) : ℝ := 2 * alphaCoeff k / (k + 1)

theorem alphaCoeff_succ_eq (k : ℕ) : alphaCoeff (k + 1) = (2 * k + 3) * algBeta k := by
  rw [alphaCoeff, algBeta]; ring

/-- **Algorithm 9.1.1 of [cartis2022evaluation]** (given `λ ∈ 𝓕` and `H + λ M = L D Lᵀ`, find
`π(λ)` and its derivatives): the output `j ↦ π⁽ʲ⁾(λ)`, with `π⁽⁰⁾ = ⟪s⁽⁰⁾, M s⁽⁰⁾⟫`,
`π⁽²ᵏ⁺¹⁾ = -βₖ ⟪y⁽ᵏ⁺¹⁾, z⁽ᵏ⁺¹⁾⟫` and `π⁽²ᵏ⁺²⁾ = αₖ₊₁ ⟪s⁽ᵏ⁺¹⁾, M s⁽ᵏ⁺¹⁾⟫`
(`algorithm_9_1_1_zero`, `algorithm_9_1_1_odd`, `algorithm_9_1_1_even`). -/
noncomputable def algorithm_9_1_1 (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) : ℕ → ℝ
  | 0 => ⟪algS L D M g 0, toEuclideanLin M (algS L D M g 0)⟫
  | j + 1 =>
    if Even j then -algBeta (j / 2) * ⟪algY L D M g (j / 2), algZ L D M g (j / 2)⟫
    else alphaCoeff (j / 2 + 1) *
      ⟪algS L D M g (j / 2 + 1), toEuclideanLin M (algS L D M g (j / 2 + 1))⟫

variable {L D M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

theorem algorithm_9_1_1_zero :
    algorithm_9_1_1 L D M g 0 = ⟪algS L D M g 0, toEuclideanLin M (algS L D M g 0)⟫ := rfl

theorem algorithm_9_1_1_odd (k : ℕ) :
    algorithm_9_1_1 L D M g (2 * k + 1) = -algBeta k * ⟪algY L D M g k, algZ L D M g k⟫ := by
  rw [algorithm_9_1_1, ite_eq_left (even_two_mul k), Nat.mul_div_cancel_left k two_pos]

theorem algorithm_9_1_1_even (k : ℕ) :
    algorithm_9_1_1 L D M g (2 * k + 2) =
      alphaCoeff (k + 1) * ⟪algS L D M g (k + 1), toEuclideanLin M (algS L D M g (k + 1))⟫ := by
  have h1 : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from rfl, algorithm_9_1_1, ite_eq_right h1, h2]

/-- With `H + λ M = L D Lᵀ`, the solves of Algorithm 9.1.1 compute `(H + λ M)⁻¹`. -/
theorem toEuclideanLin_inv_of_ldl {H : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} {d : Fin n → ℝ}
    (hfac : H + lam • M = L * diagonal d * Lᵀ) (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanLin (H + lam • M)⁻¹ x =
      toEuclideanLin Lᵀ⁻¹ (toEuclideanLin (diagonal d)⁻¹ (toEuclideanLin L⁻¹ x)) := by
  rw [hfac, Matrix.mul_inv_rev, Matrix.mul_inv_rev, toEuclideanLin_mul_apply,
    toEuclideanLin_mul_apply]

/-- The algorithm's vectors are `(-1)ᵏ` times the derivative vectors (8.2.29). -/
theorem algS_eq {H : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} {d : Fin n → ℝ}
    (hfac : H + lam • M = L * diagonal d * Lᵀ) (k : ℕ) :
    algS L (diagonal d) M g k = (-1 : ℝ) ^ k • secularDerivVec g H M lam k := by
  induction k with
  | zero => rw [algS, secularDerivVec, stepOf, toEuclideanLin_inv_of_ldl hfac, pow_zero, one_smul]
  | succ k ih =>
    rw [algS, secularDerivVec, toEuclideanLin_inv_of_ldl hfac, ih]
    simp only [map_smul, map_neg]
    module

/-- **Corollary 9.1.1 of [cartis2022evaluation] (Derivatives of the secular function via `LDLᵀ`
factors).** If `H + λ M` is positive definite with a factorization `H + λ M = L D Lᵀ`, `D`
diagonal, then Algorithm 9.1.1 provides the derivatives of `π`: `π⁽ʲ⁾(λ) = algorithm_9_1_1 j` for
every `j`. Its vectors are `(-1)ᵏ s⁽ᵏ⁾(λ)` with `s⁽ᵏ⁾` of (8.2.29); the odd derivatives are also
`2 αₖ ⟪s⁽ᵏ⁾(λ), M s⁽ᵏ⁺¹⁾(λ)⟫` (Theorem 8.2.6); and for a Cholesky factorization (`D = I`)
`π⁽²ᵏ⁺¹⁾(λ) = -βₖ ‖y⁽ᵏ⁺¹⁾(λ)‖²`. -/
theorem corollary_9_1_1 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) (hM : M.PosDef)
    {lam : ℝ} (hpd : (H + lam • M).PosDef) {d : Fin n → ℝ}
    (hfac : H + lam • M = L * diagonal d * Lᵀ) :
    (∀ j, algorithm_9_1_1 L (diagonal d) M g j = iteratedDeriv j (secularFn g H M) lam) ∧
    (∀ k, algS L (diagonal d) M g k = (-1 : ℝ) ^ k • secularDerivVec g H M lam k) ∧
    (∀ k, iteratedDeriv (2 * k + 1) (secularFn g H M) lam = 2 * alphaCoeff k *
        ⟪secularDerivVec g H M lam k, toEuclideanLin M (secularDerivVec g H M lam (k + 1))⟫) ∧
    (d = 1 → ∀ k, iteratedDeriv (2 * k + 1) (secularFn g H M) lam =
        -algBeta k * ‖algY L (diagonal d) M g k‖ ^ 2) := by
  have hMs := isSymmetric_toEuclideanLin_iff.2 hM.isHermitian
  have hS := algS_eq (g := g) hfac
  -- the odd outputs
  have hodd : ∀ k, algorithm_9_1_1 L (diagonal d) M g (2 * k + 1) =
      iteratedDeriv (2 * k + 1) (secularFn g H M) lam := by
    intro k
    have hyz : ⟪algY L (diagonal d) M g k, algZ L (diagonal d) M g k⟫ =
        (k + 1 : ℝ) * ⟪toEuclideanLin M (algS L (diagonal d) M g k),
          algS L (diagonal d) M g (k + 1)⟫ := by
      rw [algZ, algY, ← toEuclideanLin_transpose_inner_right, transpose_nonsing_inv, algS,
        inner_smul_left, RCLike.conj_to_real]
    rw [algorithm_9_1_1_odd, hyz, (theorem_8_2_6 hH hM hpd k).1, hS, hS]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    rw [← hMs, algBeta, pow_succ]
    generalize ⟪toEuclideanLin M (secularDerivVec g H M lam k),
      secularDerivVec g H M lam (k + 1)⟫ = I
    have h1 : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [show (-1 : ℝ) ^ k * -1 * ((-1) ^ k * I) = -I * ((-1) ^ k) ^ 2 by ring, h1]
    field_simp
  have heven : ∀ k, algorithm_9_1_1 L (diagonal d) M g (2 * k + 2) =
      iteratedDeriv (2 * k + 2) (secularFn g H M) lam := by
    intro k
    rw [algorithm_9_1_1_even, (theorem_8_2_6 hH hM hpd k).2, hS]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    generalize ⟪secularDerivVec g H M lam (k + 1),
      toEuclideanLin M (secularDerivVec g H M lam (k + 1))⟫ = I
    have h2 : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [show (-1 : ℝ) ^ (k + 1) * ((-1) ^ (k + 1) * I) = I * ((-1) ^ (k + 1)) ^ 2 by ring, h2,
      mul_one]
  refine ⟨fun j => ?_, hS, fun k => (theorem_8_2_6 hH hM hpd k).1, fun hd k => ?_⟩
  · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · rcases k with _ | k
      · rw [algorithm_9_1_1_zero, iteratedDeriv_zero, hS, pow_zero, one_smul, secularDerivVec,
          secularFn]
      · rw [show 2 * (k + 1) = 2 * k + 2 by ring]; exact heven k
    · exact hodd k
  · have h1 : diagonal (1 : Fin n → ℝ) = 1 := diagonal_one
    rw [← hodd, algorithm_9_1_1_odd, algZ, hd, h1, inv_one, toEuclideanLin_one_apply,
      real_inner_self_eq_norm_sq]

end CartisGouldToint.Chapter09
