import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section05

/-!
# Quarteroni–Sacco–Saleri §3.7: banded systems

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.7, over the backbone `Numlib/LinearAlgebra/Matrix/LU` (band
preservation `Matrix.IsLU.hasLowerBandwidth`, `Matrix.IsLU.hasUpperBandwidth`, the tridiagonal
matrix `Matrix.tridiagonalOfNat` and the Thomas recurrences `Matrix.thomasAlpha`,
`Matrix.thomasBeta`, `Matrix.thomasGamma` with the factors `Matrix.thomasLower`,
`Matrix.thomasUpper`), `Numlib/LinearAlgebra/Matrix/Band` (the bandwidths),
`Numlib/Direct/Substitution` and `Numlib/FloatingPoint/LU` (the rounding-error analysis of the
Thomas algorithm, `FloatingPoint.RoundsThomas`).

## Conventions

"`A` has lower bandwidth `p`" is the book's §1.6.3 condition `a_ij = 0` for `i > j + p`, and
"upper bandwidth `q`" is `a_ij = 0` for `j > i + q`; on `Fin n` these are the backbone predicates
`Matrix.HasLowerBandwidth`, `Matrix.HasUpperBandwidth` (`Matrix.hasLowerBandwidth_iff_fin`). The
tridiagonal matrix of §3.7.1 with diagonal `a`, subdiagonal `b` and superdiagonal `c` is
`Matrix.tridiagonalOfNat a b c n` for sequences `a b c : ℕ → ℝ`, `0`-based: `a i` at `(i, i)`,
`b i` at `(i, i - 1)`, `c i` at `(i, i + 1)`, so the book's `a_i, b_i, c_i` are `a (i - 1)`,
`b (i - 1)`, `c (i - 1)`; the Thomas coefficients `α_i`, `β_i`, `γ_i` are
`thomasAlpha a b c (i - 1)` and so on. The bidiagonal factors are `thomasLower a b c n` (unit
lower, subdiagonal `β`) and `thomasUpper a b c n` (diagonal `α`, superdiagonal `c`). The
computed Thomas coefficients are an admissible `FloatingPoint.RoundsThomas m a b c α̂ β̂` of the
relational model, the recurrence (3.53) with its three roundings per step, and the computed
factors are the bidiagonal matrices `Matrix.lowerBidiagonalOf β̂ n`,
`Matrix.upperBidiagonalOf α̂ c n` of those coefficients.

## Contents

* `property_3_4_lower`, `property_3_4_upper` — band preservation.
* `equation_3_53`, `equation_3_54`, `equation_3_55` — the Thomas algorithm.
* `thomas_backward_error`, `thomas_backward_error_posDef` — its stability (§3.7.1).
* `equation_3_56` — the division-free variant (§3.7.2).

The banded storage format, Programs 10–13 and the operation counts are not nodes.

## Readings and errata

Property 3.4 ("suppose that there exists an LU factorization of `A`") fails without uniqueness:
Example 3.3's `D = [0, 1; 0, 2] = L_β U_β` has lower bandwidth `0` while `L_β` does not for
`β ≠ 0`; the lower clause is stated under the hypothesis of Theorem 3.4 (the factorization is
then unique), the upper clause holds for every factorization. The stability bounds of §3.7.1
are quoted from [higham2002accuracy] (9.20) and Theorem 9.14; the backbone proves them with the
constants `u / (1 - u)` and `u / (1 - 2u)` of the relational model, which are below the book's
`4u + 3u² + u³` and `(4u + 3u² + u³) / (1 - u)` for `u < 1/2` and `u ≤ 1/4` respectively, and
the book's constants are stated under those (harmless) restrictions on the unit roundoff. The
book's "for `u` small enough" behind the positive definite / M-matrix bound is the hypothesis
that the computed pivots `α̂_i` are positive and the products `β̂_i c_{i-1}` nonnegative, the
sign pattern that the exact factors of such matrices have.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### Property 3.4: band preservation -/

/-- **Property 3.4, the lower factor.** Let `A ∈ ℝ^{n×n}` have an LU factorization `A = L U`
(the unique one: the leading principal submatrices of orders `1, …, n - 1` are nonsingular). If
`A` has lower bandwidth `p`, `a_ij = 0` for `i > j + p`, then so does `L` (backbone
`Matrix.IsLU.hasLowerBandwidth`). -/
theorem property_3_4_lower {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) {p : ℕ}
    (hp : ∀ i j : Fin n, (j : ℕ) + p < i → A i j = 0) :
    ∀ i j : Fin n, (j : ℕ) + p < i → L i j = 0 :=
  hasLowerBandwidth_iff_fin.1 (h.hasLowerBandwidth hA (hasLowerBandwidth_iff_fin.2 hp))

/-- **Property 3.4, the upper factor.** If `A = L U` (unit lower `L`) and `A` has upper
bandwidth `q`, `a_ij = 0` for `j > i + q`, then so does `U` (backbone
`Matrix.IsLU.hasUpperBandwidth`; no uniqueness is needed for this clause). -/
theorem property_3_4_upper {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U) {q : ℕ}
    (hq : ∀ i j : Fin n, (i : ℕ) + q < j → A i j = 0) :
    ∀ i j : Fin n, (i : ℕ) + q < j → U i j = 0 :=
  hasUpperBandwidth_iff_fin.1 (h.hasUpperBandwidth (hasUpperBandwidth_iff_fin.2 hq))

/-! ### §3.7.1: tridiagonal matrices and the Thomas algorithm -/

section Thomas

variable (a b c : ℕ → ℝ)

/-- **(3.53), the Thomas algorithm.** For the tridiagonal matrix `A` with diagonal `a`,
subdiagonal `b` and superdiagonal `c`, the coefficients `α₁ = a₁`, `β_i = b_i / α_{i-1}`,
`α_i = a_i - β_i c_{i-1}` (`i = 2, …, n`) are `Matrix.thomasAlpha`, `Matrix.thomasBeta`, and when
no pivot `α_i` vanishes (`i < n`) the unit lower bidiagonal `L` with subdiagonal `β` and the
upper bidiagonal `U` with diagonal `α` and superdiagonal `c` give the LU factorization `A = L U`
— the Doolittle factorization of `A` (backbone `Matrix.isLU_tridiagonal_thomas`). -/
theorem equation_3_53 (hα : ∀ i, i + 1 < n → thomasAlpha a b c i ≠ 0) :
    thomasAlpha a b c 0 = a 0 ∧
    (∀ i, thomasBeta a b c (i + 1) = b (i + 1) / thomasAlpha a b c i) ∧
    (∀ i, thomasAlpha a b c (i + 1) = a (i + 1) - thomasBeta a b c (i + 1) * c i) ∧
    (∀ i j : Fin n, thomasLower a b c n i j =
      if i = j then 1 else if (j : ℕ) + 1 = i then thomasBeta a b c i else 0) ∧
    (∀ i j : Fin n, thomasUpper a b c n i j =
      if i = j then thomasAlpha a b c i else if (i : ℕ) + 1 = j then c i else 0) ∧
    IsLU (tridiagonalOfNat a b c n) (thomasLower a b c n) (thomasUpper a b c n) :=
  ⟨thomasAlpha_zero a b c, thomasBeta_succ a b c, thomasAlpha_succ a b c, fun _ _ => rfl,
    fun _ _ => rfl, isLU_tridiagonal_thomas a b c hα⟩

/-- Forward substitution on a unit lower bidiagonal matrix: the sum over `j < i + 1` has the
single term `j = i`. -/
private theorem sum_filter_lt_succ_eq {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : ∀ i j : Fin n, j < i → (j : ℕ) + 1 ≠ i → L i j = 0) (y : Fin n → ℝ) {i : Fin n}
    (hi : (i : ℕ) + 1 < n) :
    ∑ j ∈ univ.filter (fun j : Fin n => j < ⟨i + 1, hi⟩), L ⟨i + 1, hi⟩ j * y j =
      L ⟨i + 1, hi⟩ i * y i := by
  refine Finset.sum_eq_single i (fun j hj hji => ?_)
    (fun h => (h (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩)).elim)
  rw [hL _ _ (mem_filter.1 hj).2 fun h => hji (Fin.ext (Nat.succ_injective h)), zero_mul]

/-- Backward substitution on an upper bidiagonal matrix: the sum over `j > i` has the single
term `j = i + 1`. -/
private theorem sum_filter_gt_eq {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : ∀ i j : Fin n, i < j → (i : ℕ) + 1 ≠ j → U i j = 0) (y : Fin n → ℝ) {i : Fin n}
    (hi : (i : ℕ) + 1 < n) :
    ∑ j ∈ univ.filter (fun j : Fin n => i < j), U i j * y j =
      U i ⟨i + 1, hi⟩ * y ⟨i + 1, hi⟩ := by
  refine Finset.sum_eq_single (⟨i + 1, hi⟩ : Fin n) (fun j hj hji => ?_)
    (fun h => (h (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩)).elim)
  rw [hU _ _ (mem_filter.1 hj).2 fun h => hji (Fin.ext h.symm), zero_mul]

/-- **(3.54), the bidiagonal forward substitution.** With `L` the unit lower bidiagonal factor of
(3.53), the solution `y = Matrix.forwardSubst L f` of `L y = f` is computed by `y₁ = f₁`,
`y_i = f_i - β_i y_{i-1}` for `i = 2, …, n`. -/
theorem equation_3_54 (f : Fin n → ℝ) :
    (∀ h0 : 0 < n, forwardSubst (thomasLower a b c n) f ⟨0, h0⟩ = f ⟨0, h0⟩) ∧
    ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      forwardSubst (thomasLower a b c n) f ⟨i + 1, hi⟩ =
        f ⟨i + 1, hi⟩ - thomasBeta a b c (i + 1) * forwardSubst (thomasLower a b c n) f i := by
  have hL : ∀ i j : Fin n, j < i → (j : ℕ) + 1 ≠ i → thomasLower a b c n i j = 0 := by
    intro i j hji hne
    simp [thomasLower, hji.ne', hne]
  constructor
  · intro h0
    rw [forwardSubst_apply, Finset.sum_eq_zero fun j hj =>
      absurd (mem_filter.1 hj).2 (not_lt.2 (Fin.le_def.2 (Nat.zero_le _))), sub_zero]
    simp [thomasLower]
  · intro i hi
    have hne : (⟨i + 1, hi⟩ : Fin n) ≠ i := fun h => by simp [Fin.ext_iff] at h
    rw [forwardSubst_apply, sum_filter_lt_succ_eq hL _ hi]
    simp [thomasLower, hne]

/-- **(3.55), the bidiagonal backward substitution.** With `U` the upper bidiagonal factor of
(3.53), the solution `x = Matrix.backSubst U y` of `U x = y` is computed by `xₙ = yₙ / αₙ`,
`x_i = (y_i - c_i x_{i+1}) / α_i` for `i = n - 1, …, 1`; together with (3.54) this solves the
tridiagonal system, `A (backSubst U (forwardSubst L f)) = f`, when the pivots `α_i` are nonzero
(backbone `Matrix.mulVec_luSolve`). -/
theorem equation_3_55 (y f : Fin n → ℝ) :
    (∀ h0 : 0 < n, backSubst (thomasUpper a b c n) y ⟨n - 1, Nat.sub_one_lt h0.ne'⟩ =
      y ⟨n - 1, Nat.sub_one_lt h0.ne'⟩ / thomasAlpha a b c (n - 1)) ∧
    (∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      backSubst (thomasUpper a b c n) y i =
        (y i - c i * backSubst (thomasUpper a b c n) y ⟨i + 1, hi⟩) / thomasAlpha a b c i) ∧
    ((∀ i, i < n → thomasAlpha a b c i ≠ 0) →
      tridiagonalOfNat a b c n *ᵥ
        backSubst (thomasUpper a b c n) (forwardSubst (thomasLower a b c n) f) = f) := by
  have hU : ∀ i j : Fin n, i < j → (i : ℕ) + 1 ≠ j → thomasUpper a b c n i j = 0 := by
    intro i j hij hne
    simp [thomasUpper, hij.ne, hne]
  refine ⟨fun h0 => ?_, fun i hi => ?_, fun hα => ?_⟩
  · rw [backSubst_apply, Finset.sum_eq_zero fun j hj => absurd (mem_filter.1 hj).2
      (not_lt.2 (Fin.le_def.2 (Nat.le_sub_one_of_lt j.2))), sub_zero]
    simp [thomasUpper]
  · have hne : i ≠ (⟨i + 1, hi⟩ : Fin n) := fun h => by simp [Fin.ext_iff] at h
    rw [backSubst_apply, sum_filter_gt_eq hU _ hi]
    simp [thomasUpper, hne]
  · exact mulVec_luSolve f (isLU_tridiagonal_thomas a b c fun i hi => hα i (Nat.lt_of_succ_lt hi))
      fun i => by simpa [thomasUpper] using hα i i.2

open FloatingPoint in
/-- **§3.7.1, stability of the Thomas algorithm.** If `A` is a nonsingular tridiagonal matrix
and `L̂`, `Û` are the factors actually computed by (3.53) in floating-point arithmetic with unit
roundoff `u < 1/2` (an admissible `FloatingPoint.RoundsThomas m a b c α̂ β̂` with nonzero computed
pivots), then `L̂ Û = A + δA` with `|δA| ≤ (4u + 3u² + u³) |L̂| |Û|` (backbone
`FloatingPoint.exists_roundsThomas_mul_eq_add`, [higham2002accuracy] (9.20), whose constant
`u / (1 - u)` is below the book's for `u < 1/2`). -/
theorem thomas_backward_error {m : RoundingModel ℝ} (hu : 2 * m.u < 1) {α β : ℕ → ℝ}
    (h : RoundsThomas m a b c α β) (hα : ∀ i, α i ≠ 0) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ (4 * m.u + 3 * m.u ^ 2 + m.u ^ 3) •
          ((lowerBidiagonalOf β n).abs * (upperBidiagonalOf α c n).abs) ∧
        lowerBidiagonalOf β n * upperBidiagonalOf α c n = tridiagonalOfNat a b c n + δA := by
  have hu0 := m.u_nonneg
  have hu1 : m.u < 1 := by linarith
  obtain ⟨δA, hδA, hLU⟩ := exists_roundsThomas_mul_eq_add hu1 h hα n
  refine ⟨δA, hδA.trans fun i j => ?_, hLU⟩
  rw [gamma_one_eq]
  have hM : 0 ≤ ((lowerBidiagonalOf β n).abs * (upperBidiagonalOf α c n).abs) i j := by
    rw [mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ hM
  rw [div_le_iff₀ (by linarith)]
  have h1 : 0 ≤ m.u * (1 - 2 * m.u) := mul_nonneg hu0 (by linarith)
  have h2 : 0 ≤ m.u ^ 2 * (1 - 2 * m.u) := mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 ≤ m.u ^ 3 * (1 - 2 * m.u) := mul_nonneg (pow_nonneg hu0 3) (by linarith)
  nlinarith

open FloatingPoint in
/-- **§3.7.1, the symmetric positive definite and M-matrix cases.** If moreover the computed
pivots `α̂_i` are positive and the products `β̂_i c_{i-1}` are nonnegative — the sign pattern of
the exact factors of a symmetric positive definite or an M-matrix, which the computed ones share
"for `u` small enough" — then, for `u ≤ 1/4`, `|δA| ≤ ((4u + 3u² + u³) / (1 - u)) |A|`, which
expresses the stability of the factorization (backbone
`FloatingPoint.exists_roundsThomas_mul_eq_add_of_diag_pos`, [higham2002accuracy] Theorem 9.14,
whose constant `u / (1 - 2u)` is below the book's for `u ≤ 1/4`). -/
theorem thomas_backward_error_posDef {m : RoundingModel ℝ} (hu : 4 * m.u ≤ 1) {α β : ℕ → ℝ}
    (h : RoundsThomas m a b c α β) (hα : ∀ i, 0 < α i) (hbc : ∀ i, 0 ≤ β (i + 1) * c i) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ ((4 * m.u + 3 * m.u ^ 2 + m.u ^ 3) / (1 - m.u)) • (tridiagonalOfNat a b c n).abs ∧
        lowerBidiagonalOf β n * upperBidiagonalOf α c n = tridiagonalOfNat a b c n + δA := by
  have hu0 := m.u_nonneg
  have hu2 : 2 * m.u < 1 := by linarith
  obtain ⟨δA, hδA, hLU⟩ := exists_roundsThomas_mul_eq_add_of_diag_pos hu2 h hα hbc n
  refine ⟨δA, hδA.trans fun i j => ?_, hLU⟩
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : 0 ≤ m.u * (1 - 4 * m.u) := mul_nonneg hu0 (by linarith)
  have h2 : 0 ≤ m.u ^ 2 * (1 - 4 * m.u) := mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 ≤ m.u ^ 3 := pow_nonneg hu0 3
  nlinarith

/-- **§3.7.2, (3.56), the Thomas algorithm without divisions.** With the reciprocal pivots
`γ_i = (a_i - b_i γ_{i-1} c_{i-1})⁻¹` (`γ₀ = 0`, `b₁ = 0`, `c_n = 0`; the backbone's
`Matrix.thomasGamma`, equal to `α_i⁻¹`), and the pivots nonzero, `A = L D Mᵀ` with `L` the lower
bidiagonal matrix of diagonal `γ⁻¹` and subdiagonal `b`, `D = diag γ` and `Mᵀ` the upper
bidiagonal matrix of diagonal `γ⁻¹` and superdiagonal `c`; the substitutions then read
`y₁ = γ₁ f₁`, `y_i = γ_i (f_i - b_i y_{i-1})` for `L y = f` and `xₙ = yₙ`,
`x_i = y_i - γ_i c_i x_{i+1}` for `(D Mᵀ) x = y`, without divisions. -/
theorem equation_3_56 (hα : ∀ i, i < n → thomasAlpha a b c i ≠ 0) (f y : Fin n → ℝ) :
    (∀ i, thomasGamma a b c i = (thomasAlpha a b c i)⁻¹) ∧
    thomasGamma a b c 0 = (a 0)⁻¹ ∧
    (∀ i, thomasGamma a b c (i + 1) = (a (i + 1) - b (i + 1) * thomasGamma a b c i * c i)⁻¹) ∧
    tridiagonalOfNat a b c n =
      (of fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0) *
        diagonal (fun i : Fin n => thomasGamma a b c i) *
        of (fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0) ∧
    (∀ h0 : 0 < n,
      forwardSubst (of fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0) f
        ⟨0, h0⟩ = thomasGamma a b c 0 * f ⟨0, h0⟩) ∧
    (∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      forwardSubst (of fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0) f
        ⟨i + 1, hi⟩ = thomasGamma a b c (i + 1) * (f ⟨i + 1, hi⟩ - b (i + 1) *
          forwardSubst (of fun i j : Fin n =>
            if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0) f i)) ∧
    (∀ h0 : 0 < n,
      backSubst (diagonal (fun i : Fin n => thomasGamma a b c i) * of (fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0)) y
        ⟨n - 1, Nat.sub_one_lt h0.ne'⟩ = y ⟨n - 1, Nat.sub_one_lt h0.ne'⟩) ∧
    ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      backSubst (diagonal (fun i : Fin n => thomasGamma a b c i) * of (fun i j : Fin n =>
          if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0)) y i =
        y i - thomasGamma a b c i * c i *
          backSubst (diagonal (fun i : Fin n => thomasGamma a b c i) * of (fun i j : Fin n =>
            if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0)) y
            ⟨i + 1, hi⟩ := by
  have hγ : ∀ i, thomasGamma a b c i = (thomasAlpha a b c i)⁻¹ :=
    thomasGamma_eq_inv_thomasAlpha a b c
  have hγne : ∀ i : Fin n, thomasGamma a b c i ≠ 0 := fun i => by
    rw [hγ]; exact inv_ne_zero (hα i i.2)
  set Lγ : Matrix (Fin n) (Fin n) ℝ := of fun i j =>
    if i = j then (thomasGamma a b c i)⁻¹ else if (j : ℕ) + 1 = i then b i else 0 with hLγ
  set Mγ : Matrix (Fin n) (Fin n) ℝ := of fun i j =>
    if i = j then (thomasGamma a b c i)⁻¹ else if (i : ℕ) + 1 = j then c i else 0 with hMγ
  set Dγ : Matrix (Fin n) (Fin n) ℝ := diagonal fun i : Fin n => thomasGamma a b c i with hDγ
  -- `Lγ = L diag(α)`, `Mγ = U`, `Dγ = diag(α⁻¹)`
  have hLγ' : Lγ = thomasLower a b c n * diagonal (fun i : Fin n => thomasAlpha a b c i) := by
    ext i j
    rw [mul_diagonal, hLγ, of_apply, thomasLower, of_apply, hγ, inv_inv]
    split_ifs with h1 h2
    · rw [h1, one_mul]
    · obtain ⟨i, hi⟩ := i
      obtain rfl : i = j + 1 := h2.symm
      rw [thomasBeta_succ, div_mul_cancel₀ _ (hα j (by omega))]
    · rw [zero_mul]
  have hMγ' : Mγ = thomasUpper a b c n := by
    ext i j
    rw [hMγ, of_apply, thomasUpper, of_apply, hγ, inv_inv]
  have hfact : tridiagonalOfNat a b c n = Lγ * Dγ * Mγ := by
    have hD1 : diagonal (fun i : Fin n => thomasAlpha a b c i) * Dγ = 1 := by
      rw [hDγ, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [hγ, mul_inv_cancel₀ (hα i i.2)]
    rw [hLγ', hMγ', Matrix.mul_assoc (thomasLower a b c n), hD1, Matrix.mul_one,
      (isLU_tridiagonal_thomas a b c fun i hi => hα i (Nat.lt_of_succ_lt hi)).mul_eq]
  have hDM : Dγ * Mγ = of fun i j : Fin n =>
      if i = j then 1 else if (i : ℕ) + 1 = j then thomasGamma a b c i * c i else 0 := by
    ext i j
    rw [hDγ, diagonal_mul, hMγ, of_apply, of_apply]
    split_ifs with h1
    · exact mul_inv_cancel₀ (hγne i)
    · rfl
    · exact mul_zero _
  have hL0 : ∀ i j : Fin n, j < i → (j : ℕ) + 1 ≠ i → Lγ i j = 0 := by
    intro i j hji hne
    simp [hLγ, hji.ne', hne]
  have hU0 : ∀ i j : Fin n, i < j → (i : ℕ) + 1 ≠ j → (Dγ * Mγ) i j = 0 := by
    intro i j hij hne
    rw [hDM]
    simp [hij.ne, hne]
  refine ⟨hγ, rfl, fun i => rfl, hfact, fun h0 => ?_, fun i hi => ?_, fun h0 => ?_, fun i hi => ?_⟩
  · rw [forwardSubst_apply, Finset.sum_eq_zero fun j hj =>
      absurd (mem_filter.1 hj).2 (not_lt.2 (Fin.le_def.2 (Nat.zero_le _))), sub_zero]
    simp [hLγ, div_eq_mul_inv, mul_comm]
  · have hne : (⟨i + 1, hi⟩ : Fin n) ≠ i := fun h => by simp [Fin.ext_iff] at h
    rw [forwardSubst_apply, sum_filter_lt_succ_eq hL0 _ hi]
    simp [hLγ, hne, div_eq_mul_inv, mul_comm]
  · rw [backSubst_apply, Finset.sum_eq_zero fun j hj => absurd (mem_filter.1 hj).2
      (not_lt.2 (Fin.le_def.2 (Nat.le_sub_one_of_lt j.2))), sub_zero, hDM]
    simp
  · have hne : i ≠ (⟨i + 1, hi⟩ : Fin n) := fun h => by simp [Fin.ext_iff] at h
    rw [backSubst_apply, sum_filter_gt_eq hU0 _ hi, hDM]
    simp [hne]

end Thomas

end QuarteroniSaccoSaleri.Chapter03
