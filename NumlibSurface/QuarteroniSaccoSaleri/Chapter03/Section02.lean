import Numlib.FloatingPoint.Substitution
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section01

/-!
# Quarteroni–Sacco–Saleri §3.2: solution of triangular systems

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.2, over the backbone `Numlib/Direct/Substitution` (forward and
backward substitution as total functions on a finite linear order, their correctness, and the
inverse of a triangular matrix column by column, block by block and by the entrywise
recurrence) and `Numlib/FloatingPoint/Substitution` (the rounding-error analysis of substitution
in the relational model: Higham's Theorems 8.5 and 8.7 and the diagonally dominant case).

## Conventions

Forward substitution (3.22) is `Matrix.forwardSubst L b`, backward substitution (3.23) is
`Matrix.backSubst U b`; the book's recurrences are the theorems `equation_3_22`, `equation_3_23`.
"`L` nonsingular lower triangular" is `L.IsLowerTriangular` with `IsUnit L`, which for a
triangular matrix is the same as a nowhere-zero diagonal (backbone
`Matrix.isUnit_iff_forall_diag_ne_zero_of_isLowerTriangular`). The first and last indices of
`Fin n` are `0` and `⊤` (`Fin.last`), under `[NeZero n]`.

A computed solution `x̂` of `T x = b` by substitution in floating-point arithmetic with unit
roundoff `u` is an admissible `FloatingPoint.RoundsForwardSubst m T b x̂` (or
`RoundsBackSubst`) of the relational rounding model `m : FloatingPoint.RoundingModel ℝ` of
`Numlib/FloatingPoint/Model`, with `m.u` the book's `u = ½ β^{1-t}`: every product is rounded,
the products are subtracted from `b i` one at a time in any order with one rounding each, and
the division by the diagonal entry is rounded (the running-difference order of Program 2, for
which the constant of (3.24) is exactly `n u / (1 - n u)`). The constant `n u / (1 - n u)` is the
backbone's `FloatingPoint.gamma m.u n`, and the `∞`-norms of §3.1 are used in (3.25).

## Contents

* `equation_3_22`, `equation_3_23` — forward and backward substitution.
* `equation_3_24`, `equation_3_25`, `backSubst_componentwise_error`,
  `backSubst_error_of_diagDominant` — the rounding error analysis of §3.2.2.
* `equation_3_26`, `equation_3_27`, `equation_3_28` — the inverse of an upper triangular matrix.

Programs 1–3 are not nodes (they implement `Matrix.forwardSubst` and `Matrix.backSubst`), nor
are the operation counts.

## Readings and errata

(3.25) is printed with `n u` where the rigorous constant that (3.24) and Theorem 3.1 give is
`γ_n = n u / (1 - n u) = n u + O(u²)`; it is stated with `γ_n`, for the `∞`-norm (the book also
names `‖·‖₁` and the Frobenius norm). §3.2.2's "the same result holds … if `L` and `U` are
diagonally dominant" suggests the `2^{n-i+1}` bound; under (weak, row) diagonal dominance what
holds is the linear bound `(2n - 1) γ_n ‖x̂‖_∞` ([higham2002accuracy] Lemma 8.8), which is stated.
In (3.27) the right-hand side `l_k` is described as the vector of `ℝ^k` whose *first* entry is
`1`; since `v'_k` is the leading part of the `k`-th column of `U⁻¹`, it solves `U^{(k)} v'_k = e_k`
with the `1` in the *last* (`k`-th) position, as the recurrence (3.28), `v'_kk = u_kk⁻¹`, confirms.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### Forward and backward substitution, (3.22)–(3.23) -/

/-- **(3.22), forward substitution.** For a nonsingular lower triangular `L` of order `n`, the
solution `x = Matrix.forwardSubst L b` of `L x = b` is computed by `x₁ = b₁ / l₁₁` and
`xᵢ = (bᵢ - ∑_{j<i} l_ij x_j) / l_ii`, and it solves the system (backbone
`Matrix.forwardSubst_apply`, `Matrix.mulVec_forwardSubst`). -/
theorem equation_3_22 [NeZero n] {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hLu : IsUnit L) (b : Fin n → ℝ) :
    forwardSubst L b 0 = b 0 / L 0 0 ∧
      (∀ i, forwardSubst L b i = (b i - ∑ j with j < i, L i j * forwardSubst L b j) / L i i) ∧
      L *ᵥ forwardSubst L b = b := by
  have hd := (isUnit_iff_forall_diag_ne_zero_of_isLowerTriangular hL).1 hLu
  refine ⟨?_, forwardSubst_apply L b, mulVec_forwardSubst b hL hd⟩
  rw [forwardSubst_apply, Finset.sum_eq_zero fun j hj =>
    absurd (mem_filter.1 hj).2 (not_lt.2 (Fin.zero_le j)), sub_zero]

/-- **(3.23), backward substitution.** For a nonsingular upper triangular `U` of order `n`, the
solution `x = Matrix.backSubst U b` of `U x = b` is computed by `xₙ = bₙ / uₙₙ` and
`xᵢ = (bᵢ - ∑_{j>i} u_ij x_j) / u_ii` for `i = n - 1, …, 1`, and it solves the system (backbone
`Matrix.backSubst_apply`, `Matrix.mulVec_backSubst`; `⊤ = Fin.last` is the last index). -/
theorem equation_3_23 [NeZero n] {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular)
    (hUu : IsUnit U) (b : Fin n → ℝ) :
    backSubst U b ⊤ = b ⊤ / U ⊤ ⊤ ∧
      (∀ i, backSubst U b i = (b i - ∑ j with i < j, U i j * backSubst U b j) / U i i) ∧
      U *ᵥ backSubst U b = b := by
  have hd := (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).1 hUu
  refine ⟨?_, backSubst_apply U b, mulVec_backSubst b hU hd⟩
  rw [backSubst_apply, Finset.sum_eq_zero fun j hj =>
    absurd (mem_filter.1 hj).2 (not_lt.2 le_top), sub_zero]

/-! ### §3.2.2: rounding error analysis -/

section Rounding

open FloatingPoint

variable {m : RoundingModel ℝ}

/-- `n u < 1` forces `u < 1` when `n ≥ 1`. -/
private theorem u_lt_one_of_mul_lt_one [NeZero n] (hn : (n : ℝ) * m.u < 1) : m.u < 1 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  nlinarith [m.u_nonneg]

/-- **(3.24), the backward error of substitution.** In floating-point arithmetic with unit
roundoff `u`, `n u < 1`, the computed solution `x̂` of a nonsingular triangular system `T x = b`
by forward substitution (`T = L` lower triangular) or backward substitution (`T = U` upper
triangular) is the exact solution of a perturbed system `(T + δT) x̂ = b` with
`|δT| ≤ (n u / (1 - n u)) |T|` entrywise (backbone `FloatingPoint.exists_roundsForwardSubst_eq`,
`FloatingPoint.exists_roundsBackSubst_eq`, [higham2002accuracy] Theorem 8.5). -/
theorem equation_3_24 [NeZero n] (hn : (n : ℝ) * m.u < 1) {T : Matrix (Fin n) (Fin n) ℝ}
    (hTu : IsUnit T) {b xhat : Fin n → ℝ} :
    (T.IsLowerTriangular → RoundsForwardSubst m T b xhat →
      ∃ δT : Matrix (Fin n) (Fin n) ℝ,
        δT.abs ≤ₑ (n * m.u / (1 - n * m.u)) • T.abs ∧ (T + δT) *ᵥ xhat = b) ∧
    (T.IsUpperTriangular → RoundsBackSubst m T b xhat →
      ∃ δT : Matrix (Fin n) (Fin n) ℝ,
        δT.abs ≤ₑ (n * m.u / (1 - n * m.u)) • T.abs ∧ (T + δT) *ᵥ xhat = b) := by
  have hu := u_lt_one_of_mul_lt_one hn
  have hcard : (Fintype.card (Fin n) : ℝ) * m.u < 1 := by rwa [Fintype.card_fin]
  constructor
  · intro hT h
    obtain ⟨δT, hδT, hx⟩ := exists_roundsForwardSubst_eq hu hcard hT
      ((isUnit_iff_forall_diag_ne_zero_of_isLowerTriangular hT).1 hTu) h
    refine ⟨δT, fun i j => ?_, hx⟩
    simpa [gamma_def] using hδT i j
  · intro hT h
    obtain ⟨δT, hδT, hx⟩ := exists_roundsBackSubst_eq hu hcard hT
      ((isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hT).1 hTu) h
    refine ⟨δT, fun i j => ?_, hx⟩
    simpa [gamma_def] using hδT i j

open scoped Matrix.Norms.Operator in
/-- The normwise consequence of an entrywise bound `|δT| ≤ γ |T|`, `γ ≥ 0`: `‖δT‖_∞ ≤ γ ‖T‖_∞`
(backbone `Matrix.linfty_opNorm_le_of_abs_entrywiseLE`). -/
private theorem linfty_opNorm_le_of_abs_le {δT T : Matrix (Fin n) (Fin n) ℝ} {γ : ℝ}
    (hγ : 0 ≤ γ) (h : δT.abs ≤ₑ γ • T.abs) : ‖δT‖ ≤ γ * ‖T‖ := by
  have h' : δT.abs ≤ₑ (γ • T).abs := fun i j => by
    have := h i j
    simpa [abs_mul, abs_of_nonneg hγ] using this
  calc ‖δT‖ ≤ ‖γ • T‖ := linfty_opNorm_le_of_abs_entrywiseLE h'
    _ = γ * ‖T‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]

/-- The relative error bound of Theorem 3.1 with `δb = 0`, `p = ∞`, monotone in the relative
perturbation: if `‖δT‖_∞ ≤ γ ‖T‖_∞` and `γ K_∞(T) < 1` then
`‖x - x̂‖_∞ / ‖x‖_∞ ≤ γ K_∞(T) / (1 - γ K_∞(T))`. -/
private theorem relative_error_le_of_linfty_le {T δT : Matrix (Fin n) (Fin n) ℝ}
    (hTu : IsUnit T) {b x xhat : Fin n → ℝ} (hx : T *ᵥ x = b) (hb : b ≠ 0)
    (hxhat : (T + δT) *ᵥ xhat = b) {γ : ℝ}
    (hδT : lpOpNorm ⊤ δT ≤ γ * lpOpNorm ⊤ T) (hK : γ * condNumber ⊤ T < 1) :
    ‖x - xhat‖ / ‖x‖ ≤ γ * condNumber ⊤ T / (1 - γ * condNumber ⊤ T) := by
  have hne : NeZero n := ⟨fun h => hb (by subst h; exact Subsingleton.elim _ _)⟩
  have hTpos : 0 < lpOpNorm ⊤ T := by
    have h1 := one_le_condNumberLp ⊤ hTu
    rw [condNumberLp] at h1
    refine (lpOpNorm_nonneg ⊤ T).lt_of_ne fun h => ?_
    rw [← h, zero_mul] at h1
    norm_num at h1
  have hK0 : 0 ≤ condNumber ⊤ T := mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  set r := lpOpNorm ⊤ δT / lpOpNorm ⊤ T with hr
  have hr0 : 0 ≤ r := div_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  have hrγ : r ≤ γ := by rw [hr, div_le_iff₀ hTpos]; exact hδT
  have hKr : condNumber ⊤ T * r ≤ γ * condNumber ⊤ T := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hrγ hK0
  have hsmall : lpOpNorm ⊤ δT * lpOpNorm ⊤ T⁻¹ < 1 := by
    calc lpOpNorm ⊤ δT * lpOpNorm ⊤ T⁻¹ = condNumber ⊤ T * r := by
          rw [hr, condNumber]; field_simp
      _ ≤ γ * condNumber ⊤ T := hKr
      _ < 1 := hK
  have h := theorem_3_1 (p := ⊤) hTu hsmall hx hb (δx := xhat - x) (δb := 0)
    (by rw [add_sub_cancel, hxhat, add_zero])
  rw [PiLp.norm_toLp, PiLp.norm_toLp, PiLp.norm_toLp, PiLp.norm_toLp, norm_zero, zero_div,
    zero_add, norm_sub_rev] at h
  refine h.trans ?_
  rw [← hr, div_mul_eq_mul_div]
  have h1 : 0 < 1 - γ * condNumber ⊤ T := by linarith
  have h2 : 0 < 1 - condNumber ⊤ T * r := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

/-- **(3.25).** If moreover `γ_n K_∞(T) < 1`, `γ_n = n u / (1 - n u)`, then the solution `x̂` of
a nonsingular triangular system `T x = b`, `b ≠ 0`, computed by forward or backward substitution
satisfies `‖x - x̂‖_∞ / ‖x‖_∞ ≤ γ_n K_∞(T) / (1 - γ_n K_∞(T)) = n u K_∞(T) + O(u²)`: (3.24) gives
`‖δT‖_∞ ≤ γ_n ‖T‖_∞` (backbone `Matrix.linfty_opNorm_le_of_abs_entrywiseLE`) and Theorem 3.1
with `δb = 0` does the rest. The book prints `n u` for `γ_n`, its first-order value, and names
the `1`-norm and the Frobenius norm as well; the `∞`-norm is stated. -/
theorem equation_3_25 [NeZero n] (hn : (n : ℝ) * m.u < 1) {T : Matrix (Fin n) (Fin n) ℝ}
    (hTu : IsUnit T) {b x xhat : Fin n → ℝ} (hx : T *ᵥ x = b) (hb : b ≠ 0)
    (hK : n * m.u / (1 - n * m.u) * condNumber ⊤ T < 1) :
    (T.IsLowerTriangular → RoundsForwardSubst m T b xhat →
      ‖x - xhat‖ / ‖x‖ ≤ n * m.u / (1 - n * m.u) * condNumber ⊤ T /
        (1 - n * m.u / (1 - n * m.u) * condNumber ⊤ T)) ∧
    (T.IsUpperTriangular → RoundsBackSubst m T b xhat →
      ‖x - xhat‖ / ‖x‖ ≤ n * m.u / (1 - n * m.u) * condNumber ⊤ T /
        (1 - n * m.u / (1 - n * m.u) * condNumber ⊤ T)) := by
  have hγ : 0 ≤ (n : ℝ) * m.u / (1 - n * m.u) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) m.u_nonneg) (by linarith)
  constructor
  · intro hT h
    obtain ⟨δT, hδT, hxhat⟩ := (equation_3_24 hn hTu).1 hT h
    refine relative_error_le_of_linfty_le hTu hx hb hxhat ?_ hK
    rw [lpOpNorm_top, lpOpNorm_top]
    exact linfty_opNorm_le_of_abs_le hγ hδT
  · intro hT h
    obtain ⟨δT, hδT, hxhat⟩ := (equation_3_24 hn hTu).2 hT h
    refine relative_error_le_of_linfty_le hTu hx hb hxhat ?_ hK
    rw [lpOpNorm_top, lpOpNorm_top]
    exact linfty_opNorm_le_of_abs_le hγ hδT

/-- The number of indices `j ≥ i` of `Fin n` is `n - i`. -/
private theorem card_filter_le_fin (i : Fin n) : #{j : Fin n | i ≤ j} = n - i := by
  rw [← Fin.card_Ici]
  congr 1
  ext j
  simp [Finset.mem_Ici]

/-- **§3.2.2, the improved componentwise bound.** If the entries of the nonsingular upper
triangular `U` satisfy `|u_ii| ≥ |u_ij|` for every `j > i`, then the solution `x̂` of `U x = b`
computed by backward substitution satisfies, for `1 ≤ i ≤ n`,
`|x_i - x̂_i| ≤ 2^{n-i+1} (n u / (1 - n u)) max_{j ≥ i} |x̂_j|`; with the `0`-based indices of
`Fin n` the exponent `n - i + 1` reads `n - i`. Backbone
`FloatingPoint.abs_sub_le_of_roundsBackSubst_of_abs_le_diag`, [higham2002accuracy] Theorem 8.7.
The same holds for a lower triangular `L` with `|l_ii| ≥ |l_ij|`, `j < i`, by transposition. -/
theorem backSubst_componentwise_error [NeZero n] (hn : (n : ℝ) * m.u < 1)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular) (hUu : IsUnit U)
    (hrow : ∀ i j, i < j → |U i j| ≤ |U i i|) {x b xhat : Fin n → ℝ} (hx : U *ᵥ x = b)
    (h : RoundsBackSubst m U b xhat) (i : Fin n) :
    |x i - xhat i| ≤
      2 ^ (n - i : ℕ) * (n * m.u / (1 - n * m.u)) * ⨆ j : {j : Fin n // i ≤ j}, |xhat j| := by
  have hu := u_lt_one_of_mul_lt_one hn
  have hcard : (Fintype.card (Fin n) : ℝ) * m.u < 1 := by rwa [Fintype.card_fin]
  have hd := (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).1 hUu
  have h := abs_sub_le_of_roundsBackSubst_of_abs_le_diag hu hcard hU hd hrow hx h (i := i)
    (c := ⨆ j : {j : Fin n // i ≤ j}, |xhat j|) fun j hj =>
      le_ciSup (f := fun j : {j : Fin n // i ≤ j} => |xhat j|) (Set.finite_range _).bddAbove
        ⟨j, hj⟩
  rwa [card_filter_le_fin, Fintype.card_fin, gamma_def] at h

/-- **§3.2.2, the diagonally dominant case.** "The same result holds … if `L` and `U` are
diagonally dominant": for a nonsingular upper triangular `U` that is diagonally dominant by rows
(Definition 1.24, `∑_{j ≠ i} |u_ij| ≤ |u_ii|`), the solution `x̂` of `U x = b` computed by
backward substitution satisfies `|x_i - x̂_i| ≤ (2n - 1) (n u / (1 - n u)) ‖x̂‖_∞` for every `i`
(backbone `FloatingPoint.abs_sub_le_of_roundsBackSubst_of_isDiagDominant`, [higham2002accuracy]
Lemma 8.8): under dominance the bound is linear in `n`, better than the `2^{n-i+1}` the book's
sentence suggests. -/
theorem backSubst_error_of_diagDominant [NeZero n] (hn : (n : ℝ) * m.u < 1)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular) (hUu : IsUnit U)
    (hdom : U.IsDiagDominant) {x b xhat : Fin n → ℝ} (hx : U *ᵥ x = b)
    (h : RoundsBackSubst m U b xhat) (i : Fin n) :
    |x i - xhat i| ≤ (2 * n - 1) * (n * m.u / (1 - n * m.u)) * ‖xhat‖ := by
  have hu := u_lt_one_of_mul_lt_one hn
  have hcard : (Fintype.card (Fin n) : ℝ) * m.u < 1 := by rwa [Fintype.card_fin]
  have hd := (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).1 hUu
  have hdom' : ∀ i, ∑ j ∈ univ.erase i, |U i j| ≤ |U i i| := fun i => by
    simpa [Real.norm_eq_abs] using hdom i
  have h := abs_sub_le_of_roundsBackSubst_of_isDiagDominant hu hcard hU hd hdom' hx h
    (c := ‖xhat‖) (fun j => by simpa [Real.norm_eq_abs] using norm_le_pi_norm xhat j) i
  rwa [Fintype.card_fin, gamma_def] at h

end Rounding

/-! ### §3.2.3: the inverse of a triangular matrix -/

section Inverse

variable {U : Matrix (Fin n) (Fin n) ℝ}

/-- **(3.26).** The column vectors `v_i` of the inverse `V = U⁻¹` of a nonsingular upper
triangular `U` satisfy `U v_i = e_i`, so each is computed by backward substitution (3.23) from
the canonical basis vector `e_i` (backbone `Matrix.inv_col_eq_backSubst`). -/
theorem equation_3_26 (hU : U.IsUpperTriangular) (hUu : IsUnit U) (i : Fin n) :
    U *ᵥ U⁻¹.col i = Pi.single i 1 ∧ U⁻¹.col i = backSubst U (Pi.single i 1) := by
  have hd := (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).1 hUu
  have h : U⁻¹.col i = backSubst U (Pi.single i 1) := inv_col_eq_backSubst hU hd i
  exact ⟨by rw [h, mulVec_backSubst _ hU hd], h⟩

/-- A leading principal submatrix of an upper triangular matrix is upper triangular. -/
private theorem isUpperTriangular_leadingPrincipalSubmatrix (hU : U.IsUpperTriangular)
    (k : Fin n) : (U.leadingPrincipalSubmatrix k).IsUpperTriangular :=
  fun _ _ hij => hU hij

/-- **(3.27).** For `k = 1, …, n`, let `U^{(k)}` be the leading principal submatrix of order `k`
of the nonsingular upper triangular `U` and `v'_k ∈ ℝ^k` the solution of the upper triangular
system `U^{(k)} v'_k = l_k`, `l_k` the vector of `ℝ^k` whose only nonzero entry is a `1` in the
`k`-th (last) position — the book says "the first one"; see the module documentation. Then
`v'_k` is computed by (3.23) and consists of the first `k` entries of the `k`-th column of
`U⁻¹`, because `(U^{(k)})⁻¹` is the leading block of `U⁻¹` (backbone
`Matrix.inv_toBlock_le_of_isUpperTriangular`, `Matrix.inv_col_eq_backSubst`). -/
theorem equation_3_27 (hU : U.IsUpperTriangular) (hUu : IsUnit U) (k : Fin n) :
    U.leadingPrincipalSubmatrix k *ᵥ
        backSubst (U.leadingPrincipalSubmatrix k) (Pi.single ⟨k, le_rfl⟩ 1) =
      Pi.single ⟨k, le_rfl⟩ 1 ∧
    ∀ j : {j : Fin n // j ≤ k},
      backSubst (U.leadingPrincipalSubmatrix k) (Pi.single ⟨k, le_rfl⟩ 1) j = U⁻¹ j k := by
  have hd := (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).1 hUu
  have hUk := isUpperTriangular_leadingPrincipalSubmatrix hU k
  have hdk : ∀ i : {j : Fin n // j ≤ k}, U.leadingPrincipalSubmatrix k i i ≠ 0 := fun i => hd i
  refine ⟨mulVec_backSubst _ hUk hdk, fun j => ?_⟩
  have h1 := congrFun (inv_col_eq_backSubst hUk hdk ⟨k, le_rfl⟩) j
  have h2 := congrFun (congrFun (inv_toBlock_le_of_isUpperTriangular hU hd k) j) ⟨k, le_rfl⟩
  exact h1.symm.trans h2

/-- **(3.28), the inversion algorithm for upper triangular matrices.** For `k = n, n - 1, …, 1`
the nonzero entries of the `k`-th column of `U⁻¹` are `v'_kk = u_kk⁻¹` and
`v'_ik = -u_ii⁻¹ ∑_{j=i+1}^{k} u_ij v'_jk` for `i = k - 1, …, 1`; below the diagonal `U⁻¹`
vanishes (backbone `Matrix.inv_apply_self_of_isUpperTriangular`,
`Matrix.inv_apply_of_isUpperTriangular`, `Matrix.inv_apply_of_isUpperTriangular_of_lt`). -/
theorem equation_3_28 (hU : U.IsUpperTriangular) (hUu : IsUnit U) (k : Fin n) :
    U⁻¹ k k = (U k k)⁻¹ ∧
      (∀ i, i < k → U⁻¹ i k = -(U i i)⁻¹ * ∑ j with i < j ∧ j ≤ k, U i j * U⁻¹ j k) ∧
      ∀ i, k < i → U⁻¹ i k = 0 := by
  have hd := (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).1 hUu
  exact ⟨inv_apply_self_of_isUpperTriangular hU hd k,
    fun i hik => inv_apply_of_isUpperTriangular hU hd hik,
    fun i hki => inv_apply_of_isUpperTriangular_of_lt hU hki⟩

end Inverse

end QuarteroniSaccoSaleri.Chapter03
