import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section14

/-!
# Quarteroni–Sacco–Saleri §3.15: exercises

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.15: the exercises the main text cites — 1 and 2 (§3.1.1), 4
(§3.1.2), 5 (§3.10), 11 (§3.9) and 15 (§3.11) — over the backbone
`Numlib/Analysis/Matrix/OperatorNorm` (the comparison of the induced norms),
`Numlib/LinearAlgebra/Matrix/LU` with `LU/Elimination` and `LU/Pivoting` (the LU factorization, the
envelope, the stages of GEM and the growth factor) and `Numlib/LinearAlgebra/Matrix/SVD` (the
singular system).

## Conventions

Those of §3.1 and §3.10: `‖A‖_p = lpOpNorm p A`, `K_p(A) = condNumber p A`, vectors in the
`∞`-norm carry the `Pi` norm, the growth factor is `equation_3_66 A = growthFactor A`, and the
first and last indices of `Fin n` are `0` and `⊤` under `[NeZero n]`. A matrix given by its
entries is `Matrix.of fun i j => …`.

## Contents

* `exercise_3_1` — the equivalence of `K₁`, `K₂` and `K_∞` up to powers of `n`.
* `exercise_3_2` — the unit upper triangular matrix with `-1` above the diagonal:
  `det B = 1`, `K_∞(B) = n 2^{n-1}`.
* `exercise_3_4` — `A = [1 γ; 0 1]`: `K_∞(A) = K₁(A) = (1 + γ)²`, yet the system with solution
  `(1 - γ, 1)ᵀ` is well conditioned.
* `exercise_3_5` — Wilkinson's matrix: an LU factorization with `|l_ij| ≤ 1` and
  `u_nn = 2^{n-1}`, and the growth factor `2^{n-1}`.
* `exercise_3_11` — the arrow matrix: no fill-in although the envelope is the whole strict
  lower triangle, and the permutation that empties the envelope.
* `exercise_3_15` — the ratio `‖y‖₂/‖x‖₂` of (3.70) through the singular system of `A`.

Exercise 6 is folded into `example_3_7_lu` (`Section10`); Exercise 3 (`K(A B) ≤ K(A) K(B)`) is
the backbone's `NormedRing.condNumber_mul_le` and is not cited by the text; Exercises 7–10,
12–14 are not cited and are not nodes.

## Readings

Exercise 4 asks whether the problem is well- or ill-conditioned; the answer stated is the bound
`‖δx‖_∞/‖x‖_∞ ≤ ((1 + γ)/max(|1 - γ|, 1)) ‖δb‖_∞/‖b‖_∞` with amplification factor at most `3`
for every `γ ≥ 0`, although `K_∞(A) = (1 + γ)²` is unbounded. Exercise 11's "fill-in" is read
through (3.59)–(3.60): the factors have no nonzero entry where `A` has none, while the envelope
of `A` is the whole strict lower triangle; the hint's permutation `P` (first ↔ last row and
column) makes `P A Pᵀ = A.submatrix σ σ` upper triangular, with empty envelope. Exercise 15's
singular system is written with the book's letters, `A v_i = σ_i u_i`, `Aᵀ u_i = σ_i v_i`; the
backbone's `Matrix.exists_singularSystem` names them the other way round. The discussion of when
the ratio approximates `σ_n⁻¹ = ‖A⁻¹‖₂` is prose.
-/

open Finset Matrix WithLp
open scoped ENNReal InnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### Exercise 1 -/

/-- A comparison `‖M‖_p ≤ c ‖M‖_q` of two induced norms gives `K_p(A) ≤ c² K_q(A)`. -/
private theorem condNumber_le_of_lpOpNorm_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ M : Matrix (Fin n) (Fin n) ℝ, lpOpNorm p M ≤ c * lpOpNorm q M)
    (A : Matrix (Fin n) (Fin n) ℝ) : condNumber p A ≤ c ^ 2 * condNumber q A := by
  rw [condNumber, condNumber]
  calc lpOpNorm p A * lpOpNorm p A⁻¹ ≤ (c * lpOpNorm q A) * (c * lpOpNorm q A⁻¹) :=
        mul_le_mul (h A) (h A⁻¹) (lpOpNorm_nonneg _ _) (mul_nonneg hc (lpOpNorm_nonneg _ _))
    _ = c ^ 2 * (lpOpNorm q A * lpOpNorm q A⁻¹) := by ring

/-- `K' ≤ n K` gives the book's `(1/n) K' ≤ K` (trivially for `n = 0`). -/
private theorem one_div_mul_le {K K' : ℝ} (hK : 0 ≤ K) (h : K' ≤ n * K) : (1 / n : ℝ) * K' ≤ K := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using hK
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc (1 / n : ℝ) * K' ≤ (1 / n : ℝ) * (n * K) := by gcongr
      _ = K := by field_simp

/-- **Exercise 3.1.** For any `A ∈ ℝ^{n×n}`,
`(1/n) K₂(A) ≤ K₁(A) ≤ n K₂(A)`, `(1/n) K_∞(A) ≤ K₂(A) ≤ n K_∞(A)` and
`(1/n²) K₁(A) ≤ K_∞(A) ≤ n² K₁(A)`: a matrix ill conditioned in one norm is so in every other,
up to a factor depending on `n` (backbone `Matrix.l2_opNorm_le_sqrt_card_mul_lpOpNorm_one`,
`Matrix.l2_opNorm_le_sqrt_card_mul_linfty_opNorm`, `Matrix.lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le`
and `_of_ge`, applied to `A` and `A⁻¹`). -/
theorem exercise_3_1 (A : Matrix (Fin n) (Fin n) ℝ) :
    ((1 / n : ℝ) * condNumber 2 A ≤ condNumber 1 A ∧ condNumber 1 A ≤ n * condNumber 2 A) ∧
      ((1 / n : ℝ) * condNumber ⊤ A ≤ condNumber 2 A ∧ condNumber 2 A ≤ n * condNumber ⊤ A) ∧
        ((1 / n ^ 2 : ℝ) * condNumber 1 A ≤ condNumber ⊤ A ∧
          condNumber ⊤ A ≤ n ^ 2 * condNumber 1 A) := by
  have hsq : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hnn : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (M : Matrix (Fin n) (Fin n) ℝ), 0 ≤ condNumber p M :=
    fun p _ M => mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  have h12 : ∀ M : Matrix (Fin n) (Fin n) ℝ, lpOpNorm 1 M ≤ √(n : ℝ) * lpOpNorm 2 M := fun M => by
    simpa using (l2_opNorm_le_sqrt_card_mul_lpOpNorm_one M).1
  have h21 : ∀ M : Matrix (Fin n) (Fin n) ℝ, lpOpNorm 2 M ≤ √(n : ℝ) * lpOpNorm 1 M := fun M => by
    simpa using (l2_opNorm_le_sqrt_card_mul_lpOpNorm_one M).2
  have h2i : ∀ M : Matrix (Fin n) (Fin n) ℝ, lpOpNorm 2 M ≤ √(n : ℝ) * lpOpNorm ⊤ M := fun M => by
    simpa using (l2_opNorm_le_sqrt_card_mul_linfty_opNorm M).1
  have hi2 : ∀ M : Matrix (Fin n) (Fin n) ℝ, lpOpNorm ⊤ M ≤ √(n : ℝ) * lpOpNorm 2 M := fun M => by
    simpa using (l2_opNorm_le_sqrt_card_mul_linfty_opNorm M).2
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (⊤ : ℝ≥0∞).toReal) = 1 := by simp
  have h1i : ∀ M : Matrix (Fin n) (Fin n) ℝ, lpOpNorm 1 M ≤ n * lpOpNorm ⊤ M := fun M => by
    have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le (p := 1) (q := ⊤) le_top M
    rwa [hexp, Real.rpow_one, Fintype.card_fin] at h
  have hi1 : ∀ M : Matrix (Fin n) (Fin n) ℝ, lpOpNorm ⊤ M ≤ n * lpOpNorm 1 M := fun M => by
    have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge (p := 1) (q := ⊤) le_top M
    rwa [hexp, Real.rpow_one, Fintype.card_fin] at h
  have hs := Real.sqrt_nonneg (n : ℝ)
  refine ⟨⟨one_div_mul_le (hnn 1 A) ?_, ?_⟩, ⟨one_div_mul_le (hnn 2 A) ?_, ?_⟩, ?_, ?_⟩
  · simpa [hsq] using condNumber_le_of_lpOpNorm_le hs h21 A
  · simpa [hsq] using condNumber_le_of_lpOpNorm_le hs h12 A
  · simpa [hsq] using condNumber_le_of_lpOpNorm_le hs hi2 A
  · simpa [hsq] using condNumber_le_of_lpOpNorm_le hs h2i A
  · have h := condNumber_le_of_lpOpNorm_le (Nat.cast_nonneg n) h1i A
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using hnn ⊤ A
    · have hn' : (0 : ℝ) < n ^ 2 := by positivity
      calc (1 / (n : ℝ) ^ 2) * condNumber 1 A
          ≤ (1 / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 * condNumber ⊤ A) := by gcongr
        _ = condNumber ⊤ A := by field_simp
  · exact condNumber_le_of_lpOpNorm_le (Nat.cast_nonneg n) hi1 A

/-! ### Exercise 2 -/

/-- `∑_{t < m} 2^t = 2^m - 1`. -/
private theorem sum_range_two_pow (m : ℕ) : ∑ t ∈ range m, (2 : ℝ) ^ t = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- `∑_{a ≤ j < b} 2^(b - j - 1) = 2^(b - a) - 1`. -/
private theorem sum_Ico_two_pow_rev {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Ico a b, (2 : ℝ) ^ (b - j - 1) = 2 ^ (b - a) - 1 := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, show b + 1 - b - 1 = 0 by omega, pow_zero,
      show b + 1 - a = (b - a) + 1 by omega, pow_succ]
    have : ∑ j ∈ Ico a b, (2 : ℝ) ^ (b + 1 - j - 1) = ∑ j ∈ Ico a b, (2 : ℝ) ^ (b - j - 1) * 2 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [mem_Ico] at hj
      rw [← pow_succ]
      congr 1
      omega
    rw [this, ← Finset.sum_mul, ih]
    ring

/-- `∑_{a ≤ j < b} 2^(j - a) = 2^(b - a) - 1`. -/
private theorem sum_Ico_two_pow (a b : ℕ) :
    ∑ j ∈ Ico a b, (2 : ℝ) ^ (j - a) = 2 ^ (b - a) - 1 := by
  rw [Finset.sum_Ico_eq_sum_range, ← sum_range_two_pow]
  exact Finset.sum_congr rfl fun t _ => by rw [Nat.add_sub_cancel_left]

/-- The maximum-row-sum norm of a real matrix, from a bound on every row and a row attaining
it. -/
private theorem linfty_opNorm_eq_of_forall_sum_le {B : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, ∑ j, |B i j| ≤ c) (i₀ : Fin n) (h₀ : ∑ j, |B i₀ j| = c) :
    lpOpNorm ⊤ B = c := by
  rw [lpOpNorm_top]
  exact le_antisymm (linfty_opNorm_le_of_forall_sum_le hc h)
    (h₀ ▸ sum_abs_apply_le_linfty_opNorm B i₀)

/-- **Exercise 3.2.** The matrix `B ∈ ℝ^{n×n}` with `b_ii = 1`, `b_ij = -1` for `i < j` and
`b_ij = 0` for `i > j` has determinant `1`, yet `K_∞(B) = n 2^{n-1}` is large: its inverse is
the unit upper triangular matrix with `(B⁻¹)_ij = 2^{j-i-1}` for `i < j`, so `‖B‖_∞ = n` (the
first row) and `‖B⁻¹‖_∞ = 2^{n-1}` (the first row again). -/
theorem exercise_3_2 [NeZero n] :
    let B : Matrix (Fin n) (Fin n) ℝ := of fun i j => if i = j then 1 else if i < j then -1 else 0
    B.det = 1 ∧
      B⁻¹ =
        of (fun i j : Fin n => if i = j then 1 else if i < j then 2 ^ ((j : ℕ) - i - 1) else 0) ∧
        lpOpNorm ⊤ B = n ∧ lpOpNorm ⊤ B⁻¹ = 2 ^ (n - 1) ∧ condNumber ⊤ B = n * 2 ^ (n - 1) := by
  intro B
  set C : Matrix (Fin n) (Fin n) ℝ :=
    of fun i j => if i = j then 1 else if i < j then 2 ^ ((j : ℕ) - i - 1) else 0 with hC
  have hBU : B.IsUpperTriangular := fun i j hij => by
    have hij' : j < i := hij
    simp only [B, of_apply]
    rw [ite_eq_right hij'.ne', ite_eq_right hij'.not_gt]
  have hdet : B.det = 1 := by
    rw [det_of_isUpperTriangular hBU]
    simp [B]
  -- the product `B C`, entry by entry, as a sum over `ℕ`
  have hBC : B * C = 1 := by
    ext i k
    rw [mul_apply, one_apply]
    set g : ℕ → ℝ := fun t => (if (i : ℕ) = t then (1 : ℝ) else if (i : ℕ) < t then -1 else 0) *
      (if t = (k : ℕ) then 1 else if t < (k : ℕ) then 2 ^ ((k : ℕ) - t - 1) else 0) with hg
    have hconv : ∀ j : Fin n, B i j * C j k = g j := fun j => by
      simp only [B, C, g, of_apply, Fin.ext_iff, Fin.lt_def]
    rw [Finset.sum_congr rfl fun j _ => hconv j, Fin.sum_univ_eq_sum_range g n]
    rcases lt_trichotomy (i : ℕ) k with hik | hik | hik
    · rw [ite_eq_right (Fin.ne_of_val_ne hik.ne)]
      have hsub : Ico (i : ℕ) (k + 1) ⊆ range n := fun t ht => by
        rw [mem_Ico] at ht
        rw [mem_range]
        omega
      have hzero : ∀ t ∈ range n, t ∉ Ico (i : ℕ) (k + 1) → g t = 0 := fun t _ ht => by
        rw [mem_Ico, not_and_or, not_le, not_lt] at ht
        rcases ht with ht | ht
        · simp [g, show (i : ℕ) ≠ t by omega, show ¬ (i : ℕ) < t by omega]
        · simp [g, show t ≠ (k : ℕ) by omega, show ¬ t < (k : ℕ) by omega]
      rw [← Finset.sum_subset hsub hzero, Finset.sum_Ico_succ_top hik.le,
        Finset.sum_eq_sum_Ico_succ_bot hik]
      have hmid : ∑ t ∈ Ico ((i : ℕ) + 1) k, g t = -(2 ^ ((k : ℕ) - i - 1) - 1) := by
        have hgeom := sum_Ico_two_pow_rev (a := (i : ℕ) + 1) (b := k) hik
        rw [show (k : ℕ) - (i + 1) = k - i - 1 by omega] at hgeom
        rw [← hgeom, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [mem_Ico] at ht
        simp [g, show (i : ℕ) ≠ t by omega, show (i : ℕ) < t by omega, show t ≠ (k : ℕ) by omega,
          show t < (k : ℕ) by omega]
      have hgi : g i = 2 ^ ((k : ℕ) - i - 1) := by simp [g, hik, hik.ne]
      have hgk : g k = -1 := by simp [g, hik, hik.ne]
      rw [hmid, hgi, hgk]
      ring
    · rw [ite_eq_left (Fin.ext hik)]
      rw [Finset.sum_eq_single (i : ℕ) (fun t _ hti => ?_) (fun h => absurd (mem_range.2 i.2) h)]
      · simp [g, hik]
      · rcases lt_or_gt_of_ne hti with ht | ht
        · simp [g, show (i : ℕ) ≠ t by omega, show ¬ (i : ℕ) < t by omega]
        · simp [g, show t ≠ (k : ℕ) by omega, show ¬ t < (k : ℕ) by omega]
    · rw [ite_eq_right (Fin.ne_of_val_ne hik.ne')]
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases ht : (i : ℕ) ≤ t
      · simp [g, show t ≠ (k : ℕ) by omega, show ¬ t < (k : ℕ) by omega]
      · simp [g, show (i : ℕ) ≠ t by omega, show ¬ (i : ℕ) < t by omega]
  have hinv : B⁻¹ = C := inv_eq_right_inv hBC
  -- the row sums of `B`
  have hrowB : ∀ i : Fin n, ∑ j, |B i j| = n - i := fun i => by
    have : ∀ j : Fin n, |B i j| = if i ≤ j then 1 else 0 := fun j => by
      simp only [B, of_apply]
      rcases lt_trichotomy i j with h | h | h
      · rw [ite_eq_right h.ne, ite_eq_left h, ite_eq_left h.le, abs_neg, abs_one]
      · rw [ite_eq_left h, ite_eq_left h.le, abs_one]
      · rw [ite_eq_right h.ne', ite_eq_right h.not_gt, ite_eq_right h.not_ge, abs_zero]
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_boole]
    have hfilter : (univ.filter fun j : Fin n => i ≤ j) = Ici i := by ext; simp
    rw [hfilter, Fin.card_Ici, Nat.cast_sub i.2.le]
  -- the row sums of `C`
  have hrowC : ∀ i : Fin n, ∑ j, |C i j| = 2 ^ (n - 1 - i) := fun i => by
    set f : ℕ → ℝ := fun t => if (i : ℕ) = t then (1 : ℝ) else
      if (i : ℕ) < t then 2 ^ (t - i - 1) else 0 with hf
    have : ∀ j : Fin n, |C i j| = f j := fun j => by
      simp only [C, f, of_apply, Fin.ext_iff, Fin.lt_def]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun j _ => this j, Fin.sum_univ_eq_sum_range f n,
      ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt i.2), Finset.sum_range_succ,
      Finset.sum_eq_zero fun t ht => ?_, zero_add]
    · have hfi : f i = 1 := by simp [f]
      have : ∑ t ∈ Ico ((i : ℕ) + 1) n, f t =
          ∑ t ∈ Ico ((i : ℕ) + 1) n, (2 : ℝ) ^ (t - (i + 1)) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [mem_Ico] at ht
        simp only [f]
        rw [ite_eq_right (show (i : ℕ) ≠ t by omega), ite_eq_left (show (i : ℕ) < t by omega),
          Nat.sub_sub]
      rw [hfi, this, sum_Ico_two_pow, show n - (i + 1) = n - 1 - i by omega]
      ring
    · rw [mem_range] at ht
      simp [f, show (i : ℕ) ≠ t by omega, show ¬ (i : ℕ) < t by omega]
  have hnormB : lpOpNorm ⊤ B = n := by
    refine linfty_opNorm_eq_of_forall_sum_le (Nat.cast_nonneg n) (fun i => ?_) 0 ?_
    · rw [hrowB]
      linarith [(Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ i)]
    · rw [hrowB]
      simp
  have hnormC : lpOpNorm ⊤ C = 2 ^ (n - 1) := by
    refine linfty_opNorm_eq_of_forall_sum_le (by positivity) (fun i => ?_) 0 ?_
    · rw [hrowC]
      exact pow_le_pow_right₀ one_le_two (Nat.sub_le _ _)
    · rw [hrowC]
      simp
  refine ⟨hdet, hinv, hnormB, by rw [hinv, hnormC], ?_⟩
  rw [condNumber, hinv, hnormB, hnormC]

/-! ### Exercise 4 -/

/-- The sup norm on `ℝ²`. -/
private theorem pi_norm_fin_two (a b : ℝ) : ‖![a, b]‖ = max |a| |b| := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg _))).2 fun i => ?_
    fin_cases i
    · simp
    · simp
  · simpa using norm_le_pi_norm ![a, b] 0
  · simpa using norm_le_pi_norm ![a, b] 1

/-- **Exercise 3.4.** For `A = [1 γ; 0 1]` with `γ ≥ 0`, `A⁻¹ = [1 -γ; 0 1]` and
`K_∞(A) = K₁(A) = (1 + γ)²`. For the system `A x = b` whose solution is `x = (1 - γ, 1)ᵀ`, so
that `b = (1, 1)ᵀ`, a perturbation `δb = (δ₁, δ₂)ᵀ` of the right-hand side gives
`‖δx‖_∞/‖x‖_∞ ≤ ((1 + γ)/max(|1 - γ|, 1)) ‖δb‖_∞/‖b‖_∞`, and the amplification factor is at most
`3` for every `γ ≥ 0`: the problem is well conditioned, although `K_∞(A)` is arbitrarily large
(the bound of Theorem 3.1 is attained only for special `b`). -/
theorem exercise_3_4 {γ : ℝ} (hγ : 0 ≤ γ) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, γ; 0, 1]
    A⁻¹ = !![1, -γ; 0, 1] ∧ condNumber ⊤ A = (1 + γ) ^ 2 ∧ condNumber 1 A = (1 + γ) ^ 2 ∧
      A *ᵥ ![1 - γ, 1] = ![1, 1] ∧ ‖![1 - γ, 1]‖ = max |1 - γ| 1 ∧
        ‖(![1, 1] : Fin 2 → ℝ)‖ = 1 ∧
        (∀ δb δx : Fin 2 → ℝ, A *ᵥ (![1 - γ, 1] + δx) = ![1, 1] + δb →
          ‖δx‖ / ‖![1 - γ, 1]‖ ≤
            (1 + γ) / max |1 - γ| 1 * (‖δb‖ / ‖(![1, 1] : Fin 2 → ℝ)‖)) ∧
        (1 + γ) / max |1 - γ| 1 ≤ 3 := by
  intro A
  have hinv : A⁻¹ = !![1, -γ; 0, 1] := by
    refine inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_two]
  have hrow : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M = !![1, γ; 0, 1] ∨ M = !![1, -γ; 0, 1] →
      lpOpNorm ⊤ M = 1 + γ := fun M hM => by
    rw [lpOpNorm_top]
    refine le_antisymm (linfty_opNorm_le_of_forall_sum_le (by positivity) fun i => ?_) ?_
    · rcases hM with rfl | rfl <;> fin_cases i <;>
        simp [Fin.sum_univ_two, abs_of_nonneg hγ, hγ, add_comm]
    · have := sum_abs_apply_le_linfty_opNorm M 0
      rcases hM with rfl | rfl <;> simpa [Fin.sum_univ_two, abs_of_nonneg hγ] using this
  have hKinf : condNumber ⊤ A = (1 + γ) ^ 2 := by
    rw [condNumber, hinv, hrow _ (Or.inl rfl), hrow _ (Or.inr rfl), sq]
  have hK1 : condNumber 1 A = (1 + γ) ^ 2 := by
    have ht : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M = !![1, γ; 0, 1] ∨ M = !![1, -γ; 0, 1] →
        lpOpNorm 1 M = 1 + γ := fun M hM => by
      rw [lpOpNorm_one_eq_linfty_opNorm_transpose]
      refine le_antisymm (linfty_opNorm_le_of_forall_sum_le (by positivity) fun i => ?_) ?_
      · rcases hM with rfl | rfl <;> fin_cases i <;>
          simp [Fin.sum_univ_two, abs_of_nonneg hγ, hγ, add_comm]
      · have := sum_abs_apply_le_linfty_opNorm Mᵀ 1
        rcases hM with rfl | rfl <;> simpa [Fin.sum_univ_two, abs_of_nonneg hγ, add_comm] using this
    rw [condNumber, hinv, ht _ (Or.inl rfl), ht _ (Or.inr rfl), sq]
  have hb : A *ᵥ ![1 - γ, 1] = ![1, 1] := by
    ext i
    fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_two]
  have hx : ‖![1 - γ, 1]‖ = max |1 - γ| 1 := by rw [pi_norm_fin_two, abs_one]
  have hb1 : ‖(![1, 1] : Fin 2 → ℝ)‖ = 1 := by rw [pi_norm_fin_two, abs_one, max_self]
  have hmax : 0 < max |1 - γ| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨hinv, hKinf, hK1, hb, hx, hb1, fun δb δx h => ?_, ?_⟩
  · have hδ : A *ᵥ δx = δb := by
      rw [mulVec_add, hb] at h
      exact add_left_cancel h
    have hAdet : IsUnit A.det := by simp [A, Matrix.det_fin_two_of]
    have hδx : δx = A⁻¹ *ᵥ δb := by
      rw [← hδ, mulVec_mulVec, nonsing_inv_mul _ hAdet, one_mulVec]
    have hle : ‖δx‖ ≤ (1 + γ) * ‖δb‖ := by
      rw [hδx, ← hrow _ (Or.inr rfl), ← hinv, lpOpNorm_top]
      exact linfty_opNorm_mulVec _ _
    rw [hx, hb1, div_one, div_le_iff₀ hmax, div_mul_eq_mul_div, div_mul_cancel₀ _ hmax.ne']
    exact hle
  · rw [div_le_iff₀ hmax]
    rcases le_or_gt γ 2 with h2 | h2
    · calc 1 + γ ≤ 3 * 1 := by linarith
        _ ≤ 3 * max |1 - γ| 1 := by gcongr; exact le_max_right _ _
    · calc 1 + γ ≤ 3 * |1 - γ| := by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
        _ ≤ 3 * max |1 - γ| 1 := by gcongr; exact le_max_left _ _

/-! ### Exercise 5 -/

/-- `∑_{j < i} 2^j = 2^i - 1` over `Fin n`. -/
private theorem sum_fin_lt_two_pow (i : Fin n) :
    ∑ j : Fin n, (if j < i then (2 : ℝ) ^ (j : ℕ) else 0) = 2 ^ (i : ℕ) - 1 := by
  set f : ℕ → ℝ := fun t => if t < (i : ℕ) then (2 : ℝ) ^ t else 0 with hf
  have : ∀ j : Fin n, (if j < i then (2 : ℝ) ^ (j : ℕ) else 0) = f j := fun j => by
    simp only [f, Fin.lt_def]
  rw [Finset.sum_congr rfl fun j _ => this j, Fin.sum_univ_eq_sum_range f n, hf,
    ← Finset.sum_filter]
  have hfilter : (range n).filter (fun t => t < (i : ℕ)) = range (i : ℕ) := by
    ext t
    simp only [mem_filter, mem_range]
    omega
  rw [hfilter, sum_range_two_pow]

/-- An LU factorization whose upper factor has a nowhere-zero diagonal has nonsingular strict
leading principal submatrices (backbone `Matrix.IsLU.det_strictLeadingPrincipalSubmatrix`). -/
private theorem isUnit_strict_of_isLU {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U)
    (hd : ∀ i, U i i ≠ 0) (k : Fin n) : IsUnit (A.strictLeadingPrincipalSubmatrix k) := by
  rw [isUnit_iff_isUnit_det, h.det_strictLeadingPrincipalSubmatrix, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  exact fun i _ => hd i

/-- **Exercise 3.5** (Wilkinson's matrix). Let `A ∈ ℝ^{n×n}` have entries `a_ij = 1` if `i = j`
or `j = n`, `a_ij = -1` if `i > j`, and `0` otherwise. Then `A` admits the (unique) LU
factorization `A = L U` with `L` the lower part of `A` (`l_ij = -1` below the diagonal, so
`|l_ij| ≤ 1`) and `U` the identity except for its last column `u_in = 2^{i-1}`, whence
`u_nn = 2^{n-1}`: the growth factor of GEM is `ρ_n = 2^{n-1}`, and the bound
`growthFactor_le_two_pow` of §3.10 is attained. -/
theorem exercise_3_5 [NeZero n] :
    let A : Matrix (Fin n) (Fin n) ℝ :=
      of fun i j => if i = j ∨ j = ⊤ then 1 else if j < i then -1 else 0
    let L : Matrix (Fin n) (Fin n) ℝ := of fun i j => if i = j then 1 else if j < i then -1 else 0
    let U : Matrix (Fin n) (Fin n) ℝ :=
      of fun i j => if j = ⊤ then 2 ^ (i : ℕ) else if i = j then 1 else 0
    IsLU A L U ∧ (∀ L' U', IsLU A L' U' → L' = L ∧ U' = U) ∧ (∀ i j, |L i j| ≤ 1) ∧
      U ⊤ ⊤ = 2 ^ (n - 1) ∧ equation_3_66 A = 2 ^ (n - 1) := by
  intro A L U
  have hLU : IsLU A L U := by
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, ?_⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      simp only [L, of_apply]
      rw [ite_eq_right hij'.ne, ite_eq_right hij'.not_gt]
    · simp [L]
    · have hij' : j < i := hij
      simp only [U, of_apply]
      rw [ite_eq_right (ne_top_of_lt hij'), ite_eq_right hij'.ne']
    · ext i k
      rw [mul_apply]
      by_cases hk : k = ⊤
      · subst hk
        have : ∀ j : Fin n, L i j * U j ⊤ =
            (if i = j then (2 : ℝ) ^ (i : ℕ) else 0) -
              if j < i then (2 : ℝ) ^ (j : ℕ) else 0 := by
          intro j
          have hU : U j ⊤ = 2 ^ (j : ℕ) := by simp [U]
          rw [hU]
          simp only [L, of_apply]
          rcases lt_trichotomy i j with h | h | h
          · rw [ite_eq_right h.ne, ite_eq_right h.not_gt, ite_eq_right h.ne, ite_eq_right h.not_gt]
            ring
          · subst h
            rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (lt_irrefl _)]
            ring
          · rw [ite_eq_right h.ne', ite_eq_left h, ite_eq_right h.ne', ite_eq_left h]
            ring
        rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, sum_fin_lt_two_pow,
          Finset.sum_ite_eq, ite_eq_left (mem_univ _)]
        simp [A]
      · rw [Finset.sum_eq_single k (fun j _ hjk => ?_) (fun h => absurd (mem_univ k) h)]
        · have hU : U k k = 1 := by simp [U, hk]
          rw [hU, mul_one]
          simp only [A, L, of_apply]
          by_cases hik : i = k
          · rw [ite_eq_left (Or.inl hik), ite_eq_left hik]
          · rw [ite_eq_right (not_or.2 ⟨hik, hk⟩), ite_eq_right hik]
        · simp only [U, of_apply]
          rw [ite_eq_right hk, ite_eq_right hjk, mul_zero]
  have hdiag : ∀ i, U i i ≠ 0 := fun i => by
    simp only [U, of_apply]
    split_ifs <;> positivity
  have hunit := isUnit_strict_of_isLU hLU hdiag
  have hL1 : ∀ i j, |L i j| ≤ 1 := fun i j => by
    simp only [L, of_apply]
    split_ifs <;> simp
  have hUtop : U ⊤ ⊤ = 2 ^ (n - 1) := by
    simp [U, Fin.val_top]
  refine ⟨hLU, fun L' U' h' => h'.unique hLU hunit, hL1, hUtop, ?_⟩
  -- the growth factor: the stages of GEM are those of the unique factorization
  have hpiv := (gemStage_pivots_ne_zero_iff A).2 hunit
  obtain ⟨hLeq, hUeq⟩ := (isLU_gemLower_gemStage A hpiv).unique hLU hunit
  have hsup : A.supAbs = 1 := by
    refine le_antisymm (supAbs_le zero_le_one fun i j => ?_) ?_
    · simp only [A, of_apply]
      split_ifs <;> simp
    · have := abs_apply_le_supAbs A 0 0
      simpa [A] using this
  refine le_antisymm ((growthFactor_le_two_pow (A := A)).1 fun k hk i hki => ?_) ?_
  · have : gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩ = gemLower A i ⟨k, hk⟩ := by
      simp only [gemLower, of_apply, ite_eq_left hki]
    rw [this, hLeq]
    exact hL1 i ⟨k, hk⟩
  · have := abs_gemStage_le_growthFactor_mul_supAbs A n ⊤ ⊤
    rw [hUeq, hUtop, hsup, mul_one, abs_of_pos (by positivity)] at this
    exact this

/-! ### Exercise 11 -/

/-- **Exercise 3.11.** Let `A ∈ ℝ^{n×n}` have nonzero entries only on the main diagonal, in
the first column and in the last row, with a nonzero diagonal. Then `A = L U` with `L` the
lower part of `A` scaled by the pivots and `U = diag(a_ii)`: there is no fill-in (the factors
vanish wherever `A` does), although the envelope (3.59) of `A` is the whole strict lower
triangle as soon as the first column is nonzero — "the hull can contain many zeros" (§3.9).
Exchanging the first and the last row and column (the hint), `σ = swap 0 n`, turns `A` into
`P A Pᵀ = A.submatrix σ σ`, which is upper triangular: its envelope is empty and its LU
factorization is `1 · (P A Pᵀ)`, with no fill-in at all. -/
theorem exercise_3_11 [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hpat : ∀ i j, A i j ≠ 0 → i = j ∨ j = 0 ∨ i = ⊤) (hdiag : ∀ i, A i i ≠ 0) :
    let L : Matrix (Fin n) (Fin n) ℝ :=
      of fun i j => if i = j then 1 else if j < i then A i j / A j j else 0
    let σ : Equiv.Perm (Fin n) := Equiv.swap 0 ⊤
    IsLU A L (diagonal fun i => A i i) ∧
      (∀ i j, i ≠ j → L i j ≠ 0 ∨ diagonal (fun i => A i i) i j ≠ 0 → A i j ≠ 0) ∧
        ((∀ i, 0 < i → A i 0 ≠ 0) → equation_3_59 A = {p | p.2 < p.1}) ∧
          (A.submatrix σ σ).IsUpperTriangular ∧ equation_3_59 (A.submatrix σ σ) = ∅ ∧
            IsLU (A.submatrix σ σ) 1 (A.submatrix σ σ) := by
  intro L σ
  have hupper : ∀ i j, i < j → A i j = 0 := fun i j hij => by
    by_contra h
    rcases hpat i j h with h' | h' | h'
    · exact hij.ne h'
    · exact (Fin.zero_le i).not_gt (h' ▸ hij)
    · exact (le_top (a := j)).not_gt (h' ▸ hij)
  have hLU : IsLU A L (diagonal fun i => A i i) := by
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => diagonal_apply_ne _ hij.ne', ?_⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      simp only [L, of_apply]
      rw [ite_eq_right hij'.ne, ite_eq_right hij'.not_gt]
    · simp [L]
    · ext i j
      rw [mul_diagonal]
      simp only [L, of_apply]
      rcases lt_trichotomy i j with h | h | h
      · rw [ite_eq_right h.ne, ite_eq_right h.not_gt, zero_mul, hupper i j h]
      · subst h
        rw [ite_eq_left rfl, one_mul]
      · rw [ite_eq_right h.ne', ite_eq_left h, div_mul_cancel₀ _ (hdiag j)]
  have hσ0 : ∀ j, σ j = 0 ↔ j = ⊤ := fun j => by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  have hσtop : ∀ i, σ i = ⊤ ↔ i = 0 := fun i => by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  have hBU : (A.submatrix σ σ).IsUpperTriangular := fun i j hij => by
    rw [submatrix_apply]
    by_contra h
    rcases hpat _ _ h with h' | h' | h'
    · exact hij.ne (σ.injective h').symm
    · rw [hσ0] at h'
      exact (le_top (a := i)).not_gt (h' ▸ hij)
    · rw [hσtop] at h'
      exact (Fin.zero_le j).not_gt (h' ▸ hij)
  refine ⟨hLU, fun i j hij h => ?_, fun hcol => ?_, hBU, ?_, ⟨⟨fun i j hij => ?_, fun i => ?_⟩,
    hBU, Matrix.one_mul _⟩⟩
  · rcases h with h | h
    · simp only [L, of_apply, ite_eq_right hij] at h
      split_ifs at h with hji
      · exact fun h0 => h (by rw [h0, zero_div])
      · exact absurd rfl h
    · exact absurd (diagonal_apply_ne _ hij) h
  · ext ⟨i, j⟩
    simp only [equation_3_59, envelope, Set.mem_ofPred_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, 0, Fin.zero_le _, hcol i ((Fin.zero_le j).trans_lt h)⟩⟩
  · ext ⟨i, j⟩
    simp only [equation_3_59, envelope, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and, not_exists]
    exact fun hji j₀ hj₀ h => h (hBU (hj₀.trans_lt hji))
  · exact one_apply_ne (OrderDual.toDual_lt_toDual.1 hij).ne
  · exact one_apply_eq i

/-! ### Exercise 15 -/

/-- **Exercise 3.15.** Let `A ∈ ℝ^{n×n}` be nonsingular, with singular system
`(σ_i; u_i, v_i)`, `i = 1, …, n`: `σ_i > 0`, `(u_i)` and `(v_i)` orthonormal, `A v_i = σ_i u_i`
and `Aᵀ u_i = σ_i v_i` (backbone `Matrix.exists_singularSystem`; `rank A = n`, so the `v_i` are
an orthonormal basis and every `d` expands as `d = ∑ d̃_i v_i` with `d̃_i = (v_i, d)`). Then the
solutions `x`, `y` of `Aᵀ x = d`, `A y = x` in (3.70) are `x = ∑ (d̃_i/σ_i) u_i` and
`y = ∑ (d̃_i/σ_i²) v_i`, and
`‖y‖₂/‖x‖₂ = [∑ (d̃_i/σ_i²)² / ∑ (d̃_i/σ_i)²]^{1/2}`. When this ratio approximates
`σ_n⁻¹ = ‖A⁻¹‖₂` (a `d̃_n` that is not too small, an ill-conditioned `A`) is the book's
discussion and is prose. -/
theorem exercise_3_15 [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    A.rank = n ∧
    ∃ (σ : Fin A.rank → ℝ) (u v : Fin A.rank → EuclideanSpace ℝ (Fin n)),
      (∀ i, 0 < σ i) ∧ Orthonormal ℝ u ∧ Orthonormal ℝ v ∧
      (∀ i, toLp 2 (A *ᵥ ofLp (v i)) = σ i • u i) ∧
      (∀ i, toLp 2 (Aᵀ *ᵥ ofLp (u i)) = σ i • v i) ∧
      (∀ d : Fin n → ℝ, toLp 2 d = ∑ i, ⟪v i, toLp 2 d⟫_ℝ • v i) ∧
      ∀ (d : Fin n → ℝ) (dt : Fin A.rank → ℝ), toLp 2 d = ∑ i, dt i • v i →
        toLp 2 (Aᵀ⁻¹ *ᵥ d) = ∑ i, (dt i / σ i) • u i ∧
        toLp 2 (A⁻¹ *ᵥ (Aᵀ⁻¹ *ᵥ d)) = ∑ i, (dt i / σ i ^ 2) • v i ∧
        ‖toLp 2 (A⁻¹ *ᵥ (Aᵀ⁻¹ *ᵥ d))‖ / ‖toLp 2 (Aᵀ⁻¹ *ᵥ d)‖ =
          √((∑ i, (dt i / σ i ^ 2) ^ 2) / ∑ i, (dt i / σ i) ^ 2) := by
  have hrank : A.rank = n := by rw [rank_of_isUnit A hA, Fintype.card_fin]
  obtain ⟨μ, u', v', hμ, hu', hv', hAu', hAv', -⟩ := exists_singularSystem A
  simp only [RCLike.ofReal_real_eq_id, id, conjTranspose_eq_transpose_of_trivial] at hAu' hAv'
  have hAT : IsUnit Aᵀ := (isUnit_transpose A).2 hA
  have hATd := (isUnit_iff_isUnit_det _).1 hAT
  have hAd := (isUnit_iff_isUnit_det _).1 hA
  -- the right singular vectors are an orthonormal basis
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range u') := by
    rw [hu'.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, finrank_euclideanSpace_fin, hrank])]
  set b := OrthonormalBasis.mk hu' hspan with hb
  have hexpand : ∀ d : Fin n → ℝ, toLp 2 d = ∑ i, ⟪u' i, toLp 2 d⟫_ℝ • u' i := fun d => by
    have := b.sum_repr' (toLp 2 d)
    rw [hb, OrthonormalBasis.coe_mk] at this
    exact this.symm
  -- norms of expansions along an orthonormal family
  have hnorm : ∀ (w : Fin A.rank → EuclideanSpace ℝ (Fin n)), Orthonormal ℝ w →
      ∀ c : Fin A.rank → ℝ, ‖∑ i, c i • w i‖ = √(∑ i, c i ^ 2) := fun w hw c => by
    rw [norm_eq_sqrt_real_inner, hw.inner_sum c c univ]
    simp only [starRingEnd_apply, star_trivial, sq]
  refine ⟨hrank, μ, v', u', hμ, hv', hu', hAu', hAv', hexpand, fun d dt hd => ?_⟩
  have hx : toLp 2 (Aᵀ⁻¹ *ᵥ d) = ∑ i, (dt i / μ i) • v' i := by
    have hsol : Aᵀ *ᵥ ofLp (∑ i, (dt i / μ i) • v' i) = d := by
      apply toLp_injective 2
      rw [← toEuclideanLin_apply, map_sum, hd]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hAv' i, smul_smul, div_mul_cancel₀ _ (hμ i).ne']
    rw [← hsol, mulVec_mulVec, nonsing_inv_mul _ hATd, one_mulVec, toLp_ofLp]
  have hy : toLp 2 (A⁻¹ *ᵥ (Aᵀ⁻¹ *ᵥ d)) = ∑ i, (dt i / μ i ^ 2) • u' i := by
    have hsol : A *ᵥ ofLp (∑ i, (dt i / μ i ^ 2) • u' i) = Aᵀ⁻¹ *ᵥ d := by
      apply toLp_injective 2
      rw [← toEuclideanLin_apply, map_sum, hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hAu' i, smul_smul, sq, ← div_div, div_mul_cancel₀ _ (hμ i).ne']
    rw [← hsol, mulVec_mulVec, nonsing_inv_mul _ hAd, one_mulVec, toLp_ofLp]
  refine ⟨hx, hy, ?_⟩
  rw [hx, hy, hnorm _ hu', hnorm _ hv', ← Real.sqrt_div (Finset.sum_nonneg fun i _ => sq_nonneg _)]

end QuarteroniSaccoSaleri.Chapter03
