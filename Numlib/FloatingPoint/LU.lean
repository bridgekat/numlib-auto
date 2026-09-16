import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.FloatingPoint.Substitution
import Numlib.LinearAlgebra.Matrix.LU.Pivoting

/-!
# Rounding errors of Gaussian elimination, Cholesky and the Thomas algorithm

The backward error of the LU factorization and of the solve built on it, in the relational
rounding model of `Numlib/FloatingPoint/Model`: [quarteroni2000numerical] §3.3.2, §3.4.2, §3.7.1
and §3.10, [higham2002accuracy] §9.3, §9.6 and §10.1.1.

The factorization is described in its Doolittle form, `FloatingPoint.RoundsLU m A L̂ Û`: `L̂` is
unit lower triangular, `Û` upper triangular, and every entry is an admissible value of the
recurrence [quarteroni2000numerical] (3.43) — `û_ij = a_ij - ∑_{r < i} l̂_ir û_rj` for `i ≤ j`,
`l̂_ij = (a_ij - ∑_{r < j} l̂_ir û_rj) / û_jj` for `j < i` — each computed as in
`Numlib/FloatingPoint/Substitution`: rounded products subtracted one after the other from `a_ij`
in any order, then (for `l̂_ij`) one rounded division. Every loop order of Gaussian elimination
performs exactly these operations on exactly these numbers ([higham2002accuracy] §9.3: "the
analysis applies to all the variants"), so one relation covers the book's Programs 4–6. The
Cholesky factor (`FloatingPoint.RoundsCholesky`) is the same shape with a square root on the
diagonal, modelled as one rounding of an exact square root, and the Thomas recurrence
(`FloatingPoint.RoundsThomas`) has its three roundings per step.

Results, entrywise (`Matrix.abs`, `≤ₑ`) over an ordered field:

* `FloatingPoint.exists_roundsLU_mul_eq_add`, [higham2002accuracy] Theorem 9.3 =
  [quarteroni2000numerical] (3.40): `L̂ Û = A + ΔA` with `|ΔA| ≤ γ_n |L̂| |Û|`, entry by entry from
  the scalar Lemma 8.4;
* `FloatingPoint.exists_roundsLU_solve_eq`, [higham2002accuracy] Theorem 9.4: factor, then two
  substitutions, gives `(A + ΔA) x̂ = b` with `|ΔA| ≤ γ_{3n} |L̂| |Û|`, the rigorous form of
  [quarteroni2000numerical] (3.64);
* `FloatingPoint.abs_le_of_roundsLU_of_entrywiseNonneg`, [quarteroni2000numerical] (3.41):
  `|ΔA| ≤ (n u / (1 - 2 n u)) |A|` when the computed factors are entrywise nonnegative, through
  the general `FloatingPoint.abs_entrywiseLE_of_abs_mul_eq` for factors with `|L| |U| = |L U|`;
* `FloatingPoint.linfty_opNorm_le_of_roundsLU_solve`, [higham2002accuracy] Theorem 9.5 =
  [quarteroni2000numerical] (3.67) (Wilkinson), in the conditional form the book's derivation
  deserves: under `|l̂_ij| ≤ 1` and `|û_ij| ≤ ρ max |a_ij|`, `‖ΔA‖_∞ ≤ n² γ_{3n} ρ ‖A‖_∞`. The
  "illicit manoeuvre" Higham confesses to is that these bounds hold for the exact factors (with
  `ρ` the growth factor of `Numlib/LinearAlgebra/Matrix/LU/Pivoting`) and not for the computed
  ones, so the honest theorem takes them as hypotheses;
* `FloatingPoint.exists_roundsCholesky_eq_add`, [higham2002accuracy] Theorem 10.3:
  `R̂ᵀ R̂ = A + ΔA` with `|ΔA| ≤ γ_{n+1} |R̂ᵀ| |R̂|` (the book quotes Wilkinson's normwise
  `8 n (n+1) u ‖A‖₂`, which is not reproduced);
* `FloatingPoint.exists_roundsThomas_mul_eq_add`, [higham2002accuracy] (9.20): the computed
  Thomas factors satisfy `L̂ Û = A + ΔA` with `|ΔA| ≤ γ₁ |L̂| |Û|` (Higham's `u`, in a model that
  only rounds as `x (1 + δ)`), and `FloatingPoint.exists_roundsThomas_mul_eq_add_of_diag_pos`,
  the factorization half of Theorem 9.14: `|ΔA| ≤ (u / (1 - 2u)) |A|` when the computed pivots
  and the products `β̂_i c_{i-1}` have the sign pattern of a symmetric positive definite or of an
  M-matrix.

The exact-arithmetic objects are `Numlib/LinearAlgebra/Matrix/LU`, `LU/Elimination`,
`LU/Pivoting` and `Cholesky`; the triangular solves are `Numlib/FloatingPoint/Substitution`.
-/

open Finset

open scoped Matrix

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : Type*} [Fintype n] [LinearOrder n]

/-! ### The computed LU factorization -/

/-- **The LU factorization in floating-point arithmetic**, Doolittle form. `RoundsLU m A L U`:
`L` is unit lower triangular, `U` upper triangular, and each entry is an admissible value of the
recurrence [quarteroni2000numerical] (3.43), computed by the running differences of
[higham2002accuracy] Lemma 8.4 in any order of the terms — `u_ij` for `i ≤ j` is the running
difference of `a_ij` and the rounded products `l_ir u_rj`, `r < i`; `l_ij` for `j < i` is the
running difference of `a_ij` and the rounded products `l_ir u_rj`, `r < j`, divided by `u_jj` with
one more rounding. -/
structure RoundsLU (m : RoundingModel K) (A L U : Matrix n n K) : Prop where
  /-- `L` vanishes above the diagonal. -/
  lower_apply_eq_zero : ∀ i j, i < j → L i j = 0
  /-- `L` has unit diagonal. -/
  lower_diag : ∀ i, L i i = 1
  /-- `U` vanishes below the diagonal. -/
  upper_apply_eq_zero : ∀ i j, j < i → U i j = 0
  /-- The entries of `U`: `u_ij = a_ij - ∑_{r < i} l_ir u_rj`, by running differences. -/
  upper : ∀ i j, i ≤ j → ∃ (o : List n) (p : n → K), o.Nodup ∧ (∀ r, r ∈ o ↔ r < i) ∧
    (∀ r ∈ o, m.Rounds (L i r * U r j) (p r)) ∧
    RoundsSumFrom m (A i j) (o.map fun r => -p r) (U i j)
  /-- The entries of `L`: `l_ij = (a_ij - ∑_{r < j} l_ir u_rj) / u_jj`, by running differences
  and one rounded division. -/
  lower : ∀ i j, j < i → ∃ (o : List n) (p : n → K) (t : K), o.Nodup ∧ (∀ r, r ∈ o ↔ r < j) ∧
    (∀ r ∈ o, m.Rounds (L i r * U r j) (p r)) ∧
    RoundsSumFrom m (A i j) (o.map fun r => -p r) t ∧ m.Rounds (t / U j j) (L i j)

variable {m : RoundingModel K} {A L U : Matrix n n K}

/-- The computed factors are an LU factorization of their product. -/
theorem RoundsLU.isLU_mul (h : RoundsLU m A L U) : Matrix.IsLU (L * U) L U :=
  ⟨⟨fun i j hij => h.lower_apply_eq_zero i j (OrderDual.toDual_lt_toDual.1 hij), h.lower_diag⟩,
    fun i j hij => h.upper_apply_eq_zero i j hij, rfl⟩

/-- The entry `(i, j)` of `|L| |U|` is `∑_{r ≤ min i j} |l_ir| |u_rj|`. -/
theorem RoundsLU.abs_mul_abs_apply (h : RoundsLU m A L U) (i j : n) :
    (L.abs * U.abs) i j = ∑ r ∈ univ.filter (· ≤ min i j), |L i r| * |U r j| := by
  have hLU : Matrix.IsLU (L.abs * U.abs) L.abs U.abs :=
    ⟨⟨fun i j hij => by
        simp [h.lower_apply_eq_zero i j (OrderDual.toDual_lt_toDual.1 hij)],
      fun i => by simp [h.lower_diag]⟩,
      fun i j hij => by simp [h.upper_apply_eq_zero i j hij], rfl⟩
  exact hLU.apply_eq_sum i j

/-- **One entry of [higham2002accuracy] Theorem 9.3**: `|(L U)_ij - a_ij| ≤ γ_n (|L| |U|)_ij`.
Above the diagonal the entry `u_ij` carries the running differences; below it, `l_ij u_jj`
carries them together with the division. In both cases the perturbation is charged to the terms
`l_ir u_rj`, `r ≤ min i j`. -/
theorem RoundsLU.abs_mul_sub_apply_le (hu : m.u < 1) (hcard : (Fintype.card n : K) * m.u < 1)
    (h : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0) (i j : n) :
    |(L * U) i j - A i j| ≤ gamma m.u (Fintype.card n) * (L.abs * U.abs) i j := by
  have hγ := gamma_nonneg m.u_nonneg hcard
  rw [h.isLU_mul.apply_eq_sum i j, h.abs_mul_abs_apply i j]
  rcases le_or_gt i j with hij | hji
  · -- the entry `u_ij`
    obtain ⟨o, p, hnd, ho, hp, ht⟩ := h.upper i j hij
    have hset : o.toFinset = univ.filter (· < i) := by ext r; simp [ho]
    have hlen : o.length + 1 = #{r | r ≤ i} := by
      rw [← List.toFinset_card_of_nodup hnd, hset, Finset.card_eq_sum_ones,
        Finset.card_eq_sum_ones, Matrix.sum_filter_le_eq_add]
    have hle : o.length + 1 ≤ Fintype.card n := hlen ▸ card_filter_le_le_card i
    have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard
    have hl : (o.length : K) * m.u < 1 := by
      have : (o.length : K) * m.u ≤ ((o.length + 1 : ℕ) : K) * m.u := by
        push_cast; nlinarith [m.u_nonneg]
      linarith
    obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_roundsSumFrom_map_eq hu hnd ht hl
    have hmono := gamma_mono m.u_nonneg hle hcard
    have hmono' := gamma_mono m.u_nonneg (Nat.le_succ o.length) hlu
    choose! ε hε hpε using fun r hr => (hp r hr).exists_delta
    rw [min_eq_left hij, Matrix.sum_filter_le_eq_add, Matrix.sum_filter_le_eq_add,
      h.lower_diag, one_mul, abs_one, one_mul, ← hset]
    have heq' : U i j * (1 + θ₀) =
        A i j - ∑ r ∈ o.toFinset, L i r * U r j * (1 + ε r) * (1 + θ r) := by
      rw [heq, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [hpε r (List.mem_toFinset.1 hr)]
      ring
    have hkey : ∑ r ∈ o.toFinset, L i r * U r j + U i j - A i j =
        -(∑ r ∈ o.toFinset, L i r * U r j * ((1 + ε r) * (1 + θ r) - 1) + U i j * θ₀) := by
      have hsum : ∑ r ∈ o.toFinset, L i r * U r j * ((1 + ε r) * (1 + θ r) - 1) =
          ∑ r ∈ o.toFinset, L i r * U r j * (1 + ε r) * (1 + θ r) -
            ∑ r ∈ o.toFinset, L i r * U r j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hsum]
      linear_combination heq'
    rw [hkey, abs_neg]
    calc |∑ r ∈ o.toFinset, L i r * U r j * ((1 + ε r) * (1 + θ r) - 1) + U i j * θ₀|
        ≤ ∑ r ∈ o.toFinset, gamma m.u (Fintype.card n) * (|L i r| * |U r j|) +
            gamma m.u (Fintype.card n) * |U i j| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
            rw [abs_mul, abs_mul, mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            have hr := List.mem_toFinset.1 hr
            have := abs_one_add_mul_one_add_sub_one_le_gamma m.u_nonneg hu hlu (hθ r hr) (hε r hr)
            rw [mul_comm (1 + ε r)]
            exact this.trans hmono
          · rw [abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hθ₀.trans (hmono'.trans hmono)) (abs_nonneg _)
      _ = gamma m.u (Fintype.card n) * (∑ r ∈ o.toFinset, |L i r| * |U r j| + |U i j|) := by
          rw [mul_add, Finset.mul_sum]
  · -- the entry `l_ij`
    obtain ⟨o, p, t, hnd, ho, hp, ht, hx⟩ := h.lower i j hji
    have hset : o.toFinset = univ.filter (· < j) := by ext r; simp [ho]
    have hlen : o.length + 1 = #{r | r ≤ j} := by
      rw [← List.toFinset_card_of_nodup hnd, hset, Finset.card_eq_sum_ones,
        Finset.card_eq_sum_ones, Matrix.sum_filter_le_eq_add]
    have hle : o.length + 1 ≤ Fintype.card n := hlen ▸ card_filter_le_le_card j
    have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard
    obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_rounds_sub_dot_div_eq hu hnd hp (hd j) ht hx hlu
    have hmono := gamma_mono m.u_nonneg hle hcard
    rw [min_eq_right hji.le, Matrix.sum_filter_le_eq_add, Matrix.sum_filter_le_eq_add, ← hset]
    have hkey : ∑ r ∈ o.toFinset, L i r * U r j + L i j * U j j - A i j =
        -(∑ r ∈ o.toFinset, L i r * U r j * θ r + L i j * U j j * θ₀) := by
      have hsum : ∑ r ∈ o.toFinset, L i r * U r j * θ r =
          ∑ r ∈ o.toFinset, L i r * U r j * (1 + θ r) - ∑ r ∈ o.toFinset, L i r * U r j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hsum]
      linear_combination heq
    rw [hkey, abs_neg]
    calc |∑ r ∈ o.toFinset, L i r * U r j * θ r + L i j * U j j * θ₀|
        ≤ ∑ r ∈ o.toFinset, gamma m.u (Fintype.card n) * (|L i r| * |U r j|) +
            gamma m.u (Fintype.card n) * (|L i j| * |U j j|) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
            rw [abs_mul, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right ((hθ r (List.mem_toFinset.1 hr)).trans hmono)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          · rw [abs_mul, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hθ₀.trans hmono)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = gamma m.u (Fintype.card n) *
            (∑ r ∈ o.toFinset, |L i r| * |U r j| + |L i j| * |U j j|) := by
          rw [mul_add, Finset.mul_sum]

/-- **[higham2002accuracy] Theorem 9.3**, [quarteroni2000numerical] (3.40): the computed LU
factors satisfy `L̂ Û = A + ΔA` with `|ΔA| ≤ γ_n |L̂| |Û|` entrywise, `n` the order of the matrix.
The pivots `û_jj` must be nonzero, since the model rounds `t / û_jj` with the junk value
`t / 0 = 0`. -/
theorem exists_roundsLU_mul_eq_add (hu : m.u < 1) (hcard : (Fintype.card n : K) * m.u < 1)
    (h : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0) :
    ∃ ΔA : Matrix n n K, ΔA.abs ≤ₑ gamma m.u (Fintype.card n) • (L.abs * U.abs) ∧
      L * U = A + ΔA :=
  ⟨L * U - A, fun i j => h.abs_mul_sub_apply_le hu hcard hd i j, by abel⟩

/-- `3 γ_n + γ_n² ≤ γ_{3n}`, the constant of [higham2002accuracy] Theorem 9.4, from Lemma 3.3
twice. -/
theorem three_mul_gamma_add_sq_le {u : K} (hu : 0 ≤ u) {k : ℕ} (h : ((3 * k : ℕ) : K) * u < 1) :
    3 * gamma u k + gamma u k ^ 2 ≤ gamma u (3 * k) := by
  have h2 : ((k + k : ℕ) : K) * u < 1 := by
    have : ((k + k : ℕ) : K) * u ≤ ((3 * k : ℕ) : K) * u := by
      push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg (α := K) k) hu]
    linarith
  have h3 : ((k + k + k : ℕ) : K) * u < 1 := by
    have : ((k + k + k : ℕ) : K) = ((3 * k : ℕ) : K) := by push_cast; ring
    rwa [this]
  have hk : (k : K) * u < 1 := by
    have : (k : K) * u ≤ ((3 * k : ℕ) : K) * u := by
      push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg (α := K) k) hu]
    linarith
  have hg := gamma_nonneg hu hk
  have hA := gamma_add_gamma_add_mul_le hu (j := k) (k := k) h2
  have hB := gamma_add_gamma_add_mul_le hu (j := k + k) (k := k) h3
  have hg2 : 0 ≤ gamma u (k + k) := gamma_nonneg hu h2
  have h3k : k + k + k = 3 * k := by ring
  rw [h3k] at hB
  nlinarith [mul_nonneg hg2 hg]

omit [LinearOrder n] in
/-- The error matrix of the solve, `ΔA₁ + L ΔU + ΔL U + ΔL ΔU`, is bounded by `(3γ + γ²) |L| |U|`
when each factor's error is bounded by `γ` times the factor. -/
theorem abs_add_mul_add_mul_add_mul_entrywiseLE {ΔA ΔL ΔU : Matrix n n K} {γ : K} (hγ : 0 ≤ γ)
    (hA : ΔA.abs ≤ₑ γ • (L.abs * U.abs)) (hL : ∀ i j, |ΔL i j| ≤ γ * |L i j|)
    (hU : ∀ i j, |ΔU i j| ≤ γ * |U i j|) :
    (ΔA + L * ΔU + ΔL * U + ΔL * ΔU).abs ≤ₑ (3 * γ + γ ^ 2) • (L.abs * U.abs) := by
  have hL' : ΔL.abs ≤ₑ γ • L.abs := hL
  have hU' : ΔU.abs ≤ₑ γ • U.abs := hU
  have hLabs := Matrix.entrywiseNonneg_abs L
  have hUabs := Matrix.entrywiseNonneg_abs U
  have h1 : (L * ΔU).abs ≤ₑ γ • (L.abs * U.abs) :=
    (Matrix.abs_mul_entrywiseLE L ΔU).trans (by
      rw [← Matrix.mul_smul]
      exact Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left hLabs hU')
  have h2 : (ΔL * U).abs ≤ₑ γ • (L.abs * U.abs) :=
    (Matrix.abs_mul_entrywiseLE ΔL U).trans (by
      rw [← Matrix.smul_mul]
      exact Matrix.EntrywiseLE.mul_of_entrywiseNonneg_right hUabs hL')
  have h3 : (ΔL * ΔU).abs ≤ₑ (γ * γ) • (L.abs * U.abs) :=
    (Matrix.abs_mul_entrywiseLE ΔL ΔU).trans (by
      rw [mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul]
      refine (Matrix.EntrywiseLE.mul_of_entrywiseNonneg_right (Matrix.entrywiseNonneg_abs ΔU)
        hL').trans ?_
      have hγL : (γ • L.abs).EntrywiseNonneg := fun i j => by
        simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.abs_apply]
        exact mul_nonneg hγ (abs_nonneg _)
      exact Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left hγL hU')
  intro i j
  have e1 := (Matrix.abs_add_entrywiseLE (ΔA + L * ΔU + ΔL * U) (ΔL * ΔU)) i j
  have e2 := (Matrix.abs_add_entrywiseLE (ΔA + L * ΔU) (ΔL * U)) i j
  have e3 := (Matrix.abs_add_entrywiseLE ΔA (L * ΔU)) i j
  have a1 := hA i j
  have a2 := h1 i j
  have a3 := h2 i j
  have a4 := h3 i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2 e3 a1 a2 a3 a4 ⊢
  nlinarith

/-- **[higham2002accuracy] Theorem 9.4**: factoring `A = L̂ Û` and solving the two triangular
systems by substitution yields a computed `x̂` with `(A + ΔA) x̂ = b`, `|ΔA| ≤ γ_{3n} |L̂| |Û|`.
This is the rigorous form of [quarteroni2000numerical] (3.64), whose `n u (3|A| + 5|L̂||Û|) +
O(u²)` is the first-order form of Golub and Van Loan. -/
theorem exists_roundsLU_solve_eq (hu : m.u < 1) (hcard : ((3 * Fintype.card n : ℕ) : K) * m.u < 1)
    (h : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0) {b y x : n → K}
    (hy : RoundsForwardSubst m L b y) (hx : RoundsBackSubst m U y x) :
    ∃ ΔA : Matrix n n K, ΔA.abs ≤ₑ gamma m.u (3 * Fintype.card n) • (L.abs * U.abs) ∧
      (A + ΔA) *ᵥ x = b := by
  have hcard' : (Fintype.card n : K) * m.u < 1 := by
    have : (Fintype.card n : K) * m.u ≤ ((3 * Fintype.card n : ℕ) : K) * m.u := by
      push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg (α := K) (Fintype.card n)) m.u_nonneg]
    linarith
  have hγ := gamma_nonneg m.u_nonneg hcard'
  obtain ⟨ΔA₁, hΔA₁, hLU⟩ := exists_roundsLU_mul_eq_add hu hcard' h hd
  obtain ⟨ΔL, hΔL, hyL⟩ := exists_roundsForwardSubst_eq hu hcard'
    h.isLU_mul.isUnitLowerTriangular.isLowerTriangular
    (fun i => by rw [h.lower_diag]; exact one_ne_zero) hy
  obtain ⟨ΔU, hΔU, hxU⟩ := exists_roundsBackSubst_eq hu hcard' h.isLU_mul.isUpperTriangular hd hx
  refine ⟨ΔA₁ + L * ΔU + ΔL * U + ΔL * ΔU, ?_, ?_⟩
  · refine (abs_add_mul_add_mul_add_mul_entrywiseLE hγ hΔA₁ hΔL hΔU).trans fun i j => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (three_mul_gamma_add_sq_le m.u_nonneg hcard)
      (((Matrix.entrywiseNonneg_abs L).mul (Matrix.entrywiseNonneg_abs U)).apply i j)
  · have : A + (ΔA₁ + L * ΔU + ΔL * U + ΔL * ΔU) = (L + ΔL) * (U + ΔU) := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hLU]
      abel
    rw [this, ← Matrix.mulVec_mulVec, hxU, hyL]

/-! ### Factors whose product has no cancellation -/

section NoCancellation

omit [LinearOrder n] in
/-- **The backward error is small relative to `A` when `|L| |U| = |L U|`** ([higham2002accuracy]
(9.8)–(9.9)): if `L U = A + ΔA` with `|ΔA| ≤ γ |L| |U|`, `γ < 1`, and the product has no
cancellation, then `|L| |U| = |A + ΔA| ≤ |A| + γ |L| |U|`, so `|L| |U| ≤ |A| / (1 - γ)` and
`|ΔA| ≤ (γ / (1 - γ)) |A|`. -/
theorem abs_entrywiseLE_of_abs_mul_eq {A L U ΔA : Matrix n n K} {γ : K} (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hΔ : ΔA.abs ≤ₑ γ • (L.abs * U.abs)) (hLU : L * U = A + ΔA)
    (habs : (L * U).abs = L.abs * U.abs) : ΔA.abs ≤ₑ (γ / (1 - γ)) • A.abs := by
  intro i j
  have hP : (L.abs * U.abs) i j ≤ |A i j| + |ΔA i j| := by
    rw [← habs, hLU]
    exact abs_add_le _ _
  have hd := hΔ i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.abs_apply] at hd ⊢
  have h1 : 0 < 1 - γ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith

/-- `γ_k / (1 - γ_k) = k u / (1 - 2 k u)`. -/
theorem gamma_div_one_sub_gamma {u : K} (hu : 0 ≤ u) {k : ℕ} (h : 2 * ((k : K) * u) < 1) :
    gamma u k / (1 - gamma u k) = k * u / (1 - 2 * (k * u)) := by
  have hk : (0 : K) ≤ k * u := mul_nonneg (Nat.cast_nonneg k) hu
  have h1 : (1 : K) - k * u ≠ 0 := by linarith
  have h2 : (1 : K) - 2 * (k * u) ≠ 0 := by linarith
  have : 1 - gamma u k = (1 - 2 * (k * u)) / (1 - k * u) := by
    rw [gamma_def]
    field_simp
    ring
  rw [this, gamma_def, div_div_div_cancel_right₀ h1]

/-- `γ_k < 1` when `2 k u < 1`. -/
theorem gamma_lt_one {u : K} (hu : 0 ≤ u) {k : ℕ} (h : 2 * ((k : K) * u) < 1) : gamma u k < 1 := by
  have hk : (0 : K) ≤ k * u := mul_nonneg (Nat.cast_nonneg k) hu
  rw [gamma_def, div_lt_one (by linarith)]
  linarith

variable {m : RoundingModel K} {A L U : Matrix n n K}

/-- **[quarteroni2000numerical] (3.41)**, [higham2002accuracy] (9.8): when the computed LU
factors are entrywise nonnegative, the backward error is small relative to `A` itself,
`|ΔA| ≤ (n u / (1 - 2 n u)) |A|`, since then `|L̂| |Û| = |L̂ Û| = |A + ΔA|`. -/
theorem abs_le_of_roundsLU_of_entrywiseNonneg (hu : m.u < 1)
    (hcard : 2 * ((Fintype.card n : K) * m.u) < 1) (h : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0)
    (hL : L.EntrywiseNonneg) (hU : U.EntrywiseNonneg) :
    ∃ ΔA : Matrix n n K,
      ΔA.abs ≤ₑ ((Fintype.card n : K) * m.u / (1 - 2 * ((Fintype.card n : K) * m.u))) • A.abs ∧
        L * U = A + ΔA := by
  have hcard' : (Fintype.card n : K) * m.u < 1 := by
    linarith [mul_nonneg (Nat.cast_nonneg (α := K) (Fintype.card n)) m.u_nonneg]
  obtain ⟨ΔA, hΔ, hLU⟩ := exists_roundsLU_mul_eq_add hu hcard' h hd
  refine ⟨ΔA, ?_, hLU⟩
  rw [← gamma_div_one_sub_gamma m.u_nonneg hcard]
  refine abs_entrywiseLE_of_abs_mul_eq (gamma_nonneg m.u_nonneg hcard')
    (gamma_lt_one m.u_nonneg hcard) hΔ hLU ?_
  have hLa : L.abs = L := Matrix.ext fun i j => abs_of_nonneg (hL.apply i j)
  have hUa : U.abs = U := Matrix.ext fun i j => abs_of_nonneg (hU.apply i j)
  rw [hLa, hUa]
  exact Matrix.ext fun i j => abs_of_nonneg ((hL.mul hU).apply i j)

end NoCancellation

/-! ### The normwise bound with the growth factor -/

section Normwise

open scoped Matrix.Norms.Operator

variable {μ ν : Type*} [Fintype μ] [Fintype ν]

/-- The largest entry is at most the maximum-row-sum norm. -/
theorem _root_.Matrix.supAbs_le_linfty_opNorm (B : Matrix μ ν ℝ) : B.supAbs ≤ ‖B‖ :=
  Matrix.supAbs_le (norm_nonneg _) (Matrix.abs_apply_le_linfty_opNorm B)

variable {m : RoundingModel ℝ} {A L U : Matrix n n ℝ}

/-- **[higham2002accuracy] Theorem 9.5**, [quarteroni2000numerical] (3.67) (Wilkinson), in its
honest conditional form: if the computed factors satisfy `|l̂_ij| ≤ 1` and `|û_ij| ≤ ρ max |a_ij|`,
then the backward error of the solve satisfies `‖ΔA‖_∞ ≤ n² γ_{3n} ρ ‖A‖_∞`. The two hypotheses
hold for the *exact* factors of Gaussian elimination with partial pivoting with `ρ` the growth
factor (`Matrix.gemPivotStage_partialPivotRow_norm_gemLower_le_one`,
`Matrix.abs_gemStage_le_growthFactor_mul_supAbs` of `Numlib/LinearAlgebra/Matrix/LU/Pivoting`),
which is the "illicit manoeuvre" Higham confesses to; with `ρ = ρ_n` this is the book's
`8 u n³ ρ_n ‖A‖_∞ + O(u²)` up to the constant (`n² γ_{3n} = 3 n³ u + O(u²)`). -/
theorem linfty_opNorm_le_of_roundsLU_solve (hu : m.u < 1)
    (hcard : ((3 * Fintype.card n : ℕ) : ℝ) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) {b y x : n → ℝ} (hy : RoundsForwardSubst m L b y)
    (hx : RoundsBackSubst m U y x) {ρ : ℝ} (hρ : 0 ≤ ρ) (hL : ∀ i j, |L i j| ≤ 1)
    (hU : ∀ i j, |U i j| ≤ ρ * A.supAbs) :
    ∃ ΔA : Matrix n n ℝ,
      ‖ΔA‖ ≤ (Fintype.card n : ℝ) ^ 2 * gamma m.u (3 * Fintype.card n) * ρ * ‖A‖ ∧
        (A + ΔA) *ᵥ x = b := by
  obtain ⟨ΔA, hΔ, hAx⟩ := exists_roundsLU_solve_eq hu hcard h hd hy hx
  refine ⟨ΔA, ?_, hAx⟩
  have hγ := gamma_nonneg m.u_nonneg hcard
  have hρS : 0 ≤ ρ * A.supAbs := mul_nonneg hρ (Matrix.supAbs_nonneg A)
  -- the row sums of `|L| |U|`
  have hrow : ∀ i, ∑ j, |(L.abs * U.abs) i j| ≤ (Fintype.card n : ℝ) ^ 2 * (ρ * A.supAbs) := by
    intro i
    have hnn : ∀ j, 0 ≤ (L.abs * U.abs) i j := fun j =>
      ((Matrix.entrywiseNonneg_abs L).mul (Matrix.entrywiseNonneg_abs U)).apply i j
    calc ∑ j, |(L.abs * U.abs) i j| = ∑ j, ∑ r, |L i r| * |U r j| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_of_nonneg (hnn j), Matrix.mul_apply]
          rfl
      _ ≤ ∑ _j : n, ∑ _r : n, 1 * (ρ * A.supAbs) := by
          gcongr with j _ r
          · exact hL i r
          · exact hU r j
      _ = (Fintype.card n : ℝ) ^ 2 * (ρ * A.supAbs) := by
          simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hΔabs : ΔA.abs ≤ₑ gamma m.u (3 * Fintype.card n) • (L.abs * U.abs).abs :=
    hΔ.trans (Matrix.EntrywiseLE.smul_of_nonneg hγ fun i j => le_abs_self _)
  calc ‖ΔA‖ ≤ gamma m.u (3 * Fintype.card n) * ‖L.abs * U.abs‖ :=
        Matrix.linfty_opNorm_le_mul_of_abs_entrywiseLE hγ hΔabs
    _ ≤ gamma m.u (3 * Fintype.card n) * ((Fintype.card n : ℝ) ^ 2 * (ρ * A.supAbs)) :=
        mul_le_mul_of_nonneg_left
          (Matrix.linfty_opNorm_le_of_forall_sum_le (by positivity) hrow) hγ
    _ ≤ gamma m.u (3 * Fintype.card n) * ((Fintype.card n : ℝ) ^ 2 * (ρ * ‖A‖)) := by
        gcongr
        exact Matrix.supAbs_le_linfty_opNorm A
    _ = (Fintype.card n : ℝ) ^ 2 * gamma m.u (3 * Fintype.card n) * ρ * ‖A‖ := by ring

end Normwise

/-! ### The computed Cholesky factorization -/

section Cholesky

variable {m : RoundingModel K} {A R : Matrix n n K}

/-- **The Cholesky factorization in floating-point arithmetic**, [quarteroni2000numerical] (3.45)
in the indexing of the upper factor `R = Hᵀ`, [higham2002accuracy] Algorithm 10.2: `R` is upper
triangular; the diagonal entry `r_jj` is an admissible rounding of an exact square root `s` of the
running difference `t` of `a_jj` and the rounded squares `r_rj²`, `r < j`; and the entry `r_ij`,
`i < j`, is the running difference of `a_ij` and the rounded products `r_ri r_rj`, `r < i`, divided
by `r_ii` with one more rounding. The square root is modelled as one rounding of an exact root
(`0 ≤ s`, `s * s = t`), which keeps the scalar field abstract; over `ℝ` it is `Real.sqrt t`, and
the relation is unsatisfiable when `t < 0`, which is the breakdown of the algorithm. -/
structure RoundsCholesky (m : RoundingModel K) (A R : Matrix n n K) : Prop where
  /-- `R` vanishes below the diagonal. -/
  apply_eq_zero : ∀ i j, j < i → R i j = 0
  /-- The diagonal: `r_jj = √(a_jj - ∑_{r < j} r_rj²)`. -/
  diag : ∀ j, ∃ (o : List n) (p : n → K) (t s : K), o.Nodup ∧ (∀ r, r ∈ o ↔ r < j) ∧
    (∀ r ∈ o, m.Rounds (R r j * R r j) (p r)) ∧
    RoundsSumFrom m (A j j) (o.map fun r => -p r) t ∧ 0 ≤ s ∧ s * s = t ∧ m.Rounds s (R j j)
  /-- Above the diagonal: `r_ij = (a_ij - ∑_{r < i} r_ri r_rj) / r_ii`. -/
  offDiag : ∀ i j, i < j → ∃ (o : List n) (p : n → K) (t : K), o.Nodup ∧ (∀ r, r ∈ o ↔ r < i) ∧
    (∀ r ∈ o, m.Rounds (R r i * R r j) (p r)) ∧
    RoundsSumFrom m (A i j) (o.map fun r => -p r) t ∧ m.Rounds (t / R i i) (R i j)

/-- The entry `(i, j)` of `Rᵀ R` for an upper triangular `R` is `∑_{r ≤ min i j} r_ri r_rj`. -/
theorem RoundsCholesky.transpose_mul_apply (h : RoundsCholesky m A R) (i j : n) :
    (Rᵀ * R) i j = ∑ r ∈ univ.filter (· ≤ min i j), R r i * R r j := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_filter_of_ne fun r _ hr => ?_).symm
  rw [le_min_iff]
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hir | hjr
  · exact hr (by rw [Matrix.transpose_apply, h.apply_eq_zero r i hir, zero_mul])
  · exact hr (by rw [h.apply_eq_zero r j hjr, mul_zero])

/-- The entry `(i, j)` of `|Rᵀ| |R|` is `∑_{r ≤ min i j} |r_ri| |r_rj|`. -/
theorem RoundsCholesky.abs_transpose_mul_abs_apply (h : RoundsCholesky m A R) (i j : n) :
    (Rᵀ.abs * R.abs) i j = ∑ r ∈ univ.filter (· ≤ min i j), |R r i| * |R r j| := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_filter_of_ne fun r _ hr => ?_).symm
  rw [le_min_iff]
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hir | hjr
  · exact hr (by
      rw [Matrix.abs_apply, Matrix.transpose_apply, h.apply_eq_zero r i hir, abs_zero, zero_mul])
  · exact hr (by rw [Matrix.abs_apply R, h.apply_eq_zero r j hjr, abs_zero, mul_zero])

omit [IsStrictOrderedRing K] [LinearOrder n] in
/-- The sums `Rᵀ R` and `|Rᵀ| |R|` are symmetric in `(i, j)`. -/
theorem transpose_mul_apply_comm (R : Matrix n n K) (i j : n) :
    (Rᵀ * R) i j = (Rᵀ * R) j i ∧ (Rᵀ.abs * R.abs) i j = (Rᵀ.abs * R.abs) j i := by
  constructor
  · rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ => by rw [Matrix.transpose_apply, Matrix.transpose_apply,
      mul_comm]
  · rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ => by
      rw [Matrix.abs_apply, Matrix.abs_apply, Matrix.abs_apply, Matrix.abs_apply,
        Matrix.transpose_apply, Matrix.transpose_apply, mul_comm]

/-- **One entry of [higham2002accuracy] Theorem 10.3**, on or above the diagonal:
`|(Rᵀ R)_ij - a_ij| ≤ γ_{n+1} (|Rᵀ| |R|)_ij`. The square root on the diagonal costs one more
rounding than the division of the LU case, whence `n + 1`. -/
theorem RoundsCholesky.abs_transpose_mul_sub_apply_le_of_le (hu : m.u < 1)
    (hcard : ((Fintype.card n + 1 : ℕ) : K) * m.u < 1) (h : RoundsCholesky m A R)
    (hd : ∀ i, R i i ≠ 0) {i j : n} (hij : i ≤ j) :
    |(Rᵀ * R) i j - A i j| ≤ gamma m.u (Fintype.card n + 1) * (Rᵀ.abs * R.abs) i j := by
  have hcard' : (Fintype.card n : K) * m.u < 1 := by
    have : (Fintype.card n : K) * m.u ≤ ((Fintype.card n + 1 : ℕ) : K) * m.u := by
      push_cast; nlinarith [m.u_nonneg]
    linarith
  have hγ := gamma_nonneg m.u_nonneg hcard
  have hmonon := gamma_mono m.u_nonneg (Nat.le_succ (Fintype.card n)) hcard
  rw [h.transpose_mul_apply i j, h.abs_transpose_mul_abs_apply i j, min_eq_left hij,
    Matrix.sum_filter_le_eq_add, Matrix.sum_filter_le_eq_add]
  rcases hij.eq_or_lt with rfl | hlt
  · -- the diagonal
    obtain ⟨o, p, t, s, hnd, ho, hp, ht, hs0, hs, hR⟩ := h.diag i
    have hset : o.toFinset = univ.filter (· < i) := by ext r; simp [ho]
    have hlen : o.length + 1 = #{r | r ≤ i} := by
      rw [← List.toFinset_card_of_nodup hnd, hset, Finset.card_eq_sum_ones,
        Finset.card_eq_sum_ones, Matrix.sum_filter_le_eq_add]
    have hle : o.length + 1 ≤ Fintype.card n := hlen ▸ card_filter_le_le_card i
    have hle2 : o.length + 2 ≤ Fintype.card n + 1 := by omega
    have hlu2 : ((o.length + 2 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle2) m.u_nonneg).trans_lt hcard
    have hlu1 : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard'
    have hl : (o.length : K) * m.u < 1 := by
      have : (o.length : K) * m.u ≤ ((o.length + 1 : ℕ) : K) * m.u := by
        push_cast; nlinarith [m.u_nonneg]
      linarith
    obtain ⟨θ₀', θ', hθ₀', hθ', heq⟩ := exists_roundsSumFrom_map_eq hu hnd ht hl
    obtain ⟨δ, hδ, hRδ⟩ := hR.exists_delta
    choose! ε hε hpε using fun r hr => (hp r hr).exists_delta
    have hd1 : (1 : K) + δ ≠ 0 := by linarith [neg_le_of_abs_le hδ]
    have hmono2 := gamma_mono m.u_nonneg hle2 hcard
    have hmono1 := gamma_mono m.u_nonneg hle hcard'
    -- the perturbation of the pivot: two divisions by `1 + δ`
    set θ₀ : K := (1 + θ₀') / (1 + δ) / (1 + δ) - 1 with hθ₀def
    have hθ₀ : |θ₀| ≤ gamma m.u (o.length + 2) := by
      have h1 := abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu1 hθ₀' hδ
      have h2 := abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu2 h1 hδ
      rwa [add_sub_cancel] at h2
    have hRR : R i i * R i i * (1 + θ₀) = t * (1 + θ₀') := by
      rw [hθ₀def, hRδ, add_sub_cancel, ← hs]
      field_simp
    have heq' : R i i * R i i * (1 + θ₀) =
        A i i - ∑ r ∈ o.toFinset, R r i * R r i * (1 + θ' r) * (1 + ε r) := by
      rw [hRR, heq, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [hpε r (List.mem_toFinset.1 hr)]
      ring
    rw [← hset]
    have hkey : ∑ r ∈ o.toFinset, R r i * R r i + R i i * R i i - A i i =
        -(∑ r ∈ o.toFinset, R r i * R r i * ((1 + θ' r) * (1 + ε r) - 1) + R i i * R i i * θ₀) := by
      have hsum : ∑ r ∈ o.toFinset, R r i * R r i * ((1 + θ' r) * (1 + ε r) - 1) =
          ∑ r ∈ o.toFinset, R r i * R r i * (1 + θ' r) * (1 + ε r) -
            ∑ r ∈ o.toFinset, R r i * R r i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hsum]
      linear_combination heq'
    rw [hkey, abs_neg]
    calc |∑ r ∈ o.toFinset, R r i * R r i * ((1 + θ' r) * (1 + ε r) - 1) + R i i * R i i * θ₀|
        ≤ ∑ r ∈ o.toFinset, gamma m.u (Fintype.card n + 1) * (|R r i| * |R r i|) +
            gamma m.u (Fintype.card n + 1) * (|R i i| * |R i i|) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
            rw [abs_mul, abs_mul, mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            have hr := List.mem_toFinset.1 hr
            exact (abs_one_add_mul_one_add_sub_one_le_gamma m.u_nonneg hu hlu1 (hθ' r hr)
              (hε r hr)).trans (hmono1.trans hmonon)
          · rw [abs_mul, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hθ₀.trans hmono2)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = gamma m.u (Fintype.card n + 1) *
            (∑ r ∈ o.toFinset, |R r i| * |R r i| + |R i i| * |R i i|) := by
          rw [mul_add, Finset.mul_sum]
  · -- above the diagonal
    obtain ⟨o, p, t, hnd, ho, hp, ht, hx⟩ := h.offDiag i j hlt
    have hset : o.toFinset = univ.filter (· < i) := by ext r; simp [ho]
    have hlen : o.length + 1 = #{r | r ≤ i} := by
      rw [← List.toFinset_card_of_nodup hnd, hset, Finset.card_eq_sum_ones,
        Finset.card_eq_sum_ones, Matrix.sum_filter_le_eq_add]
    have hle : o.length + 1 ≤ Fintype.card n := hlen ▸ card_filter_le_le_card i
    have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard'
    obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_rounds_sub_dot_div_eq hu hnd hp (hd i) ht hx hlu
    have hmono := (gamma_mono m.u_nonneg hle hcard').trans hmonon
    rw [← hset]
    have hkey : ∑ r ∈ o.toFinset, R r i * R r j + R i i * R i j - A i j =
        -(∑ r ∈ o.toFinset, R r i * R r j * θ r + R i i * R i j * θ₀) := by
      have hsum : ∑ r ∈ o.toFinset, R r i * R r j * θ r =
          ∑ r ∈ o.toFinset, R r i * R r j * (1 + θ r) - ∑ r ∈ o.toFinset, R r i * R r j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hsum]
      linear_combination heq
    rw [hkey, abs_neg]
    calc |∑ r ∈ o.toFinset, R r i * R r j * θ r + R i i * R i j * θ₀|
        ≤ ∑ r ∈ o.toFinset, gamma m.u (Fintype.card n + 1) * (|R r i| * |R r j|) +
            gamma m.u (Fintype.card n + 1) * (|R i i| * |R i j|) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
            rw [abs_mul, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right ((hθ r (List.mem_toFinset.1 hr)).trans hmono)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          · rw [abs_mul, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hθ₀.trans hmono)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = gamma m.u (Fintype.card n + 1) *
            (∑ r ∈ o.toFinset, |R r i| * |R r j| + |R i i| * |R i j|) := by
          rw [mul_add, Finset.mul_sum]

/-- **[higham2002accuracy] Theorem 10.3**: the computed Cholesky factor of a symmetric matrix
satisfies `R̂ᵀ R̂ = A + ΔA` with `|ΔA| ≤ γ_{n+1} |R̂ᵀ| |R̂|` entrywise. The square root costs one
rounding more than the division of Gaussian elimination, whence `n + 1`; [quarteroni2000numerical]
§3.4.2 quotes instead Wilkinson's normwise `‖ΔA‖₂ ≤ 8 n (n + 1) u ‖A‖₂`, which is not
reproduced. The entries below the diagonal follow from the symmetry of `A`; the diagonal of `R̂`
must be nonzero for the divisions. -/
theorem exists_roundsCholesky_eq_add (hu : m.u < 1)
    (hcard : ((Fintype.card n + 1 : ℕ) : K) * m.u < 1) (hA : A.IsSymm)
    (h : RoundsCholesky m A R) (hd : ∀ i, R i i ≠ 0) :
    ∃ ΔA : Matrix n n K, ΔA.abs ≤ₑ gamma m.u (Fintype.card n + 1) • (Rᵀ.abs * R.abs) ∧
      Rᵀ * R = A + ΔA := by
  refine ⟨Rᵀ * R - A, fun i j => ?_, by abel⟩
  simp only [Matrix.abs_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rcases le_or_gt i j with hij | hji
  · exact h.abs_transpose_mul_sub_apply_le_of_le hu hcard hd hij
  · obtain ⟨h1, h2⟩ := transpose_mul_apply_comm R i j
    rw [h1, h2, hA.apply j i]
    exact h.abs_transpose_mul_sub_apply_le_of_le hu hcard hd hji.le

end Cholesky

/-! ### The Thomas algorithm -/

section Thomas

variable {m : RoundingModel K} {N : ℕ}

/-- The unit lower bidiagonal matrix with subdiagonal `β`: `Matrix.thomasLower a b c N` is
`lowerBidiagonalOf (Matrix.thomasBeta a b c) N` (`FloatingPoint.thomasLower_eq`). -/
def lowerBidiagonalOf (β : ℕ → K) (N : ℕ) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => if i = j then 1 else if (j : ℕ) + 1 = i then β i else 0

/-- The upper bidiagonal matrix with diagonal `α` and superdiagonal `c`:
`Matrix.thomasUpper a b c N` is `upperBidiagonalOf (Matrix.thomasAlpha a b c) c N`
(`FloatingPoint.thomasUpper_eq`). -/
def upperBidiagonalOf (α c : ℕ → K) (N : ℕ) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => if i = j then α i else if (i : ℕ) + 1 = j then c i else 0

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The exact Thomas lower factor is the bidiagonal matrix of the exact multipliers. -/
theorem thomasLower_eq (a b c : ℕ → K) (N : ℕ) :
    Matrix.thomasLower a b c N = lowerBidiagonalOf (Matrix.thomasBeta a b c) N := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The exact Thomas upper factor is the bidiagonal matrix of the exact pivots. -/
theorem thomasUpper_eq (a b c : ℕ → K) (N : ℕ) :
    Matrix.thomasUpper a b c N = upperBidiagonalOf (Matrix.thomasAlpha a b c) c N := rfl

/-- The entrywise absolute value of the lower bidiagonal matrix. -/
theorem abs_lowerBidiagonalOf (β : ℕ → K) (N : ℕ) :
    (lowerBidiagonalOf β N).abs = lowerBidiagonalOf (fun i => |β i|) N := by
  ext i j
  simp only [Matrix.abs_apply, lowerBidiagonalOf, Matrix.of_apply]
  split_ifs <;> simp

/-- The entrywise absolute value of the upper bidiagonal matrix. -/
theorem abs_upperBidiagonalOf (α c : ℕ → K) (N : ℕ) :
    (upperBidiagonalOf α c N).abs = upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N := by
  ext i j
  simp only [Matrix.abs_apply, upperBidiagonalOf, Matrix.of_apply]
  split_ifs <;> simp

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Left multiplication by the lower bidiagonal matrix adds `β_i` times the previous row. -/
theorem lowerBidiagonalOf_mul_apply (β : ℕ → K) (M : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    (lowerBidiagonalOf β N * M) i j =
      M i j + if h : 0 < (i : ℕ) then β i * M ⟨i - 1, by omega⟩ j else 0 := by
  rw [Matrix.mul_apply]
  have hterm : ∀ r : Fin N, lowerBidiagonalOf β N i r * M r j =
      (if r = i then M i j else 0) + if _h : (r : ℕ) + 1 = i then β i * M r j else 0 := by
    intro r
    simp only [lowerBidiagonalOf, Matrix.of_apply]
    by_cases hri : r = i
    · subst hri
      simp
    · simp only [Ne.symm hri, hri, ite_false, zero_add]
      split_ifs <;> simp
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Matrix.sum_dite_val_add_one_eq]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- An entry of the upper bidiagonal matrix off its two diagonals vanishes. -/
theorem upperBidiagonalOf_apply_eq_zero {α c : ℕ → K} {i j : Fin N} (h1 : (i : ℕ) ≠ j)
    (h2 : (i : ℕ) + 1 ≠ j) : upperBidiagonalOf α c N i j = 0 := by
  simp [upperBidiagonalOf, Fin.ext_iff, h1, h2]

/-- The entries of the upper bidiagonal matrix of absolute values are nonnegative. -/
theorem upperBidiagonalOf_abs_nonneg (α c : ℕ → K) (i j : Fin N) :
    0 ≤ upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N i j := by
  simp only [upperBidiagonalOf, Matrix.of_apply]
  split_ifs <;> positivity

/-- **The Thomas algorithm in floating-point arithmetic**, [quarteroni2000numerical] (3.53) with
its three roundings per step: `α̂₀ = a₀`, `β̂_{i+1}` is an admissible rounding of `b_{i+1} / α̂_i`,
and `α̂_{i+1}` of `a_{i+1} - fl(β̂_{i+1} c_i)`. -/
structure RoundsThomas (m : RoundingModel K) (a b c α β : ℕ → K) : Prop where
  /-- The first pivot is exact. -/
  alpha_zero : α 0 = a 0
  /-- The multipliers: `β_{i+1} = fl(b_{i+1} / α_i)`. -/
  beta_succ : ∀ i, m.Rounds (b (i + 1) / α i) (β (i + 1))
  /-- The pivots: `α_{i+1} = fl(a_{i+1} - fl(β_{i+1} c_i))`. -/
  alpha_succ : ∀ i, ∃ q, m.Rounds (β (i + 1) * c i) q ∧ m.Rounds (a (i + 1) - q) (α (i + 1))

variable {a b c α β : ℕ → K}

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `u ≤ γ₁ = u / (1 - u)`. -/
theorem gamma_one_eq {u : K} : gamma u 1 = u / (1 - u) := by simp [gamma_def]

/-- **One diagonal entry of the Thomas factorization**: `|α̂_{i+1} + β̂_{i+1} c_i - a_{i+1}| ≤
γ₁ (|α̂_{i+1}| + |β̂_{i+1}| |c_i|)`. -/
theorem RoundsThomas.abs_alpha_add_mul_sub_le (hu : m.u < 1) (h : RoundsThomas m a b c α β)
    (i : ℕ) :
    |α (i + 1) + β (i + 1) * c i - a (i + 1)| ≤
      gamma m.u 1 * (|α (i + 1)| + |β (i + 1)| * |c i|) := by
  obtain ⟨q, hq, hα⟩ := h.alpha_succ i
  obtain ⟨δ₁, hδ₁, rfl⟩ := hq.exists_delta
  obtain ⟨δ₂, hδ₂, hα'⟩ := hα.exists_delta
  have hd : (0 : K) < 1 + δ₂ := by linarith [neg_le_of_abs_le hδ₂]
  have hu1 : (0 : K) < 1 - m.u := by linarith
  have hkey : α (i + 1) + β (i + 1) * c i - a (i + 1) =
      α (i + 1) * (δ₂ / (1 + δ₂)) - β (i + 1) * c i * δ₁ := by
    rw [hα']
    field_simp
    ring
  rw [hkey, gamma_one_eq]
  have h1 : |α (i + 1) * (δ₂ / (1 + δ₂))| ≤ m.u / (1 - m.u) * |α (i + 1)| := by
    rw [abs_mul, abs_div, abs_of_pos hd, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [div_le_div_iff₀ hd hu1]
    nlinarith [neg_le_of_abs_le hδ₂, le_of_abs_le hδ₂, abs_nonneg δ₂, m.u_nonneg]
  have h2 : |β (i + 1) * c i * δ₁| ≤ m.u / (1 - m.u) * (|β (i + 1)| * |c i|) := by
    rw [abs_mul, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right (hδ₁.trans ?_) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    rw [le_div_iff₀ hu1]
    nlinarith [m.u_nonneg]
  calc |α (i + 1) * (δ₂ / (1 + δ₂)) - β (i + 1) * c i * δ₁|
      ≤ |α (i + 1) * (δ₂ / (1 + δ₂))| + |β (i + 1) * c i * δ₁| := abs_sub _ _
    _ ≤ m.u / (1 - m.u) * |α (i + 1)| + m.u / (1 - m.u) * (|β (i + 1)| * |c i|) :=
        add_le_add h1 h2
    _ = m.u / (1 - m.u) * (|α (i + 1)| + |β (i + 1)| * |c i|) := by ring

/-- **One subdiagonal entry of the Thomas factorization**:
`|β̂_{i+1} α̂_i - b_{i+1}| ≤ γ₁ |β̂_{i+1}| |α̂_i|`, for a nonzero pivot `α̂_i`. -/
theorem RoundsThomas.abs_beta_mul_alpha_sub_le (hu : m.u < 1) (h : RoundsThomas m a b c α β)
    (i : ℕ) (hα : α i ≠ 0) :
    |β (i + 1) * α i - b (i + 1)| ≤ gamma m.u 1 * (|β (i + 1)| * |α i|) := by
  obtain ⟨ε, hε, hβ⟩ := (h.beta_succ i).exists_delta
  have hd : (0 : K) < 1 + ε := by linarith [neg_le_of_abs_le hε]
  have hu1 : (0 : K) < 1 - m.u := by linarith
  have hkey : β (i + 1) * α i - b (i + 1) = β (i + 1) * α i * (ε / (1 + ε)) := by
    rw [hβ]
    field_simp
    ring
  rw [hkey, gamma_one_eq, abs_mul, abs_mul, abs_div, abs_of_pos hd, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [div_le_div_iff₀ hd hu1]
  nlinarith [neg_le_of_abs_le hε, le_of_abs_le hε, abs_nonneg ε, m.u_nonneg]

/-- **[higham2002accuracy] (9.20)**, the backward error of the Thomas factorization: the
bidiagonal factors built from the computed multipliers and pivots satisfy `L̂ Û = A + ΔA` with
`|ΔA| ≤ γ₁ |L̂| |Û|`, `A` the tridiagonal matrix of `a`, `b`, `c`. The perturbation lives on the
diagonal and the subdiagonal; the superdiagonal `c` is reproduced exactly. Higham's constant is
`u`, with the rounding written as a division `x / (1 + δ)`; the relational model only provides
`x (1 + δ)`, which costs `γ₁ = u / (1 - u)`. The pivots must be nonzero for the divisions. -/
theorem exists_roundsThomas_mul_eq_add (hu : m.u < 1) (h : RoundsThomas m a b c α β)
    (hα : ∀ i, α i ≠ 0) (N : ℕ) :
    ∃ ΔA : Matrix (Fin N) (Fin N) K,
      ΔA.abs ≤ₑ gamma m.u 1 • ((lowerBidiagonalOf β N).abs * (upperBidiagonalOf α c N).abs) ∧
        lowerBidiagonalOf β N * upperBidiagonalOf α c N = Matrix.tridiagonalOfNat a b c N + ΔA := by
  have hγ : 0 ≤ gamma m.u 1 := gamma_nonneg m.u_nonneg (by simpa using hu)
  refine ⟨_ - _, fun i j => ?_, (add_sub_cancel _ _).symm⟩
  simp only [Matrix.abs_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [lowerBidiagonalOf_mul_apply, abs_lowerBidiagonalOf, abs_upperBidiagonalOf,
    lowerBidiagonalOf_mul_apply]
  by_cases hi : 0 < (i : ℕ)
  swap
  · -- the first row: `α₀ = a₀`, and the superdiagonal is exact
    simp only [hi, dite_false, add_zero]
    have hi0 : (i : ℕ) = 0 := by omega
    by_cases hij : (i : ℕ) = j
    · have hU : upperBidiagonalOf α c N i j = α i := by
        simp [upperBidiagonalOf, Fin.ext_iff, hij]
      have hA : Matrix.tridiagonalOfNat a b c N i j = a i := by
        simp [Matrix.tridiagonalOfNat, hij]
      rw [hU, hA, hi0, h.alpha_zero, sub_self, abs_zero]
      exact mul_nonneg hγ (upperBidiagonalOf_abs_nonneg α c i j)
    by_cases hsup : (i : ℕ) + 1 = j
    · have hU : upperBidiagonalOf α c N i j = c i := by
        simp [upperBidiagonalOf, Fin.ext_iff, hij, hsup]
      have hA : Matrix.tridiagonalOfNat a b c N i j = c i := by
        simp [Matrix.tridiagonalOfNat, hij, hsup, show ¬ ((j : ℕ) + 1 = i) by omega]
      rw [hU, hA, sub_self, abs_zero]
      exact mul_nonneg hγ (upperBidiagonalOf_abs_nonneg α c i j)
    · have hU : upperBidiagonalOf α c N i j = 0 := upperBidiagonalOf_apply_eq_zero hij hsup
      have hA : Matrix.tridiagonalOfNat a b c N i j = 0 := by
        simp [Matrix.tridiagonalOfNat, hij, hsup, show ¬ ((j : ℕ) + 1 = i) by omega]
      rw [hU, hA, sub_self, abs_zero]
      exact mul_nonneg hγ (upperBidiagonalOf_abs_nonneg α c i j)
  simp only [hi, dite_true]
  have hi' : (i : ℕ) - 1 + 1 = i := by omega
  by_cases hij : (i : ℕ) = j
  · -- the diagonal
    have hUii : upperBidiagonalOf α c N i j = α i := by simp [upperBidiagonalOf, Fin.ext_iff, hij]
    have hUi'i : upperBidiagonalOf α c N ⟨i - 1, by omega⟩ j = c (i - 1) := by
      simp [upperBidiagonalOf, Fin.ext_iff, ← hij, show (i : ℕ) - 1 ≠ i by omega, hi']
    have hUii' : upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N i j = |α i| := by
      simp [upperBidiagonalOf, Fin.ext_iff, hij]
    have hUi'i' : upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N ⟨i - 1, by omega⟩ j =
        |c (i - 1)| := by
      simp [upperBidiagonalOf, Fin.ext_iff, ← hij, show (i : ℕ) - 1 ≠ i by omega, hi']
    have hA : Matrix.tridiagonalOfNat a b c N i j = a i := by
      simp [Matrix.tridiagonalOfNat, hij]
    rw [hUii, hUi'i, hUii', hUi'i', hA]
    have := h.abs_alpha_add_mul_sub_le hu (i - 1)
    rw [hi'] at this
    exact this
  by_cases hsub : (j : ℕ) + 1 = i
  · -- the subdiagonal
    have hUij : upperBidiagonalOf α c N i j = 0 := upperBidiagonalOf_apply_eq_zero hij (by omega)
    have hUi'j : upperBidiagonalOf α c N ⟨i - 1, by omega⟩ j = α (i - 1) := by
      simp [upperBidiagonalOf, Fin.ext_iff, show (i : ℕ) - 1 = j by omega]
    have hUij' : upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N i j = 0 :=
      upperBidiagonalOf_apply_eq_zero hij (by omega)
    have hUi'j' : upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N ⟨i - 1, by omega⟩ j =
        |α (i - 1)| := by
      simp [upperBidiagonalOf, Fin.ext_iff, show (i : ℕ) - 1 = j by omega]
    have hA : Matrix.tridiagonalOfNat a b c N i j = b i := by
      simp [Matrix.tridiagonalOfNat, hij, hsub]
    rw [hUij, hUi'j, hUij', hUi'j', hA, zero_add, zero_add]
    have := h.abs_beta_mul_alpha_sub_le hu (i - 1) (hα (i - 1))
    rw [hi'] at this
    exact this
  · -- the superdiagonal and the rest: exact
    have hUi'j : upperBidiagonalOf α c N ⟨i - 1, by omega⟩ j = 0 :=
      upperBidiagonalOf_apply_eq_zero (by simp; omega) (by simp; omega)
    have hUi'j' : upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N ⟨i - 1, by omega⟩ j = 0 :=
      upperBidiagonalOf_apply_eq_zero (by simp; omega) (by simp; omega)
    rw [hUi'j, hUi'j', mul_zero, mul_zero, add_zero, add_zero]
    by_cases hsup : (i : ℕ) + 1 = j
    · have hU : upperBidiagonalOf α c N i j = c i := by
        simp [upperBidiagonalOf, Fin.ext_iff, hij, hsup]
      have hA : Matrix.tridiagonalOfNat a b c N i j = c i := by
        simp [Matrix.tridiagonalOfNat, hij, hsub, hsup]
      rw [hU, hA, sub_self, abs_zero]
      exact mul_nonneg hγ (upperBidiagonalOf_abs_nonneg α c i j)
    · have hU : upperBidiagonalOf α c N i j = 0 := upperBidiagonalOf_apply_eq_zero hij hsup
      have hA : Matrix.tridiagonalOfNat a b c N i j = 0 := by
        simp [Matrix.tridiagonalOfNat, hij, hsub, hsup]
      rw [hU, hA, sub_self, abs_zero]
      exact mul_nonneg hγ (upperBidiagonalOf_abs_nonneg α c i j)

/-- When the computed pivots are positive and the products `β̂_{i+1} c_i` nonnegative, the
product of the computed Thomas factors has no cancellation: `|L̂ Û| = |L̂| |Û|`. -/
theorem abs_lowerBidiagonalOf_mul_upperBidiagonalOf (hα : ∀ i, 0 < α i)
    (hbc : ∀ i, 0 ≤ β (i + 1) * c i) (N : ℕ) :
    (lowerBidiagonalOf β N * upperBidiagonalOf α c N).abs =
      (lowerBidiagonalOf β N).abs * (upperBidiagonalOf α c N).abs := by
  ext i j
  rw [Matrix.abs_apply, lowerBidiagonalOf_mul_apply, abs_lowerBidiagonalOf, abs_upperBidiagonalOf,
    lowerBidiagonalOf_mul_apply]
  by_cases hi : 0 < (i : ℕ)
  swap
  · simp only [hi, dite_false, add_zero]
    simp [upperBidiagonalOf]
    split_ifs <;> simp
  simp only [hi, dite_true]
  have hi' : (i : ℕ) - 1 + 1 = i := by omega
  by_cases hij : (i : ℕ) = j
  · have hUii : upperBidiagonalOf α c N i j = α i := by simp [upperBidiagonalOf, Fin.ext_iff, hij]
    have hUi'i : upperBidiagonalOf α c N ⟨i - 1, by omega⟩ j = c (i - 1) := by
      simp [upperBidiagonalOf, Fin.ext_iff, ← hij, show (i : ℕ) - 1 ≠ i by omega, hi']
    have hUii' : upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N i j = |α i| := by
      simp [upperBidiagonalOf, Fin.ext_iff, hij]
    have hUi'i' : upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N ⟨i - 1, by omega⟩ j =
        |c (i - 1)| := by
      simp [upperBidiagonalOf, Fin.ext_iff, ← hij, show (i : ℕ) - 1 ≠ i by omega, hi']
    rw [hUii, hUi'i, hUii', hUi'i']
    have h1 := hα i
    have h2 := hbc (i - 1)
    rw [hi'] at h2
    rw [abs_of_nonneg (add_nonneg h1.le h2), abs_of_pos h1, ← abs_mul, abs_of_nonneg h2]
  by_cases hsub : (j : ℕ) + 1 = i
  · have hUij : upperBidiagonalOf α c N i j = 0 := upperBidiagonalOf_apply_eq_zero hij (by omega)
    have hUij' : upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N i j = 0 :=
      upperBidiagonalOf_apply_eq_zero hij (by omega)
    rw [hUij, hUij', zero_add, zero_add, abs_mul]
    congr 1
    simp [upperBidiagonalOf, Fin.ext_iff, show (i : ℕ) - 1 = j by omega]
  · have hUi'j : upperBidiagonalOf α c N ⟨i - 1, by omega⟩ j = 0 :=
      upperBidiagonalOf_apply_eq_zero (by simp; omega) (by simp; omega)
    have hUi'j' : upperBidiagonalOf (fun i => |α i|) (fun i => |c i|) N ⟨i - 1, by omega⟩ j = 0 :=
      upperBidiagonalOf_apply_eq_zero (by simp; omega) (by simp; omega)
    rw [hUi'j, hUi'j', mul_zero, mul_zero, add_zero, add_zero]
    simp only [upperBidiagonalOf, Matrix.of_apply]
    split_ifs <;> simp

/-- **[higham2002accuracy] Theorem 9.14, the factorization half**, [quarteroni2000numerical]
§3.7.1: when the computed pivots are positive and the products `β̂_{i+1} c_i` nonnegative — the
sign pattern of a symmetric positive definite tridiagonal matrix (`b = c`) and of a tridiagonal
M-matrix (`b, c ≤ 0`) — the backward error of the Thomas factorization is small relative to `A`
itself: `|ΔA| ≤ (u / (1 - 2u)) |A|`. Higham's "if `u` is sufficiently small" is what makes the
computed pivots positive; here their positivity is the hypothesis. -/
theorem exists_roundsThomas_mul_eq_add_of_diag_pos (hu : 2 * m.u < 1)
    (h : RoundsThomas m a b c α β) (hα : ∀ i, 0 < α i) (hbc : ∀ i, 0 ≤ β (i + 1) * c i) (N : ℕ) :
    ∃ ΔA : Matrix (Fin N) (Fin N) K,
      ΔA.abs ≤ₑ (m.u / (1 - 2 * m.u)) • (Matrix.tridiagonalOfNat a b c N).abs ∧
        lowerBidiagonalOf β N * upperBidiagonalOf α c N = Matrix.tridiagonalOfNat a b c N + ΔA := by
  have hu1 : m.u < 1 := by linarith [m.u_nonneg]
  obtain ⟨ΔA, hΔ, hLU⟩ := exists_roundsThomas_mul_eq_add hu1 h (fun i => (hα i).ne') N
  refine ⟨ΔA, ?_, hLU⟩
  have h2 : 2 * (((1 : ℕ) : K) * m.u) < 1 := by simpa using hu
  have := gamma_div_one_sub_gamma m.u_nonneg h2
  simp only [Nat.cast_one, one_mul] at this
  rw [← this]
  exact abs_entrywiseLE_of_abs_mul_eq (gamma_nonneg m.u_nonneg (by simpa using hu1))
    (gamma_lt_one m.u_nonneg h2) hΔ hLU (abs_lowerBidiagonalOf_mul_upperBidiagonalOf hα hbc N)

end Thomas

end FloatingPoint
