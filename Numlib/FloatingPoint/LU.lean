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
  M-matrix;
* `FloatingPoint.roundsLU_exact_iff`: at the exact model (`RoundingModel.exact`) the computed
  factors are the Doolittle factors `Matrix.luLower A`, `Matrix.luUpper A`, junk division included —
  the route from the rounding bridge of an LU program to its exact specification;
* `FloatingPoint.exists_add_mulVec_eq_of_lu_errors`: the combination step of [higham2002accuracy]
  Theorem 9.4, for any substitution relations with an entrywise backward error; its instances are
  `FloatingPoint.exists_roundsLU_solve_eq` and `FloatingPoint.exists_roundsLU_solveDot_eq`, the
  rigorous form of [golub2013matrix] Theorem 3.3.2 for the inner-product substitutions of
  `Numlib/FloatingPoint/Substitution`;
* `FloatingPoint.linfty_opNorm_le_of_abs_le_smul_abs_mul_abs`: `‖ΔA‖_∞ ≤ n² γ c_L c_U` from an
  entrywise bound `|ΔA| ≤ γ |L| |U|` and entry bounds on the factors ([golub2013matrix] (3.4.9),
  where the computed multipliers are only bounded by `1 + u`);
* `FloatingPoint.RoundsLDL`, the `L D Lᵀ` recurrence of [golub2013matrix] Algorithm 4.1.1 with the
  products `v_k = fl(l_jk d_k)` rounded once and reused down column `j`:
  `FloatingPoint.exists_roundsLDL_mul_eq_add` (`L̂ D̂ L̂ᵀ = A + ΔA`,
  `|ΔA| ≤ γ_{n+1} |L̂| |D̂| |L̂ᵀ|`) and `FloatingPoint.exists_roundsLDL_solve_eq` (`γ_{3n+2}`, the
  rigorous [golub2013matrix] (4.1.4));
* `FloatingPoint.RoundsCholeskyDiv`, Cholesky in the operation order of [golub2013matrix]
  Algorithm 4.2.1 (the whole column, diagonal included, divided by the rounded square root of the
  pivot): `FloatingPoint.exists_roundsCholeskyDiv_mul_transpose_eq_add` (`γ_{n+3}`: the diagonal
  `fl(t / fl(√t))` carries four roundings in `ĝ_jj²`),
  `FloatingPoint.exists_roundsCholeskyDiv_add_mulVec_eq` (`γ_{3n+3}`) and
  `FloatingPoint.l2_opNorm_le_of_roundsCholeskyDiv`,
  `‖E‖₂ ≤ n γ_{3n+3} ‖A‖₂ / (1 - n γ_{n+3})`, the rigorous form of Wilkinson's `c_n u ‖A‖₂`.

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
  upper : ∀ i j, i ≤ j → ∃ o : List n, o.Nodup ∧ (∀ r, r ∈ o ↔ r < i) ∧
    RoundsRunningDiff m o (L i) (fun r => U r j) (A i j) (U i j)
  /-- The entries of `L`: `l_ij = (a_ij - ∑_{r < j} l_ir u_rj) / u_jj`, by running differences
  and one rounded division. -/
  lower : ∀ i j, j < i → ∃ (o : List n) (t : K), o.Nodup ∧ (∀ r, r ∈ o ↔ r < j) ∧
    RoundsRunningDiff m o (L i) (fun r => U r j) (A i j) t ∧ m.Rounds (t / U j j) (L i j)

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
`l_ir u_rj`, `r ≤ min i j`. Only the pivots that are divisors must be nonzero, those `u_jj` with
some row `i > j` below them: the last pivot divides nothing. -/
theorem RoundsLU.abs_mul_sub_apply_le (hu : m.u < 1) (hcard : (Fintype.card n : K) * m.u < 1)
    (h : RoundsLU m A L U) (hd : ∀ j i, j < i → U j j ≠ 0) (i j : n) :
    |(L * U) i j - A i j| ≤ gamma m.u (Fintype.card n) * (L.abs * U.abs) i j := by
  have hγ := gamma_nonneg m.u_nonneg hcard
  rw [h.isLU_mul.apply_eq_sum i j, h.abs_mul_abs_apply i j]
  rcases le_or_gt i j with hij | hji
  · -- the entry `u_ij`
    obtain ⟨o, hnd, ho, p, hp, ht⟩ := h.upper i j hij
    beta_reduce at hp
    have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
    have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
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
    obtain ⟨o, t, hnd, ho, ht, hx⟩ := h.lower i j hji
    have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
    have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
    have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard
    obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_rounds_sub_dot_div_eq hu hnd (hd j i hji) ht hx hlu
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
The pivots `û_jj` that are divisors, those with some row `i > j` below them, must be nonzero,
since the model rounds `t / û_jj` with the junk value `t / 0 = 0`; the last pivot divides nothing
and may vanish. -/
theorem exists_roundsLU_mul_eq_add (hu : m.u < 1) (hcard : (Fintype.card n : K) * m.u < 1)
    (h : RoundsLU m A L U) (hd : ∀ j i, j < i → U j j ≠ 0) :
    ∃ ΔA : Matrix n n K, ΔA.abs ≤ₑ gamma m.u (Fintype.card n) • (L.abs * U.abs) ∧
      L * U = A + ΔA :=
  ⟨L * U - A, fun i j => h.abs_mul_sub_apply_le hu hcard hd i j, by abel⟩

/-! ### The exact model -/

section Exact

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The lower factor read off the packed recurrence, below the diagonal. -/
private theorem luLower_apply_of_lt (A : Matrix n n K) {i j : n} (h : j < i) :
    A.luLower i j = A.luPacked i j := by
  simp [Matrix.luLower, h]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The upper factor read off the packed recurrence, on and above the diagonal. -/
private theorem luUpper_apply_of_le (A : Matrix n n K) {i j : n} (h : i ≤ j) :
    A.luUpper i j = A.luPacked i j := by
  simp [Matrix.luUpper, h]

/-- **Exact-model characterization of the computed LU factors**: at the exact model the relation
`FloatingPoint.RoundsLU` pins the factors to the Doolittle recurrence, `L = Matrix.luLower A` and
`U = Matrix.luUpper A`, with no hypothesis on `A` (both sides divide by a zero pivot with the same
junk value). Every exact run of an LU algorithm whose rounding bridge lands in `RoundsLU` is
therefore `(luLower A, luUpper A)`, and `Matrix.isLU_luLower_luUpper` is its exact
specification. -/
theorem roundsLU_exact_iff {A L U : Matrix n n K} :
    RoundsLU (RoundingModel.exact K) A L U ↔ L = A.luLower ∧ U = A.luUpper := by
  constructor
  · intro h
    -- the recurrences satisfied by the factors
    have hU : ∀ i j, i ≤ j → U i j = A i j - ∑ r ∈ univ.filter (· < i), L i r * U r j := by
      intro i j hij
      obtain ⟨o, hnd, ho, ht⟩ := h.upper i j hij
      rw [ht.eq_of_exact hnd, toFinset_eq_filter_lt_of_forall_mem_iff ho]
    have hL : ∀ i j, j < i →
        L i j = (A i j - ∑ r ∈ univ.filter (· < j), L i r * U r j) / U j j := by
      intro i j hij
      obtain ⟨o, t, hnd, ho, ht, hx⟩ := h.lower i j hij
      rw [RoundingModel.exact_rounds_iff] at hx
      rw [hx, ht.eq_of_exact hnd, toFinset_eq_filter_lt_of_forall_mem_iff ho]
    -- the packed recurrence agrees with the factors, by induction along `min i j`
    have key : ∀ k i j, min i j = k →
        (i ≤ j → A.luPacked i j = U i j) ∧ (j < i → A.luPacked i j = L i j) := by
      intro k
      induction k using WellFoundedLT.induction with
      | ind k ih =>
      have hU' : ∀ i j, min i j = k → i ≤ j → A.luPacked i j = U i j := by
        intro i j hk hij
        rw [Matrix.luPacked_of_le A hij, hU i j hij]
        congr 1
        refine Finset.sum_congr rfl fun r hr => ?_
        have hr' := (mem_filter.1 hr).2
        have hrk : r < k := by rw [← hk, min_eq_left hij]; exact hr'
        rw [(ih r hrk i r (min_eq_right hr'.le)).2 hr',
          (ih r hrk r j (min_eq_left (hr'.le.trans hij))).1 (hr'.le.trans hij)]
      refine fun i j hk => ⟨hU' i j hk, fun hij => ?_⟩
      have hjk : j = k := (min_eq_right hij.le).symm.trans hk
      rw [Matrix.luPacked_of_lt A hij, hU' j j (by rw [min_self]; exact hjk) le_rfl, hL i j hij]
      congr 2
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' := (mem_filter.1 hr).2
      have hrk : r < k := hjk ▸ hr'
      rw [(ih r hrk i r (min_eq_right (hr'.trans hij).le)).2 (hr'.trans hij),
        (ih r hrk r j (min_eq_left hr'.le)).1 hr'.le]
    refine ⟨Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · simp only [Matrix.luLower, Matrix.of_apply]
      split_ifs with hij hij'
      · exact ((key _ i j rfl).2 hij).symm
      · subst hij'
        exact h.lower_diag i
      · exact h.lower_apply_eq_zero i j (lt_of_le_of_ne (not_lt.1 hij) hij')
    · simp only [Matrix.luUpper, Matrix.of_apply]
      split_ifs with hij
      · exact ((key _ i j rfl).1 hij).symm
      · exact h.upper_apply_eq_zero i j (not_le.1 hij)
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_,
      fun i j hij => ?_⟩
    · simp [Matrix.luLower, hij.not_gt, hij.ne]
    · simp [Matrix.luLower]
    · simp [Matrix.luUpper, not_le.2 hij]
    · refine ⟨(univ.filter (· < i)).toList, Finset.nodup_toList _, fun r => by simp, ?_⟩
      rw [roundsRunningDiff_exact_iff, ← List.sum_toFinset _ (Finset.nodup_toList _),
        Finset.toList_toFinset, luUpper_apply_of_le A hij, Matrix.luPacked_of_le A hij]
      congr 1
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' := (mem_filter.1 hr).2
      rw [luLower_apply_of_lt A hr', luUpper_apply_of_le A (hr'.le.trans hij)]
    · refine ⟨(univ.filter (· < j)).toList,
        A i j - ∑ r ∈ (univ.filter (· < j)).toList.toFinset, A.luLower i r * A.luUpper r j,
        Finset.nodup_toList _, fun r => by simp,
        roundsRunningDiff_exact_iff.2 (by rw [List.sum_toFinset _ (Finset.nodup_toList _)]), ?_⟩
      rw [RoundingModel.exact_rounds_iff, Finset.toList_toFinset, luLower_apply_of_lt A hij,
        Matrix.luPacked_of_lt A hij, luUpper_apply_of_le A le_rfl]
      congr 2
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' := (mem_filter.1 hr).2
      rw [luLower_apply_of_lt A (hr'.trans hij), luUpper_apply_of_le A hr'.le]

end Exact

/-! ### The solve -/

omit [LinearOrder n] in
/-- **The combination step of [higham2002accuracy] Theorem 9.4**: if `L U = A + ΔA₁` with
`|ΔA₁| ≤ γ_A |L| |U|`, `(L + ΔL) y = b` with `|ΔL| ≤ γ_L |L|` and `(U + ΔU) x = y` with
`|ΔU| ≤ γ_U |U|`, then `(A + ΔA) x = b` with `|ΔA| ≤ (γ_A + (1 + γ_L)(1 + γ_U) - 1) |L| |U|` — for
one constant `γ` this is `(3γ + γ²) |L| |U|`. Any pair of substitution relations with an entrywise
backward error can use it. -/
theorem exists_add_mulVec_eq_of_lu_errors {A L U ΔA₁ ΔL ΔU : Matrix n n K} {γA γL γU : K}
    (hγL : 0 ≤ γL) (hLU : L * U = A + ΔA₁) (hA : ΔA₁.abs ≤ₑ γA • (L.abs * U.abs))
    (hL : ΔL.abs ≤ₑ γL • L.abs) (hU : ΔU.abs ≤ₑ γU • U.abs) {b y x : n → K}
    (hy : (L + ΔL) *ᵥ y = b) (hx : (U + ΔU) *ᵥ x = y) :
    ∃ ΔA : Matrix n n K,
      ΔA.abs ≤ₑ (γA + ((1 + γL) * (1 + γU) - 1)) • (L.abs * U.abs) ∧ (A + ΔA) *ᵥ x = b := by
  refine ⟨ΔA₁ + ((L + ΔL) * (U + ΔU) - L * U), ?_, ?_⟩
  · refine (Matrix.abs_add_entrywiseLE _ _).trans ?_
    rw [add_smul]
    exact hA.add (Matrix.abs_add_mul_add_sub_mul_entrywiseLE hγL Matrix.EntrywiseLE.rfl hL
      Matrix.EntrywiseLE.rfl hU)
  · have : A + (ΔA₁ + ((L + ΔL) * (U + ΔU) - L * U)) = (L + ΔL) * (U + ΔU) := by
      rw [hLU]
      abel
    rw [this, ← Matrix.mulVec_mulVec, hx, hy]

omit [Fintype n] [LinearOrder n] in
/-- A bound `c P` with `P` entrywise nonnegative is weakened to `d P` for `c ≤ d`. -/
private theorem entrywiseLE_smul_of_le {B P : Matrix n n K} {c d : K} (hB : B ≤ₑ c • P)
    (hcd : c ≤ d) (hP : P.EntrywiseNonneg) : B ≤ₑ d • P := fun i j => by
  refine (hB i j).trans ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcd (hP.apply i j)

/-- `n u < 1` from `3 n u < 1`. -/
private theorem card_mul_lt_one_of_three_mul {u : K} (hu : 0 ≤ u) {k : ℕ}
    (h : ((3 * k : ℕ) : K) * u < 1) : (k : K) * u < 1 := by
  have : (k : K) * u ≤ ((3 * k : ℕ) : K) * u := by
    push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg (α := K) k) hu]
  linarith

/-- [higham2002accuracy] Theorem 9.4 for any triangular solves with backward error `γ_n`. -/
private theorem exists_roundsLU_solve_eq_of_errors (hu : m.u < 1)
    (hcard : ((3 * Fintype.card n : ℕ) : K) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) {ΔL ΔU : Matrix n n K}
    (hΔL : ∀ i j, |ΔL i j| ≤ gamma m.u (Fintype.card n) * |L i j|)
    (hΔU : ∀ i j, |ΔU i j| ≤ gamma m.u (Fintype.card n) * |U i j|) {b y x : n → K}
    (hy : (L + ΔL) *ᵥ y = b) (hx : (U + ΔU) *ᵥ x = y) :
    ∃ ΔA : Matrix n n K, ΔA.abs ≤ₑ gamma m.u (3 * Fintype.card n) • (L.abs * U.abs) ∧
      (A + ΔA) *ᵥ x = b := by
  have hcard' := card_mul_lt_one_of_three_mul m.u_nonneg hcard
  have hγ := gamma_nonneg m.u_nonneg hcard'
  obtain ⟨ΔA₁, hΔA₁, hLU⟩ := exists_roundsLU_mul_eq_add hu hcard' h fun j _ _ => hd j
  obtain ⟨ΔA, hΔA, hAx⟩ :=
    exists_add_mulVec_eq_of_lu_errors (γU := gamma m.u (Fintype.card n)) hγ hLU hΔA₁ hΔL hΔU hy hx
  refine ⟨ΔA, entrywiseLE_smul_of_le hΔA ?_
    ((Matrix.entrywiseNonneg_abs L).mul (Matrix.entrywiseNonneg_abs U)), hAx⟩
  have h3 := three_mul_gamma_add_sq_le m.u_nonneg hcard
  have : gamma m.u (Fintype.card n) +
      ((1 + gamma m.u (Fintype.card n)) * (1 + gamma m.u (Fintype.card n)) - 1) =
      3 * gamma m.u (Fintype.card n) + gamma m.u (Fintype.card n) ^ 2 := by ring
  rw [this]
  exact h3

/-- **[higham2002accuracy] Theorem 9.4**: factoring `A = L̂ Û` and solving the two triangular
systems by substitution yields a computed `x̂` with `(A + ΔA) x̂ = b`, `|ΔA| ≤ γ_{3n} |L̂| |Û|`.
This is the rigorous form of [quarteroni2000numerical] (3.64), whose `n u (3|A| + 5|L̂||Û|) +
O(u²)` is the first-order form of Golub and Van Loan. Unlike the factorization alone
(`FloatingPoint.exists_roundsLU_mul_eq_add`), back substitution divides by every pivot, so all of
them must be nonzero. -/
theorem exists_roundsLU_solve_eq (hu : m.u < 1) (hcard : ((3 * Fintype.card n : ℕ) : K) * m.u < 1)
    (h : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0) {b y x : n → K}
    (hy : RoundsForwardSubst m L b y) (hx : RoundsBackSubst m U y x) :
    ∃ ΔA : Matrix n n K, ΔA.abs ≤ₑ gamma m.u (3 * Fintype.card n) • (L.abs * U.abs) ∧
      (A + ΔA) *ᵥ x = b := by
  have hcard' := card_mul_lt_one_of_three_mul m.u_nonneg hcard
  obtain ⟨ΔL, hΔL, hyL⟩ := exists_roundsForwardSubst_eq hu hcard'
    h.isLU_mul.isUnitLowerTriangular.isLowerTriangular
    (fun i => by rw [h.lower_diag]; exact one_ne_zero) hy
  obtain ⟨ΔU, hΔU, hxU⟩ := exists_roundsBackSubst_eq hu hcard' h.isLU_mul.isUpperTriangular hd hx
  exact exists_roundsLU_solve_eq_of_errors hu hcard h hd hΔL hΔU hyL hxU

/-- **[higham2002accuracy] Theorem 9.4 for the inner-product substitutions**, the rigorous form of
[golub2013matrix] Theorem 3.3.2 (whose triangular solves are Algorithms 3.1.1–3.1.2): factoring
`A = L̂ Û` and solving the two triangular systems by `FloatingPoint.RoundsForwardSubstDot` and
`FloatingPoint.RoundsBackSubstDot` yields `(A + ΔA) x̂ = b` with `|ΔA| ≤ γ_{3n} |L̂| |Û|`. -/
theorem exists_roundsLU_solveDot_eq (hu : m.u < 1)
    (hcard : ((3 * Fintype.card n : ℕ) : K) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) {b y x : n → K} (hy : RoundsForwardSubstDot m L b y)
    (hx : RoundsBackSubstDot m U y x) :
    ∃ ΔA : Matrix n n K, ΔA.abs ≤ₑ gamma m.u (3 * Fintype.card n) • (L.abs * U.abs) ∧
      (A + ΔA) *ᵥ x = b := by
  have hcard' := card_mul_lt_one_of_three_mul m.u_nonneg hcard
  obtain ⟨ΔL, hΔL, hyL⟩ := exists_roundsForwardSubstDot_eq hu hcard'
    h.isLU_mul.isUnitLowerTriangular.isLowerTriangular
    (fun i => by rw [h.lower_diag]; exact one_ne_zero) hy
  obtain ⟨ΔU, hΔU, hxU⟩ :=
    exists_roundsBackSubstDot_eq hu hcard' h.isLU_mul.isUpperTriangular hd hx
  exact exists_roundsLU_solve_eq_of_errors hu hcard h hd hΔL hΔU hyL hxU

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

variable {m : RoundingModel K} {A L U : Matrix n n K}

/-- **[quarteroni2000numerical] (3.41)**, [higham2002accuracy] (9.8): when the computed LU
factors are entrywise nonnegative, the backward error is small relative to `A` itself,
`|ΔA| ≤ (n u / (1 - 2 n u)) |A|`, since then `|L̂| |Û| = |L̂ Û| = |A + ΔA|`. -/
theorem abs_le_of_roundsLU_of_entrywiseNonneg (hu : m.u < 1)
    (hcard : 2 * ((Fintype.card n : K) * m.u) < 1) (h : RoundsLU m A L U)
    (hd : ∀ j i, j < i → U j j ≠ 0) (hL : L.EntrywiseNonneg) (hU : U.EntrywiseNonneg) :
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

/-- **The normwise consequence of an entrywise factor bound**: if `|ΔA| ≤ γ |L| |U|` entrywise and
the entries of the factors are bounded, `|l_ij| ≤ c_L` and `|u_ij| ≤ c_U`, then
`‖ΔA‖_∞ ≤ n² γ c_L c_U`, every row sum of `|L| |U|` being at most `n · n · c_L c_U`.
`FloatingPoint.linfty_opNorm_le_of_roundsLU_solve` is the case `c_L = 1`, `c_U = ρ max |a_ij|`;
[golub2013matrix] (3.4.9) needs `c_L = 1 + u`, the bound the relational model gives on the
computed multipliers of partial pivoting. -/
theorem linfty_opNorm_le_of_abs_le_smul_abs_mul_abs {ΔA L U : Matrix n n ℝ} {γ cL cU : ℝ}
    (hγ : 0 ≤ γ) (hΔ : ΔA.abs ≤ₑ γ • (L.abs * U.abs)) (hL : ∀ i j, |L i j| ≤ cL)
    (hU : ∀ i j, |U i j| ≤ cU) :
    ‖ΔA‖ ≤ (Fintype.card n : ℝ) ^ 2 * γ * cL * cU := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · rw [Subsingleton.elim ΔA 0, norm_zero, Fintype.card_eq_zero]
    simp
  have hcL : 0 ≤ cL := (abs_nonneg _).trans (hL i₀ i₀)
  have hcU : 0 ≤ cU := (abs_nonneg _).trans (hU i₀ i₀)
  -- the row sums of `|L| |U|`
  have hrow : ∀ i, ∑ j, |(L.abs * U.abs) i j| ≤ (Fintype.card n : ℝ) ^ 2 * (cL * cU) := by
    intro i
    have hnn : ∀ j, 0 ≤ (L.abs * U.abs) i j := fun j =>
      ((Matrix.entrywiseNonneg_abs L).mul (Matrix.entrywiseNonneg_abs U)).apply i j
    calc ∑ j, |(L.abs * U.abs) i j| = ∑ j, ∑ r, |L i r| * |U r j| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_of_nonneg (hnn j), Matrix.mul_apply]
          rfl
      _ ≤ ∑ _j : n, ∑ _r : n, cL * cU := by
          gcongr with j _ r
          · exact hL i r
          · exact hU r j
      _ = (Fintype.card n : ℝ) ^ 2 * (cL * cU) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hΔabs : ΔA.abs ≤ₑ γ • (L.abs * U.abs).abs :=
    hΔ.trans (Matrix.EntrywiseLE.smul_of_nonneg hγ fun i j => le_abs_self _)
  calc ‖ΔA‖ ≤ γ * ‖L.abs * U.abs‖ := Matrix.linfty_opNorm_le_mul_of_abs_entrywiseLE hγ hΔabs
    _ ≤ γ * ((Fintype.card n : ℝ) ^ 2 * (cL * cU)) :=
        mul_le_mul_of_nonneg_left
          (Matrix.linfty_opNorm_le_of_forall_sum_le (by positivity) hrow) hγ
    _ = (Fintype.card n : ℝ) ^ 2 * γ * cL * cU := by ring

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
  calc ‖ΔA‖ ≤ (Fintype.card n : ℝ) ^ 2 * gamma m.u (3 * Fintype.card n) * 1 * (ρ * A.supAbs) :=
        linfty_opNorm_le_of_abs_le_smul_abs_mul_abs hγ hΔ hL hU
    _ = (Fintype.card n : ℝ) ^ 2 * gamma m.u (3 * Fintype.card n) * ρ * A.supAbs := by ring
    _ ≤ (Fintype.card n : ℝ) ^ 2 * gamma m.u (3 * Fintype.card n) * ρ * ‖A‖ :=
        mul_le_mul_of_nonneg_left (Matrix.supAbs_le_linfty_opNorm A)
          (mul_nonneg (mul_nonneg (sq_nonneg _) hγ) hρ)

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
  diag : ∀ j, ∃ (o : List n) (t s : K), o.Nodup ∧ (∀ r, r ∈ o ↔ r < j) ∧
    RoundsRunningDiff m o (fun r => R r j) (fun r => R r j) (A j j) t ∧ 0 ≤ s ∧ s * s = t ∧
      m.Rounds s (R j j)
  /-- Above the diagonal: `r_ij = (a_ij - ∑_{r < i} r_ri r_rj) / r_ii`. -/
  offDiag : ∀ i j, i < j → ∃ (o : List n) (t : K), o.Nodup ∧ (∀ r, r ∈ o ↔ r < i) ∧
    RoundsRunningDiff m o (fun r => R r i) (fun r => R r j) (A i j) t ∧
      m.Rounds (t / R i i) (R i j)

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
    obtain ⟨o, t, s, hnd, ho, ⟨p, hp, ht⟩, hs0, hs, hR⟩ := h.diag i
    beta_reduce at hp
    have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
    have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
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
    obtain ⟨o, t, hnd, ho, ht, hx⟩ := h.offDiag i j hlt
    have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
    have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
    have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard'
    obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_rounds_sub_dot_div_eq hu hnd (hd i) ht hx hlu
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

/-! ### Symmetric factorizations in the operation order of [golub2013matrix] -/

section Symmetric

variable {ι : Type*}

/-- **From a perturbed row equation to an entrywise bound**: if
`P (1 + θ₀) = c - ∑_{k ∈ s} f_k (1 + θ_k)` with `|θ₀|` and every `|θ_k|` at most `γ`, then
`|∑_{k ∈ s} f_k + P - c| ≤ γ (∑_{k ∈ s} |f_k| + |P|)`. Every entry of the backward error of a
factorization computed by running differences is of this shape. -/
theorem abs_sum_add_sub_le_of_mul_one_add_eq {s : Finset ι} {f θ : ι → K} {P c θ₀ γ : K}
    (hθ₀ : |θ₀| ≤ γ) (hθ : ∀ k ∈ s, |θ k| ≤ γ)
    (heq : P * (1 + θ₀) = c - ∑ k ∈ s, f k * (1 + θ k)) :
    |∑ k ∈ s, f k + P - c| ≤ γ * (∑ k ∈ s, |f k| + |P|) := by
  have hkey : ∑ k ∈ s, f k + P - c = -(∑ k ∈ s, f k * θ k + P * θ₀) := by
    have hsum : ∑ k ∈ s, f k * θ k = ∑ k ∈ s, f k * (1 + θ k) - ∑ k ∈ s, f k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    linear_combination heq
  rw [hkey, abs_neg, mul_add, Finset.mul_sum]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hθ k hk) (abs_nonneg _)
  · rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hθ₀ (abs_nonneg _)

/-- Two rounding factors multiplied onto a relative perturbation of order `k` give one of order
`k + 2`. -/
private theorem abs_one_add_mul_one_add_mul_one_add_sub_one_le_gamma {u : K} (hu : 0 ≤ u)
    (hu1 : u < 1) {k : ℕ} (h : ((k + 2 : ℕ) : K) * u < 1) {θ δ ε : K} (hθ : |θ| ≤ gamma u k)
    (hδ : |δ| ≤ u) (hε : |ε| ≤ u) : |(1 + θ) * (1 + δ) * (1 + ε) - 1| ≤ gamma u (k + 2) := by
  have h1 : ((k + 1 : ℕ) : K) * u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu).trans_lt h
  have h2 := abs_one_add_mul_one_add_sub_one_le_gamma hu hu1 (k := k + 1) h
    (abs_one_add_mul_one_add_sub_one_le_gamma hu hu1 h1 hθ hδ) hε
  rwa [add_sub_cancel] at h2

/-- The rounding factors of a pivot computed as `fl(t / fl(√t))`, and of the entries divided by
it: `(1 + θ)(1 + δ₁)² / ((1 + δ₂)(1 + δ₃))` is a relative perturbation of order `k + 4` when `θ` is
one of order `k`. -/
private theorem abs_one_add_mul_sq_div_div_sub_one_le_gamma {u : K} (hu : 0 ≤ u) (hu1 : u < 1)
    {k : ℕ} (h : ((k + 4 : ℕ) : K) * u < 1) {θ δ₁ δ₂ δ₃ : K} (hθ : |θ| ≤ gamma u k)
    (hδ₁ : |δ₁| ≤ u) (hδ₂ : |δ₂| ≤ u) (hδ₃ : |δ₃| ≤ u) :
    |(1 + θ) * (1 + δ₁) * (1 + δ₁) / (1 + δ₂) / (1 + δ₃) - 1| ≤ gamma u (k + 4) := by
  have h2 : ((k + 2 : ℕ) : K) * u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu).trans_lt h
  have h3 : ((k + 2 + 1 : ℕ) : K) * u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu).trans_lt h
  have c2 := abs_one_add_mul_one_add_mul_one_add_sub_one_le_gamma hu hu1 h2 hθ hδ₁ hδ₁
  have c3 := abs_one_add_div_one_add_sub_one_le_gamma hu h3 c2 hδ₂
  rw [add_sub_cancel] at c3
  have c4 := abs_one_add_div_one_add_sub_one_le_gamma hu (k := k + 3) h c3 hδ₃
  rwa [add_sub_cancel] at c4

end Symmetric

/-! ### The computed `L D Lᵀ` factorization -/

section LDL

/-- **The `L D Lᵀ` factorization in floating-point arithmetic**, in the operation order of
[golub2013matrix] Algorithm 4.1.1. `RoundsLDL m A L D`: `L` is unit lower triangular, `D` is
diagonal, and there are the vectors `v` of the algorithm, `V j k = fl(l_jk d_k)` for `k < j` (one
per column `j`, reused down the column), such that the pivot `d_j` is the running difference of
`a_jj` and the rounded products `l_jk V j k`, `k < j`, and the entry `l_ij`, `j < i`, is the
running difference of `a_ij` and the rounded products `l_ik V j k`, `k < j`, divided by `d_j` with
one more rounding. The book's matrix–vector products are read as running differences from the
entry of `A`, in any order of the terms, as in `FloatingPoint.RoundsLU`; only the lower triangle
of `A` is read. -/
structure RoundsLDL (m : RoundingModel K) (A L D : Matrix n n K) : Prop where
  /-- `L` vanishes above the diagonal. -/
  lower_apply_eq_zero : ∀ i j, i < j → L i j = 0
  /-- `L` has unit diagonal. -/
  lower_diag : ∀ i, L i i = 1
  /-- `D` is diagonal. -/
  isDiag : D.IsDiag
  /-- The recurrence, with the rounded products `V j k = fl(l_jk d_k)` of the algorithm. -/
  exists_rounds : ∃ V : Matrix n n K, (∀ j k, k < j → m.Rounds (L j k * D k k) (V j k)) ∧
    (∀ j, ∃ o : List n, o.Nodup ∧ (∀ k, k ∈ o ↔ k < j) ∧
      RoundsRunningDiff m o (L j) (V j) (A j j) (D j j)) ∧
    (∀ i j, j < i → ∃ (o : List n) (t : K), o.Nodup ∧ (∀ k, k ∈ o ↔ k < j) ∧
      RoundsRunningDiff m o (L i) (V j) (A i j) t ∧ m.Rounds (t / D j j) (L i j))

variable {m : RoundingModel K} {A L D : Matrix n n K}

/-- The entry `(i, j)` of `|L| |D| |Lᵀ|` for the computed factors is
`∑_{k ≤ min i j} |l_ik| |d_k| |l_jk|`. -/
theorem RoundsLDL.abs_mul_mul_transpose_abs_apply (h : RoundsLDL m A L D) (i j : n) :
    (L.abs * D.abs * Lᵀ.abs) i j =
      ∑ k ∈ univ.filter (· ≤ min i j), |L i k| * |D k k| * |L j k| :=
  Matrix.mul_mul_transpose_apply_of_isDiag (L := L.abs)
    (fun i j hij => by simp [h.lower_apply_eq_zero i j hij])
    (h.isDiag.map (f := (|·|)) abs_zero) i j

/-- **One entry of the backward error of the computed `L D Lᵀ` factors**, on or below the
diagonal: `|(L D Lᵀ)_ij - a_ij| ≤ γ_{n+1} (|L| |D| |Lᵀ|)_ij`. The products `V j k = fl(l_jk d_k)`
cost one rounding more than the products of Gaussian elimination, whence `n + 1`. Only the pivots
that are divisors must be nonzero. -/
theorem RoundsLDL.abs_mul_mul_transpose_sub_apply_le_of_le (hu : m.u < 1)
    (hcard : ((Fintype.card n + 1 : ℕ) : K) * m.u < 1) (h : RoundsLDL m A L D)
    (hd : ∀ j i, j < i → D j j ≠ 0) {i j : n} (hji : j ≤ i) :
    |(L * D * Lᵀ) i j - A i j| ≤
      gamma m.u (Fintype.card n + 1) * (L.abs * D.abs * Lᵀ.abs) i j := by
  have hcard' : (Fintype.card n : K) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard
  obtain ⟨V, hV, hdiag, hoff⟩ := h.exists_rounds
  rw [Matrix.mul_mul_transpose_apply_of_isDiag h.lower_apply_eq_zero h.isDiag,
    h.abs_mul_mul_transpose_abs_apply, min_eq_right hji, Matrix.sum_filter_le_eq_add,
    Matrix.sum_filter_le_eq_add]
  rcases hji.eq_or_lt with hij | hlt
  · -- the diagonal
    rw [← hij]
    obtain ⟨o, hnd, ho, p, hp, ht⟩ := hdiag j
    have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
    have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
    have hl : (o.length : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard'
    have hlu2 : ((o.length + 2 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard
    obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_roundsSumFrom_map_eq hu hnd ht hl
    choose! ε hε hpε using fun k hk => (hp k hk).exists_delta
    choose! η hη hVη using fun k (hk : k ∈ o) => (hV j k ((ho k).1 hk)).exists_delta
    have hmono := gamma_mono m.u_nonneg (show o.length + 2 ≤ Fintype.card n + 1 by omega) hcard
    have hmono0 := gamma_mono m.u_nonneg (show o.length ≤ Fintype.card n + 1 by omega) hcard
    simp only [h.lower_diag, abs_one, mul_one, one_mul]
    rw [← hset]
    have key := abs_sum_add_sub_le_of_mul_one_add_eq (s := o.toFinset)
      (f := fun k => L j k * D k k * L j k) (P := D j j) (c := A j j)
      (θ := fun k => (1 + θ k) * (1 + ε k) * (1 + η k) - 1) (hθ₀.trans hmono0)
      (fun k hk => (abs_one_add_mul_one_add_mul_one_add_sub_one_le_gamma m.u_nonneg hu hlu2
        (hθ k (List.mem_toFinset.1 hk)) (hε k (List.mem_toFinset.1 hk))
        (hη k (List.mem_toFinset.1 hk))).trans hmono) (by
        rw [heq, sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hpε k (List.mem_toFinset.1 hk), hVη k (List.mem_toFinset.1 hk)]
        ring)
    simpa only [abs_mul] using key
  · -- below the diagonal
    obtain ⟨o, t, hnd, ho, ht, hx⟩ := hoff i j hlt
    have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
    have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
    have hlu1 : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard'
    have hlu2 : ((o.length + 1 + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard
    obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ :=
      exists_rounds_sub_dot_div_eq hu hnd (hd j i hlt) ht hx hlu1
    choose! η hη hVη using fun k (hk : k ∈ o) => (hV j k ((ho k).1 hk)).exists_delta
    have hmono := gamma_mono m.u_nonneg (show o.length + 1 + 1 ≤ Fintype.card n + 1 by omega)
      hcard
    have hmono1 := gamma_mono m.u_nonneg (show o.length + 1 ≤ Fintype.card n + 1 by omega) hcard
    simp only [h.lower_diag, abs_one, mul_one]
    rw [← hset]
    have key := abs_sum_add_sub_le_of_mul_one_add_eq (s := o.toFinset)
      (f := fun k => L i k * D k k * L j k) (P := L i j * D j j) (c := A i j)
      (θ := fun k => (1 + θ k) * (1 + η k) - 1) (hθ₀.trans hmono1)
      (fun k hk => (abs_one_add_mul_one_add_sub_one_le_gamma m.u_nonneg hu hlu2
        (hθ k (List.mem_toFinset.1 hk)) (hη k (List.mem_toFinset.1 hk))).trans hmono) (by
        rw [mul_comm (L i j), heq]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hVη k (List.mem_toFinset.1 hk)]
        ring)
    simpa only [abs_mul] using key

/-- **The backward error of the computed `L D Lᵀ` factors** ([golub2013matrix] Algorithm 4.1.1):
for a symmetric `A`, `L̂ D̂ L̂ᵀ = A + ΔA` with `|ΔA| ≤ γ_{n+1} |L̂| |D̂| |L̂ᵀ|` entrywise. The
entries below the diagonal follow from the symmetry of `A` and of `L̂ D̂ L̂ᵀ`; only the pivots that
are divisors must be nonzero. -/
theorem exists_roundsLDL_mul_eq_add (hu : m.u < 1)
    (hcard : ((Fintype.card n + 1 : ℕ) : K) * m.u < 1) (hA : A.IsSymm) (h : RoundsLDL m A L D)
    (hd : ∀ j i, j < i → D j j ≠ 0) :
    ∃ ΔA : Matrix n n K,
      ΔA.abs ≤ₑ gamma m.u (Fintype.card n + 1) • (L.abs * D.abs * Lᵀ.abs) ∧
        L * D * Lᵀ = A + ΔA := by
  refine ⟨L * D * Lᵀ - A, fun i j => ?_, by abel⟩
  simp only [Matrix.abs_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rcases le_or_gt j i with hji | hij
  · exact h.abs_mul_mul_transpose_sub_apply_le_of_le hu hcard hd hji
  · have hS := Matrix.isSymm_mul_mul_transpose_of_isDiag L h.isDiag
    have hS' : (L.abs * D.abs * Lᵀ.abs).IsSymm :=
      Matrix.isSymm_mul_mul_transpose_of_isDiag L.abs (h.isDiag.map (f := (|·|)) abs_zero)
    rw [← hS.apply i j, ← hS'.apply i j, ← hA.apply i j]
    exact h.abs_mul_mul_transpose_sub_apply_le_of_le hu hcard hd hij.le

omit [LinearOrder n] in
/-- **The combination step for three factors** (the `L D Lᵀ` analogue of
`FloatingPoint.exists_add_mulVec_eq_of_lu_errors`): if `L D Lᵀ = A + ΔA₁` with
`|ΔA₁| ≤ γ_A |L| |D| |Lᵀ|`, `(L + ΔL₁) z = b`, `(D + ΔD) y = z` and `(Lᵀ + ΔL₂) x = y` with
`|ΔL₁| ≤ γ₁ |L|`, `|ΔD| ≤ γ₂ |D|` and `|ΔL₂| ≤ γ₃ |Lᵀ|`, then `(A + ΔA) x = b` with
`|ΔA| ≤ (γ_A + (1 + γ₁)(1 + γ₂)(1 + γ₃) - 1) |L| |D| |Lᵀ|`. -/
theorem exists_add_mulVec_eq_of_ldl_errors {A L D ΔA₁ ΔL₁ ΔD ΔL₂ : Matrix n n K}
    {γA γ₁ γ₂ γ₃ : K} (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂) (hLDL : L * D * Lᵀ = A + ΔA₁)
    (hA : ΔA₁.abs ≤ₑ γA • (L.abs * D.abs * Lᵀ.abs)) (hL₁ : ΔL₁.abs ≤ₑ γ₁ • L.abs)
    (hD : ΔD.abs ≤ₑ γ₂ • D.abs) (hL₂ : ΔL₂.abs ≤ₑ γ₃ • Lᵀ.abs) {b z y x : n → K}
    (hz : (L + ΔL₁) *ᵥ z = b) (hy : (D + ΔD) *ᵥ y = z) (hx : (Lᵀ + ΔL₂) *ᵥ x = y) :
    ∃ ΔA : Matrix n n K,
      ΔA.abs ≤ₑ (γA + ((1 + γ₁) * (1 + γ₂) * (1 + γ₃) - 1)) • (L.abs * D.abs * Lᵀ.abs) ∧
        (A + ΔA) *ᵥ x = b := by
  refine ⟨ΔA₁ + ((L + ΔL₁) * (D + ΔD) * (Lᵀ + ΔL₂) - L * D * Lᵀ), ?_, ?_⟩
  · have h₁ := Matrix.abs_add_mul_add_sub_mul_entrywiseLE hγ₁ Matrix.EntrywiseLE.rfl hL₁
      Matrix.EntrywiseLE.rfl hD
    have hc : 0 ≤ (1 + γ₁) * (1 + γ₂) - 1 := by nlinarith
    have h₂ := Matrix.abs_add_mul_add_sub_mul_entrywiseLE hc (Matrix.abs_mul_entrywiseLE L D) h₁
      Matrix.EntrywiseLE.rfl hL₂
    have e₁ : L * D + ((L + ΔL₁) * (D + ΔD) - L * D) = (L + ΔL₁) * (D + ΔD) := by abel
    have e₂ : (1 + ((1 + γ₁) * (1 + γ₂) - 1)) * (1 + γ₃) - 1 =
        (1 + γ₁) * (1 + γ₂) * (1 + γ₃) - 1 := by ring
    rw [e₁, e₂] at h₂
    refine (Matrix.abs_add_entrywiseLE _ _).trans ?_
    rw [add_smul]
    exact hA.add h₂
  · have : A + (ΔA₁ + ((L + ΔL₁) * (D + ΔD) * (Lᵀ + ΔL₂) - L * D * Lᵀ)) =
        (L + ΔL₁) * (D + ΔD) * (Lᵀ + ΔL₂) := by
      rw [hLDL]
      abel
    rw [this, ← Matrix.mulVec_mulVec, hx, ← Matrix.mulVec_mulVec, hy, hz]

/-- The constant of the `L D Lᵀ` solve: `γ_{k+1} + (1 + γ_k)(1 + γ₁)(1 + γ_k) - 1 ≤ γ_{3k+2}`. -/
private theorem gamma_add_one_add_mul_one_add_mul_one_add_sub_one_le {u : K} (hu : 0 ≤ u) {k : ℕ}
    (h : ((3 * k + 2 : ℕ) : K) * u < 1) :
    gamma u (k + 1) + ((1 + gamma u k) * (1 + gamma u 1) * (1 + gamma u k) - 1) ≤
      gamma u (3 * k + 2) := by
  have hle : ∀ j, j ≤ 3 * k + 2 → ((j : ℕ) : K) * u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu).trans_lt h
  have a := gamma_add_gamma_add_mul_le hu (j := k) (k := 1) (hle _ (by omega))
  have b := gamma_add_gamma_add_mul_le hu (j := k + 1) (k := k) (hle _ (by omega))
  have c := gamma_add_gamma_add_mul_le hu (j := k + 1) (k := k + 1 + k) (hle _ (by omega))
  rw [show k + 1 + (k + 1 + k) = 3 * k + 2 by ring] at c
  have gk := gamma_nonneg hu (hle k (by omega))
  have g1 := gamma_nonneg hu (hle 1 (by omega))
  have gk1 := gamma_nonneg hu (hle (k + 1) (by omega))
  have g2k1 := gamma_nonneg hu (hle (k + 1 + k) (by omega))
  have s1 : (1 + gamma u k) * (1 + gamma u 1) ≤ 1 + gamma u (k + 1) := by
    nlinarith
  have s2 : (1 + gamma u k) * (1 + gamma u 1) * (1 + gamma u k) ≤
      (1 + gamma u (k + 1)) * (1 + gamma u k) :=
    mul_le_mul_of_nonneg_right s1 (by linarith)
  nlinarith [mul_nonneg gk1 g2k1]

/-- **[golub2013matrix] (4.1.4), rigorous**: for a symmetric `A`, the solution computed by the
factorization of [golub2013matrix] Algorithm 4.1.1, forward substitution with `L̂`, the diagonal
solve `y_i = fl(z_i / d_i)` and back substitution with `L̂ᵀ` satisfies `(A + E) x̂ = b` with
`|E| ≤ γ_{3n+2} |L̂| |D̂| |L̂ᵀ|`. This implies the book's first-order bound
`n u (2|A| + 4|L̂||D̂||L̂ᵀ|) + O(u²)` for `n ≥ 2`, since `(3n + 2) u ≤ 4 n u`; the book's `2|A|`
term is not needed. -/
theorem exists_roundsLDL_solve_eq (hu : m.u < 1)
    (hcard : ((3 * Fintype.card n + 2 : ℕ) : K) * m.u < 1) (hA : A.IsSymm) (h : RoundsLDL m A L D)
    (hd : ∀ j, D j j ≠ 0) {b z y x : n → K} (hz : RoundsForwardSubst m L b z)
    (hy : ∀ i, m.Rounds (z i / D i i) (y i)) (hx : RoundsBackSubst m Lᵀ y x) :
    ∃ E : Matrix n n K, E.abs ≤ₑ gamma m.u (3 * Fintype.card n + 2) • (L.abs * D.abs * Lᵀ.abs) ∧
      (A + E) *ᵥ x = b := by
  have hle : ∀ j, j ≤ 3 * Fintype.card n + 2 → ((j : ℕ) : K) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard
  have hN := hle (Fintype.card n) (by omega)
  obtain ⟨ΔA₁, hΔA₁, hLDL⟩ :=
    exists_roundsLDL_mul_eq_add hu (hle _ (by omega)) hA h fun j _ _ => hd j
  obtain ⟨ΔL₁, hΔL₁, hzL⟩ := exists_roundsForwardSubst_eq hu hN
    (fun i j hij => h.lower_apply_eq_zero i j (OrderDual.toDual_lt_toDual.1 hij))
    (fun i => by rw [h.lower_diag]; exact one_ne_zero) hz
  obtain ⟨ΔL₂, hΔL₂, hxL⟩ := exists_roundsBackSubst_eq hu hN
    (fun i j hij => by rw [Matrix.transpose_apply]; exact h.lower_apply_eq_zero j i hij)
    (fun i => by rw [Matrix.transpose_apply, h.lower_diag]; exact one_ne_zero) hx
  -- the diagonal solve
  choose δ hδ hyδ using fun i => (hy i).exists_delta
  have h1 : ((0 + 1 : ℕ) : K) * m.u < 1 := by simpa using hu
  have hΔD : (Matrix.diagonal fun i => D i i * ((1 + 0) / (1 + δ i) - 1)).abs ≤ₑ
      gamma m.u 1 • D.abs := by
    intro i j
    simp only [Matrix.abs_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (abs_one_add_div_one_add_sub_one_le_gamma (θ := 0) m.u_nonneg h1 (by simp) (hδ i))
        (abs_nonneg _)
    · rw [abs_zero]
      exact mul_nonneg (gamma_nonneg m.u_nonneg (by simpa using hu)) (abs_nonneg _)
  have hyD : (D + Matrix.diagonal fun i => D i i * ((1 + 0) / (1 + δ i) - 1)) *ᵥ y = z := by
    have hD : D + Matrix.diagonal (fun i => D i i * ((1 + 0) / (1 + δ i) - 1)) =
        Matrix.diagonal fun i => D i i * ((1 + 0) / (1 + δ i)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.diagonal_apply]
      split_ifs with hij
      · subst hij
        ring
      · rw [h.isDiag hij, add_zero]
    ext i
    have hδ1 : (1 : K) + δ i ≠ 0 := by linarith [neg_le_of_abs_le (hδ i)]
    have hdi := hd i
    rw [hD, Matrix.mulVec_diagonal, hyδ i]
    field_simp
    ring
  obtain ⟨E, hE, hAx⟩ := exists_add_mulVec_eq_of_ldl_errors (γ₃ := gamma m.u (Fintype.card n))
    (gamma_nonneg m.u_nonneg hN)
    (gamma_nonneg m.u_nonneg (hle 1 (by omega))) hLDL hΔA₁ hΔL₁ hΔD hΔL₂ hzL hyD hxL
  refine ⟨E, entrywiseLE_smul_of_le hE
    (gamma_add_one_add_mul_one_add_mul_one_add_sub_one_le m.u_nonneg hcard) ?_, hAx⟩
  exact ((Matrix.entrywiseNonneg_abs L).mul (Matrix.entrywiseNonneg_abs D)).mul
    (Matrix.entrywiseNonneg_abs Lᵀ)

end LDL

/-! ### Cholesky in the operation order of [golub2013matrix] Algorithm 4.2.1 -/

section CholeskyDiv

/-- **Cholesky in the operation order of [golub2013matrix] Algorithm 4.2.1** (gaxpy Cholesky: the
column `A(j:n, j)` is updated by running differences and then divided, diagonal included, by the
rounded square root `ŝ_j = fl(√t_j)` of the pivot). `RoundsCholeskyDiv m A G`: `G` is lower
triangular, and there are the pivots `t_j` (the running difference of `a_jj` and the rounded
squares `g_jk²`, `k < j`) and their rounded square roots `ŝ_j`, modelled as one rounding of an exact
root `0 ≤ s`, `s² = t_j`, such that `g_jj = fl(t_j / ŝ_j)` and, for `j < i`, `g_ij = fl(t_ij / ŝ_j)`
with `t_ij` the running difference of `a_ij` and the rounded products `g_ik g_jk`, `k < j`. It
differs from `FloatingPoint.RoundsCholesky` (whose diagonal is `fl(√t)`) exactly in the diagonal:
`fl(t / fl(√t)) = √t (1 + δ₂) / (1 + δ₁)`. Only the lower triangle of `A` is read. -/
structure RoundsCholeskyDiv (m : RoundingModel K) (A G : Matrix n n K) : Prop where
  /-- `G` vanishes above the diagonal. -/
  apply_eq_zero : ∀ i j, i < j → G i j = 0
  /-- The recurrence, with the pivots `t j` and their rounded square roots `sh j`. -/
  exists_rounds : ∃ t sh : n → K,
    (∀ j, ∃ o : List n, o.Nodup ∧ (∀ k, k ∈ o ↔ k < j) ∧
      RoundsRunningDiff m o (G j) (G j) (A j j) (t j)) ∧
    (∀ j, ∃ s, 0 ≤ s ∧ s * s = t j ∧ m.Rounds s (sh j)) ∧
    (∀ j, m.Rounds (t j / sh j) (G j j)) ∧
    (∀ i j, j < i → ∃ (o : List n) (r : K), o.Nodup ∧ (∀ k, k ∈ o ↔ k < j) ∧
      RoundsRunningDiff m o (G i) (G j) (A i j) r ∧ m.Rounds (r / sh j) (G i j))

variable {m : RoundingModel K} {A G : Matrix n n K}

/-- The entry `(i, j)` of `|G| |Gᵀ|` for the computed factor is `∑_{k ≤ min i j} |g_ik| |g_jk|`. -/
theorem RoundsCholeskyDiv.abs_mul_transpose_abs_apply (h : RoundsCholeskyDiv m A G) (i j : n) :
    (G.abs * Gᵀ.abs) i j = ∑ k ∈ univ.filter (· ≤ min i j), |G i k| * |G j k| :=
  have hG : ∀ i j, i < j → G.abs i j = 0 := fun i j hij => by simp [h.apply_eq_zero i j hij]
  Matrix.mul_transpose_apply_of_lower hG hG i j

/-- **One entry of the backward error of Cholesky in the operation order of [golub2013matrix]
Algorithm 4.2.1**, on or below the diagonal: `|(G Gᵀ)_ij - a_ij| ≤ γ_{n+3} (|G| |Gᵀ|)_ij`. The
products `g_ij g_jj` and `g_jj²` carry the rounding of the square root twice and the two divisions
once each, four roundings where Gaussian elimination has one; the terms carry `#{k ≤ j} ≤ n`. The
hypothesis is on the returned diagonal: `g_jj ≠ 0` forces `ŝ_j ≠ 0` and `t_j ≠ 0`. -/
theorem RoundsCholeskyDiv.abs_mul_transpose_sub_apply_le_of_le (hu : m.u < 1)
    (hcard : ((Fintype.card n + 3 : ℕ) : K) * m.u < 1) (h : RoundsCholeskyDiv m A G)
    (hd : ∀ j, G j j ≠ 0) {i j : n} (hji : j ≤ i) :
    |(G * Gᵀ) i j - A i j| ≤ gamma m.u (Fintype.card n + 3) * (G.abs * Gᵀ.abs) i j := by
  have hcard' : (Fintype.card n : K) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard
  obtain ⟨t, sh, hdiagsum, hroot, hdiag, hoff⟩ := h.exists_rounds
  -- the pivot of column `j`
  obtain ⟨s, -, hss, hsh⟩ := hroot j
  obtain ⟨δ₁, hδ₁, hshδ⟩ := hsh.exists_delta
  obtain ⟨δ₂, hδ₂, hGδ⟩ := (hdiag j).exists_delta
  have hsh0 : sh j ≠ 0 := fun h0 => hd j (by rw [hGδ, h0, div_zero, zero_mul])
  have hs0 : s ≠ 0 := fun h0 => hsh0 (by rw [hshδ, h0, zero_mul])
  have hd₁ : (1 : K) + δ₁ ≠ 0 := by linarith [neg_le_of_abs_le hδ₁]
  have hd₂ : (1 : K) + δ₂ ≠ 0 := by linarith [neg_le_of_abs_le hδ₂]
  rw [Matrix.mul_transpose_apply_of_lower h.apply_eq_zero h.apply_eq_zero,
    h.abs_mul_transpose_abs_apply, min_eq_right hji, Matrix.sum_filter_le_eq_add,
    Matrix.sum_filter_le_eq_add]
  -- the row `i` data: a running difference `r` of `a_ij`, then `g_ij = fl(r / ŝ_j)`
  obtain ⟨o, r, δ₃, hnd, ho, hrd, hδ₃, hGr⟩ : ∃ (o : List n) (r δ₃ : K),
      o.Nodup ∧ (∀ k, k ∈ o ↔ k < j) ∧ RoundsRunningDiff m o (G i) (G j) (A i j) r ∧
      |δ₃| ≤ m.u ∧ G i j = r / sh j * (1 + δ₃) := by
    rcases hji.eq_or_lt with hij | hlt
    · rw [← hij]
      obtain ⟨o, hnd, ho, ht⟩ := hdiagsum j
      exact ⟨o, t j, δ₂, hnd, ho, ht, hδ₂, hGδ⟩
    · obtain ⟨o, r, hnd, ho, hr, hx⟩ := hoff i j hlt
      obtain ⟨δ₃, hδ₃, hGr⟩ := hx.exists_delta
      exact ⟨o, r, δ₃, hnd, ho, hr, hδ₃, hGr⟩
  obtain ⟨p, hp, hr⟩ := hrd
  have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
  have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
  have hl : (o.length : K) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard'
  have hlu1 : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard'
  have hlu4 : ((o.length + 4 : ℕ) : K) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard
  have hd₃ : (1 : K) + δ₃ ≠ 0 := by linarith [neg_le_of_abs_le hδ₃]
  obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_roundsSumFrom_map_eq hu hnd hr hl
  choose! ε hε hpε using fun k hk => (hp k hk).exists_delta
  -- `g_ij g_jj = r (1 + δ₂)(1 + δ₃) / (1 + δ₁)²`, since `ŝ_j² = t_j (1 + δ₁)²`
  have hprod : G i j * G j j = r / sh j * (1 + δ₃) * (t j / sh j * (1 + δ₂)) := by
    rw [← hGr, ← hGδ]
  have hr' : G i j * G j j * ((1 + θ₀) * (1 + δ₁) * (1 + δ₁) / (1 + δ₂) / (1 + δ₃)) =
      r * (1 + θ₀) := by
    rw [hprod, hshδ, ← hss]
    field_simp
  have hmono4 := gamma_mono m.u_nonneg (show o.length + 4 ≤ Fintype.card n + 3 by omega) hcard
  have hmono1 := gamma_mono m.u_nonneg (show o.length + 1 ≤ Fintype.card n + 3 by omega) hcard
  rw [← hset]
  have key := abs_sum_add_sub_le_of_mul_one_add_eq (s := o.toFinset)
    (f := fun k => G i k * G j k) (P := G i j * G j j) (c := A i j)
    (θ := fun k => (1 + θ k) * (1 + ε k) - 1)
    ((abs_one_add_mul_sq_div_div_sub_one_le_gamma m.u_nonneg hu hlu4 hθ₀ hδ₁ hδ₂ hδ₃).trans
      hmono4)
    (fun k hk => (abs_one_add_mul_one_add_sub_one_le_gamma m.u_nonneg hu hlu1
      (hθ k (List.mem_toFinset.1 hk)) (hε k (List.mem_toFinset.1 hk))).trans hmono1) (by
      rw [add_sub_cancel, hr', heq, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hpε k (List.mem_toFinset.1 hk)]
      ring)
  simpa only [abs_mul] using key

/-- **The backward error of Cholesky in the operation order of [golub2013matrix] Algorithm 4.2.1**:
for a symmetric `A`, the computed factor satisfies `Ĝ Ĝᵀ = A + ΔA` with
`|ΔA| ≤ γ_{n+3} |Ĝ| |Ĝᵀ|` entrywise. The constant is two more than the `γ_{n+1}` of
`FloatingPoint.exists_roundsCholesky_eq_add`, whose diagonal is `fl(√t)`: here
`ĝ_jj² = t_j (1 + δ₂)² / (1 + δ₁)²` carries four roundings, and for `n = 1`, `δ₁ = -u`, `δ₂ = u` the
bound `γ_3` is already exceeded. The diagonal of `Ĝ` must be nonzero. -/
theorem exists_roundsCholeskyDiv_mul_transpose_eq_add (hu : m.u < 1)
    (hcard : ((Fintype.card n + 3 : ℕ) : K) * m.u < 1) (hA : A.IsSymm)
    (h : RoundsCholeskyDiv m A G) (hd : ∀ j, G j j ≠ 0) :
    ∃ ΔA : Matrix n n K, ΔA.abs ≤ₑ gamma m.u (Fintype.card n + 3) • (G.abs * Gᵀ.abs) ∧
      G * Gᵀ = A + ΔA := by
  refine ⟨G * Gᵀ - A, fun i j => ?_, by abel⟩
  simp only [Matrix.abs_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rcases le_or_gt j i with hji | hij
  · exact h.abs_mul_transpose_sub_apply_le_of_le hu hcard hd hji
  · have hS' : (G.abs * Gᵀ.abs).IsSymm := Matrix.isSymm_mul_transpose_self G.abs
    rw [← (Matrix.isSymm_mul_transpose_self G).apply i j, ← hS'.apply i j, ← hA.apply i j]
    exact h.abs_mul_transpose_sub_apply_le_of_le hu hcard hd hij.le

/-- The constant of the Cholesky solve: `γ_{k+3} + (1 + γ_k)(1 + γ_k) - 1 ≤ γ_{3k+3}`. -/
private theorem gamma_add_three_add_one_add_mul_one_add_sub_one_le {u : K} (hu : 0 ≤ u) {k : ℕ}
    (h : ((3 * k + 3 : ℕ) : K) * u < 1) :
    gamma u (k + 3) + ((1 + gamma u k) * (1 + gamma u k) - 1) ≤ gamma u (3 * k + 3) := by
  have hle : ∀ j, j ≤ 3 * k + 3 → ((j : ℕ) : K) * u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu).trans_lt h
  have b := gamma_add_gamma_add_mul_le hu (j := k) (k := k) (hle _ (by omega))
  have c := gamma_add_gamma_add_mul_le hu (j := k + 3) (k := k + k) (hle _ (by omega))
  rw [show k + 3 + (k + k) = 3 * k + 3 by ring] at c
  have g3 := gamma_nonneg hu (hle (k + 3) (by omega))
  have g2k := gamma_nonneg hu (hle (k + k) (by omega))
  nlinarith [mul_nonneg g3 g2k]

/-- **The Cholesky solve in the operation order of [golub2013matrix]** (Algorithm 4.2.1, then
forward substitution with `Ĝ` and back substitution with `Ĝᵀ`; [higham2002accuracy] Theorem 10.4
for this order): for a symmetric `A`, `(A + E) x̂ = b` with `|E| ≤ γ_{3n+3} |Ĝ| |Ĝᵀ|`. From
`FloatingPoint.exists_roundsCholeskyDiv_mul_transpose_eq_add`, the substitution theorems and
`FloatingPoint.exists_add_mulVec_eq_of_lu_errors` with `L = Ĝ`, `U = Ĝᵀ`. -/
theorem exists_roundsCholeskyDiv_add_mulVec_eq (hu : m.u < 1)
    (hcard : ((3 * Fintype.card n + 3 : ℕ) : K) * m.u < 1) (hA : A.IsSymm)
    (h : RoundsCholeskyDiv m A G) (hd : ∀ j, G j j ≠ 0) {b y x : n → K}
    (hy : RoundsForwardSubst m G b y) (hx : RoundsBackSubst m Gᵀ y x) :
    ∃ E : Matrix n n K, E.abs ≤ₑ gamma m.u (3 * Fintype.card n + 3) • (G.abs * Gᵀ.abs) ∧
      (A + E) *ᵥ x = b := by
  have hle : ∀ j, j ≤ 3 * Fintype.card n + 3 → ((j : ℕ) : K) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard
  have hN := hle (Fintype.card n) (by omega)
  obtain ⟨ΔA₁, hΔA₁, hGG⟩ :=
    exists_roundsCholeskyDiv_mul_transpose_eq_add hu (hle _ (by omega)) hA h hd
  obtain ⟨ΔL, hΔL, hyL⟩ := exists_roundsForwardSubst_eq hu hN
    (fun i j hij => h.apply_eq_zero i j (OrderDual.toDual_lt_toDual.1 hij)) hd hy
  obtain ⟨ΔU, hΔU, hxU⟩ := exists_roundsBackSubst_eq hu hN
    (fun i j hij => by rw [Matrix.transpose_apply]; exact h.apply_eq_zero j i hij)
    (fun i => by rw [Matrix.transpose_apply]; exact hd i) hx
  obtain ⟨E, hE, hAx⟩ := exists_add_mulVec_eq_of_lu_errors (γU := gamma m.u (Fintype.card n))
    (gamma_nonneg m.u_nonneg hN) hGG
    hΔA₁ hΔL hΔU hyL hxU
  exact ⟨E, entrywiseLE_smul_of_le hE
    (gamma_add_three_add_one_add_mul_one_add_sub_one_le m.u_nonneg hcard)
    ((Matrix.entrywiseNonneg_abs G).mul (Matrix.entrywiseNonneg_abs Gᵀ)), hAx⟩

end CholeskyDiv

/-! ### Wilkinson's normwise bound for the Cholesky solve -/

section Wilkinson

open Matrix (lpOpNorm)

open scoped Matrix.Norms.Frobenius in
/-- **The normwise size of `|G| |Gᵀ|`**: if `|E| ≤ γ |G| |Gᵀ|` entrywise, then
`‖E‖₂ ≤ γ n ‖G‖₂²`, through `‖E‖₂ ≤ ‖E‖_F ≤ γ ‖|G|‖_F ‖|Gᵀ|‖_F = γ ‖G‖_F² ≤ γ n ‖G‖₂²`. -/
theorem lpOpNorm_two_le_of_abs_le_smul_abs_mul_abs_transpose {E G : Matrix n n ℝ} {γ : ℝ}
    (hγ : 0 ≤ γ) (hE : E.abs ≤ₑ γ • (G.abs * Gᵀ.abs)) :
    lpOpNorm 2 E ≤ γ * Fintype.card n * lpOpNorm 2 G ^ 2 := by
  have hF : ‖E‖ ≤ γ * ‖G.abs * Gᵀ.abs‖ :=
    Matrix.frobenius_norm_le_of_forall_abs_le hγ fun i j => by
    have := hE i j
    simp only [Matrix.abs_apply, Matrix.smul_apply, smul_eq_mul] at this
    rwa [abs_of_nonneg
      (((Matrix.entrywiseNonneg_abs G).mul (Matrix.entrywiseNonneg_abs Gᵀ)).apply i j)]
  have habs : ∀ B : Matrix n n ℝ, ‖B.abs‖ = ‖B‖ := fun B =>
    Matrix.frobenius_norm_map_eq B _ fun a => by simp
  have hmul : ‖G.abs * Gᵀ.abs‖ ≤ ‖G‖ ^ 2 := by
    refine (Matrix.frobenius_norm_mul _ _).trans (le_of_eq ?_)
    rw [habs, habs, Matrix.frobenius_norm_transpose, sq]
  have hrank : ‖G‖ ≤ √(Fintype.card n : ℝ) * lpOpNorm 2 G :=
    (Matrix.frobenius_norm_le_sqrt_rank_mul_l2_opNorm G).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast G.rank_le_card_width))
        (Matrix.lpOpNorm_nonneg _ _))
  have hsq : ‖G‖ ^ 2 ≤ Fintype.card n * lpOpNorm 2 G ^ 2 := by
    calc ‖G‖ ^ 2 ≤ (√(Fintype.card n : ℝ) * lpOpNorm 2 G) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hrank 2
      _ = Fintype.card n * lpOpNorm 2 G ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc lpOpNorm 2 E ≤ ‖E‖ := Matrix.l2_opNorm_le_frobenius_norm E
    _ ≤ γ * ‖G.abs * Gᵀ.abs‖ := hF
    _ ≤ γ * (Fintype.card n * lpOpNorm 2 G ^ 2) :=
        mul_le_mul_of_nonneg_left (hmul.trans hsq) hγ
    _ = γ * Fintype.card n * lpOpNorm 2 G ^ 2 := by ring

variable {m : RoundingModel ℝ} {A G : Matrix n n ℝ}

/-- **Wilkinson's normwise bound for the Cholesky solve, rigorous** ([golub2013matrix] §4.2.6:
"`(A + E) x̂ = b`, `‖E‖₂ ≤ c_n u ‖A‖₂`"): under the hypotheses of
`FloatingPoint.exists_roundsCholeskyDiv_add_mulVec_eq` and `n γ_{n+3} < 1`, the computed solution
satisfies `(A + E) x̂ = b` with `‖E‖₂ ≤ n γ_{3n+3} ‖A‖₂ / (1 - n γ_{n+3})`. Both the solve's `E` and
the factorization's `ΔA` are bounded by `γ n ‖Ĝ‖₂²`
(`FloatingPoint.lpOpNorm_two_le_of_abs_le_smul_abs_mul_abs_transpose`), and
`‖Ĝ‖₂² = ‖Ĝ Ĝᵀ‖₂ = ‖A + ΔA‖₂ ≤ ‖A‖₂ + n γ_{n+3} ‖Ĝ‖₂²` is solved for `‖Ĝ‖₂²`. -/
theorem l2_opNorm_le_of_roundsCholeskyDiv (hu : m.u < 1)
    (hcard : ((3 * Fintype.card n + 3 : ℕ) : ℝ) * m.u < 1)
    (hγ : Fintype.card n * gamma m.u (Fintype.card n + 3) < 1) (hA : A.IsSymm)
    (h : RoundsCholeskyDiv m A G) (hd : ∀ j, G j j ≠ 0) {b y x : n → ℝ}
    (hy : RoundsForwardSubst m G b y) (hx : RoundsBackSubst m Gᵀ y x) :
    ∃ E : Matrix n n ℝ,
      lpOpNorm 2 E ≤ Fintype.card n * gamma m.u (3 * Fintype.card n + 3) * lpOpNorm 2 A /
        (1 - Fintype.card n * gamma m.u (Fintype.card n + 3)) ∧ (A + E) *ᵥ x = b := by
  have hle : ∀ j, j ≤ 3 * Fintype.card n + 3 → ((j : ℕ) : ℝ) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) m.u_nonneg).trans_lt hcard
  obtain ⟨E, hE, hAx⟩ := exists_roundsCholeskyDiv_add_mulVec_eq hu hcard hA h hd hy hx
  obtain ⟨ΔA, hΔA, hGG⟩ :=
    exists_roundsCholeskyDiv_mul_transpose_eq_add hu (hle _ (by omega)) hA h hd
  refine ⟨E, ?_, hAx⟩
  have hγ₁ := gamma_nonneg m.u_nonneg (hle (Fintype.card n + 3) (by omega))
  have hγ₃ := gamma_nonneg m.u_nonneg hcard
  have hΔ := lpOpNorm_two_le_of_abs_le_smul_abs_mul_abs_transpose hγ₁ hΔA
  have hE' := lpOpNorm_two_le_of_abs_le_smul_abs_mul_abs_transpose hγ₃ hE
  have hg : lpOpNorm 2 G ^ 2 ≤ lpOpNorm 2 A + lpOpNorm 2 ΔA := by
    have hGG' := Matrix.lpOpNorm_two_mul_conjTranspose_self G
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hGG] at hGG'
    rw [← hGG']
    exact Matrix.lpOpNorm_add_le 2 A ΔA
  have hpos : 0 < 1 - Fintype.card n * gamma m.u (Fintype.card n + 3) := by linarith
  have hg' : lpOpNorm 2 G ^ 2 ≤
      lpOpNorm 2 A / (1 - Fintype.card n * gamma m.u (Fintype.card n + 3)) := by
    rw [le_div_iff₀ hpos]
    linarith
  calc lpOpNorm 2 E ≤ gamma m.u (3 * Fintype.card n + 3) * Fintype.card n * lpOpNorm 2 G ^ 2 := hE'
    _ ≤ gamma m.u (3 * Fintype.card n + 3) * Fintype.card n *
          (lpOpNorm 2 A / (1 - Fintype.card n * gamma m.u (Fintype.card n + 3))) :=
        mul_le_mul_of_nonneg_left hg' (by positivity)
    _ = _ := by ring

end Wilkinson

/-! ### The Thomas algorithm -/

section Thomas

open Matrix (lowerBidiagonalOf upperBidiagonalOf lowerBidiagonalOf_mul_apply
  upperBidiagonalOf_apply_eq_zero)

variable {m : RoundingModel K} {N : ℕ}

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
