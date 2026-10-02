import Numlib.Direct.Substitution
import Numlib.FloatingPoint.InnerProduct
import Numlib.FloatingPoint.Program

/-!
# Rounding errors of forward and backward substitution

The backward error of the substitution algorithms for triangular systems, in the relational
rounding model of `Numlib/FloatingPoint/Model` and in the style of
`Numlib/FloatingPoint/InnerProduct`: [quarteroni2000numerical] §3.2.2, [higham2002accuracy]
§8.1–8.2.

The algorithm is described by *what is rounded*, for an explicit order of the operations.
`RoundsForwardSubst m T b x̂` says that each `x̂ i` is an admissible value of
`(b i - ∑_{j < i} T i j x̂ j) / T i i` computed as [higham2002accuracy] Lemma 8.4 computes it: the
products `T i j x̂ j` are rounded, subtracted one after the other from `b i` — in *any* order of the
indices `j < i`, which is existentially quantified — with one rounding per subtraction, and the
result is divided by `T i i` with one more rounding. This is the running-difference form of the
recurrence (the book's Program 2), and it is the evaluation order for which the constant of
Theorem 8.5 is exactly `γ_n`. The Doolittle recurrence of `Numlib/FloatingPoint/LU`
(`FloatingPoint.RoundsLU`) is computed by the same running differences, which is why its constant
is `γ_n` as well.

The inner-product order of [golub2013matrix] Algorithms 3.1.1–3.1.2 (Program 1 of
[quarteroni2000numerical]: the dot product `s = fl(s + fl(t_ij x̂_j))` accumulated from `s = 0`,
then one rounded subtraction from `b i` and one rounded division, the first row divided only) is
`FloatingPoint.RoundsForwardSubstDot` and `FloatingPoint.RoundsBackSubstDot`. It rounds `0 + p`
and `b i - s`, which the relational model cannot know to be exact, yet the bound is still `γ_n`:
the extra rounding lands on the diagonal with order `2 ≤ n`
(`FloatingPoint.exists_rounds_sub_dotFrom_div_eq`), and on each term with order `#{j ≤ i} ≤ n`.
The first row must only divide: rounding `b 1 - 0` there too would give the diagonal the order
`2`, and the bound `γ_n` would fail for `n = 1`.

The scalar core is [higham2002accuracy] Lemma 8.4 (`FloatingPoint.exists_rounds_sub_dot_div_eq`):
`d ŷ (1 + θ₀) = c - ∑_i a_i b_i (1 + θ_i)` with every `|θ| ≤ γ_{k+1}`, `k` the number of terms. It
rests on two one-rounding steps, `(1 + θ_k)(1 + δ) = 1 + θ_{k+1}` and `(1 + θ_k) / (1 + δ) = 1 +
θ_{k+1}` (`FloatingPoint.abs_one_add_div_one_add_sub_one_le_gamma`), the latter being why a
division counts as one rounding rather than two.

Results, entrywise, over an ordered field `K`:

* `FloatingPoint.exists_roundsForwardSubst_eq`, `FloatingPoint.exists_roundsBackSubst_eq`:
  [higham2002accuracy] Theorem 8.5 = [quarteroni2000numerical] (3.24), `(T + ΔT) x̂ = b` with
  `|ΔT| ≤ γ_n |T|`;
* `FloatingPoint.abs_sub_le_of_roundsBackSubst_of_abs_le_diag`: [higham2002accuracy] Theorem
  8.7 = [quarteroni2000numerical] §3.2.2's improved bound `|x_i - x̂_i| ≤ 2^{n-i+1} γ_n max_{j ≥ i}
  |x̂_j|` when `|u_ii| ≥ |u_ij|`, from Lemma 8.6 (`Matrix.sum_abs_inv_mul_abs_apply_le_two_pow`);
* `FloatingPoint.abs_sub_le_of_roundsBackSubst_of_isDiagDominant`: the row diagonally dominant
  case, `|x_i - x̂_i| ≤ (2n - 1) γ_n ‖x̂‖_∞`, from Lemma 8.8
  (`Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant'`);
* `FloatingPoint.exists_roundsForwardSubstDot_eq`, `FloatingPoint.exists_roundsBackSubstDot_eq`:
  the rigorous forms of [golub2013matrix] (3.1.1)–(3.1.2), `(T + ΔT) x̂ = b` with `|ΔT| ≤ γ_n |T|`
  for the inner-product order;
* `FloatingPoint.roundsForwardSubst_exact_iff` and its three siblings: at the exact model
  (`RoundingModel.exact`) every relation of this file pins its output to `Matrix.forwardSubst` or
  `Matrix.backSubst`, with no hypothesis on the matrix. This is how the exact specification of a
  substitution program is read off its rounding bridge;
* `FloatingPoint.roundsForwardSubst_of_mem_run_colSubst`: the column-oriented loop of
  [golub2013matrix] Algorithm 3.1.3, over any linear order, lands in `RoundsForwardSubst` in every
  run of the relational model.

The entry relation of every row is the running difference `FloatingPoint.RoundsRunningDiff` of
`Numlib/FloatingPoint/InnerProduct` (its program is `FloatingPoint.runningDiff`), and the number of
its terms is counted once, by `FloatingPoint.length_add_one_le_card_of_forall_mem_iff`.

Every backward-error theorem is assembled from its rows by one lemma,
`FloatingPoint.exists_add_mulVec_eq_of_forall_row_eq`. Backward substitution is forward
substitution on the dual order (`FloatingPoint.roundsBackSubst_iff_roundsForwardSubst_toDual`), as
in `Numlib/Direct/Substitution`. The normwise consequence [quarteroni2000numerical] (3.25) needs a
norm and is a surface statement over `ℝ` through `relative_error_le_condNumber`.
-/

open Finset

open scoped Matrix

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Running differences: the scalar core -/

variable {ι : Type*} [DecidableEq ι]

/-- **Running sums, backwards** ([higham2002accuracy], the computation inside Lemma 8.4): if `t` is
obtained from `c` by adding the terms `f j`, `j ∈ o`, one rounding per addition, then
`t (1 + θ₀) = c + ∑_{j ∈ o} f j (1 + θ_j)` with every `|θ| ≤ γ_k`, `k` the number of terms. The
term `c` is not perturbed; every rounding is charged to `t` and to the terms added after it. -/
theorem exists_roundsSumFrom_map_eq {m : RoundingModel K} (hu : m.u < 1) {c t : K} {f : ι → K}
    {o : List ι} (hnd : o.Nodup) (h : RoundsSumFrom m c (o.map f) t)
    (hlu : ((o.length : ℕ) : K) * m.u < 1) :
    ∃ (θ₀ : K) (θ : ι → K), |θ₀| ≤ gamma m.u o.length ∧ (∀ j ∈ o, |θ j| ≤ gamma m.u o.length) ∧
      t * (1 + θ₀) = c + ∑ j ∈ o.toFinset, f j * (1 + θ j) := by
  classical
  induction o generalizing c t with
  | nil =>
    simp only [List.map_nil] at h
    cases h
    exact ⟨0, fun _ => 0, by simp, by simp, by simp⟩
  | cons j o ih =>
    simp only [List.map_cons] at h
    rcases h with _ | ⟨ht', hr⟩
    rename_i t'
    rw [List.length_cons] at hlu
    have hcast : ((o.length + 1 : ℕ) : K) * m.u = (o.length : K) * m.u + m.u := by
      push_cast; ring
    have hl : (o.length : K) * m.u < 1 := by
      rw [hcast] at hlu
      linarith [m.u_nonneg]
    obtain ⟨θ₀', θ', hθ₀', hθ', heq⟩ := ih (List.nodup_cons.1 hnd).2 hr hl
    obtain ⟨δ, hδ, rfl⟩ := ht'.exists_delta
    have hd : (1 : K) + δ ≠ 0 := by
      have := neg_le_of_abs_le hδ
      linarith
    have hj : j ∉ o.toFinset := fun hj => (List.nodup_cons.1 hnd).1 (List.mem_toFinset.1 hj)
    refine ⟨(1 + θ₀') / (1 + δ) - 1,
      fun i => if i = j then 0 else (1 + θ' i) / (1 + δ) - 1, ?_, ?_, ?_⟩
    · exact abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu hθ₀' hδ
    · intro i hi
      rw [List.mem_cons] at hi
      dsimp only
      by_cases hij : i = j
      · simp [hij, gamma_nonneg m.u_nonneg hlu]
      · rw [ite_eq_right hij]
        exact abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu (hθ' i (hi.resolve_left hij))
          hδ
    · rw [List.toFinset_cons, Finset.sum_insert hj]
      dsimp only
      rw [ite_eq_left rfl, add_zero, mul_one]
      have hsum : ∑ i ∈ o.toFinset, f i * (1 + if i = j then 0 else (1 + θ' i) / (1 + δ) - 1) =
          (∑ i ∈ o.toFinset, f i * (1 + θ' i)) / (1 + δ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hij : i ≠ j := fun e => hj (e ▸ hi)
        rw [ite_eq_right hij]
        field_simp
        ring
      have h1 : t * (1 + ((1 + θ₀') / (1 + δ) - 1)) = t * (1 + θ₀') / (1 + δ) := by
        field_simp
        ring
      rw [hsum, h1, heq]
      field_simp
      ring

/-- **[higham2002accuracy] Lemma 8.4**: if `ŷ = (c - ∑_{j ∈ o} a_j b_j) / d` is evaluated as a
running difference in the order `o` (`FloatingPoint.RoundsRunningDiff`) and a final division, then
`d ŷ (1 + θ₀) = c - ∑_{j ∈ o} a_j b_j (1 + θ_j)` with every `|θ| ≤ γ_{k+1}`, `k` the number of
terms — no matter what the order `o`. The divisor must be nonzero, since the model rounds
`t / d` with the junk value `t / 0 = 0`. -/
theorem exists_rounds_sub_dot_div_eq {m : RoundingModel K} (hu : m.u < 1) {a b : ι → K}
    {o : List ι} (hnd : o.Nodup) {c d t y : K} (hd : d ≠ 0) (ht : RoundsRunningDiff m o a b c t)
    (hy : m.Rounds (t / d) y) (hlu : ((o.length + 1 : ℕ) : K) * m.u < 1) :
    ∃ (θ₀ : K) (θ : ι → K), |θ₀| ≤ gamma m.u (o.length + 1) ∧
      (∀ j ∈ o, |θ j| ≤ gamma m.u (o.length + 1)) ∧
      d * y * (1 + θ₀) = c - ∑ j ∈ o.toFinset, a j * b j * (1 + θ j) := by
  classical
  obtain ⟨p, hp, ht⟩ := ht
  have hcast : ((o.length + 1 : ℕ) : K) * m.u = (o.length : K) * m.u + m.u := by push_cast; ring
  have hl : (o.length : K) * m.u < 1 := by
    rw [hcast] at hlu
    linarith [m.u_nonneg]
  obtain ⟨θ₀', θ', hθ₀', hθ', heq⟩ := exists_roundsSumFrom_map_eq hu hnd ht hl
  obtain ⟨δ, hδ, rfl⟩ := hy.exists_delta
  -- the rounded products, as relative perturbations
  have hprod : ∀ j ∈ o, ∃ ε : K, |ε| ≤ m.u ∧ p j = a j * b j * (1 + ε) := fun j hj =>
    (hp j hj).exists_delta
  choose! ε hε hpε using hprod
  have hd1 : (1 : K) + δ ≠ 0 := by
    have := neg_le_of_abs_le hδ
    linarith
  refine ⟨(1 + θ₀') / (1 + δ) - 1, fun j => (1 + θ' j) * (1 + ε j) - 1, ?_, ?_, ?_⟩
  · exact abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu hθ₀' hδ
  · intro j hj
    exact abs_one_add_mul_one_add_sub_one_le_gamma m.u_nonneg hu hlu (hθ' j hj) (hε j hj)
  · have hsum : ∑ j ∈ o.toFinset, a j * b j * (1 + ((1 + θ' j) * (1 + ε j) - 1)) =
        -∑ j ∈ o.toFinset, (-p j) * (1 + θ' j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hpε j (List.mem_toFinset.1 hj)]
      ring
    have heq' : t * (1 + θ₀') = c + ∑ j ∈ o.toFinset, -p j * (1 + θ' j) := heq
    dsimp only
    rw [hsum, sub_neg_eq_add, ← heq']
    field_simp
    ring

/-- **The scalar core of the inner-product order** (the analogue of [higham2002accuracy] Lemma 8.4
for "dot product, then subtract, then divide", [golub2013matrix] Algorithm 3.1.1): if `s` is
obtained from `0` by adding the rounded products `p_j = fl(a_j b_j)`, `j ∈ o`, one rounding per
addition (the first one, `fl(0 + p)`, included), `t` rounds `c - s` and `y` rounds `t / d`, then
`d y (1 + θ₀) = c - ∑_{j ∈ o} a_j b_j (1 + θ_j)` with `|θ₀| ≤ γ₂` and `|θ_j| ≤ γ_{k+1}`, `k` the
number of terms. The divisor must be nonzero, since the model rounds `t / d` with the junk value
`t / 0 = 0`. -/
theorem exists_rounds_sub_dotFrom_div_eq {m : RoundingModel K} (hu : m.u < 1) {a b p : ι → K}
    {o : List ι} (hnd : o.Nodup) (hp : ∀ j ∈ o, m.Rounds (a j * b j) (p j)) {c d s t y : K}
    (hd : d ≠ 0) (hs : RoundsSumFrom m 0 (o.map p) s) (ht : m.Rounds (c - s) t)
    (hy : m.Rounds (t / d) y) (hlu : ((o.length + 1 : ℕ) : K) * m.u < 1) (h2 : 2 * m.u < 1) :
    ∃ (θ₀ : K) (θ : ι → K), |θ₀| ≤ gamma m.u 2 ∧
      (∀ j ∈ o, |θ j| ≤ gamma m.u (o.length + 1)) ∧
      d * y * (1 + θ₀) = c - ∑ j ∈ o.toFinset, a j * b j * (1 + θ j) := by
  classical
  have hl : (o.length : K) * m.u < 1 := by
    have : (o.length : K) * m.u ≤ ((o.length + 1 : ℕ) : K) * m.u := by
      push_cast; nlinarith [m.u_nonneg]
    linarith
  obtain ⟨φ, θ', -, hθ', hseq⟩ := exists_roundsSumFrom_map_eq_add_sum hnd hs hl
  choose! ε hε hpε using fun j hj => (hp j hj).exists_delta
  obtain ⟨δ₁, hδ₁, rfl⟩ := ht.exists_delta
  obtain ⟨δ₂, hδ₂, rfl⟩ := hy.exists_delta
  have hd₁ : (1 : K) + δ₁ ≠ 0 := by linarith [neg_le_of_abs_le hδ₁]
  have hd₂ : (1 : K) + δ₂ ≠ 0 := by linarith [neg_le_of_abs_le hδ₂]
  refine ⟨(1 + 0) / (1 + δ₁) / (1 + δ₂) - 1, fun j => (1 + θ' j) * (1 + ε j) - 1, ?_,
    fun j hj => abs_one_add_mul_one_add_sub_one_le_gamma m.u_nonneg hu hlu (hθ' j hj) (hε j hj),
    ?_⟩
  · have hA := abs_one_add_div_one_add_sub_one_le_gamma (k := 0) (θ := 0) m.u_nonneg
      (by simpa using hu) (by simp) hδ₁
    have hB := abs_one_add_div_one_add_sub_one_le_gamma (k := 1) m.u_nonneg
      (by norm_num; exact h2) hA hδ₂
    rwa [add_sub_cancel] at hB
  · have hsum : s = ∑ j ∈ o.toFinset, a j * b j * (1 + ((1 + θ' j) * (1 + ε j) - 1)) := by
      rw [hseq, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hpε j (List.mem_toFinset.1 hj)]
      ring
    rw [← hsum]
    field_simp
    ring

/-! ### Forward substitution -/

section Forward

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **Forward substitution in floating-point arithmetic.** `RoundsForwardSubst m T b x̂` says that
every `x̂ i` is an admissible computed value of `(b i - ∑_{j < i} T i j x̂ j) / T i i`
([quarteroni2000numerical] (3.22)), computed as in [higham2002accuracy] Lemma 8.4: the running
difference `t` of `b i` and the rounded products `T i j x̂ j` in some order `o` of the indices
`j < i` (`FloatingPoint.RoundsRunningDiff`), divided by `T i i` with one more rounding. The order
is existentially quantified, so a theorem about `RoundsForwardSubst` holds for every order an
implementation may use. -/
def RoundsForwardSubst (m : RoundingModel K) (T : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, ∃ (o : List n) (t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ j < i) ∧
    RoundsRunningDiff m o (T i) xhat (b i) t ∧ m.Rounds (t / T i i) (xhat i)

/-- The number of indices `≤ i` is at most the number of indices. -/
theorem card_filter_le_le_card (i : n) : #{j | j ≤ i} ≤ Fintype.card n := by
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- A list of exactly the indices below `i` enumerates the `Finset` of the indices below `i`. -/
theorem toFinset_eq_filter_lt_of_forall_mem_iff {o : List n} {i : n} (ho : ∀ j, j ∈ o ↔ j < i) :
    o.toFinset = univ.filter (· < i) := by
  ext j
  simp [ho]

/-- **The number of terms of a running difference over the indices below `i`**: a duplicate-free
list of exactly those indices has at most `card n - 1` entries, so a row of a substitution or of a
factorization (the terms and one more operation) carries at most `card n` roundings. -/
theorem length_add_one_le_card_of_forall_mem_iff {o : List n} {i : n} (hnd : o.Nodup)
    (ho : ∀ j, j ∈ o ↔ j < i) : o.length + 1 ≤ Fintype.card n := by
  have hlen : o.length + 1 = #{j | j ≤ i} := by
    rw [← List.toFinset_card_of_nodup hnd, toFinset_eq_filter_lt_of_forall_mem_iff ho,
      Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Matrix.sum_filter_le_eq_add]
  exact hlen ▸ card_filter_le_le_card i

/-- **One row of [higham2002accuracy] Theorem 8.5**: a computed row of forward substitution
satisfies `t_ii x̂_i (1 + θ₀) = b_i - ∑_{j < i} t_ij x̂_j (1 + θ_j)` with every `|θ| ≤ γ_n`, `n` the
order of the system, by Lemma 8.4 with `#{j ≤ i} ≤ n` roundings. -/
theorem exists_roundsForwardSubst_row_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {T : Matrix n n K} {b xhat : n → K}
    (h : RoundsForwardSubst m T b xhat) (i : n) (hd : T i i ≠ 0) :
    ∃ (θ₀ : K) (θ : n → K), |θ₀| ≤ gamma m.u (Fintype.card n) ∧
      (∀ j, j < i → |θ j| ≤ gamma m.u (Fintype.card n)) ∧
      T i i * xhat i * (1 + θ₀) =
        b i - ∑ j ∈ univ.filter (· < i), T i j * xhat j * (1 + θ j) := by
  obtain ⟨o, t, hnd, ho, ht, hx⟩ := h i
  have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
  have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
  have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard
  obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_rounds_sub_dot_div_eq hu hnd hd ht hx hlu
  have hmono := gamma_mono m.u_nonneg hle hcard
  refine ⟨θ₀, θ, hθ₀.trans hmono, fun j hj => (hθ j ((ho j).2 hj)).trans hmono, ?_⟩
  rw [← hset]
  exact heq

/-- **Rows to a perturbed triangular system**, the assembly step of [higham2002accuracy]
Theorem 8.5 shared by every evaluation order: if every row `i` of a lower triangular `T` satisfies
`t_ii x̂_i (1 + θ₀) = b_i - ∑_{j < i} t_ij x̂_j (1 + θ_j)` with every `|θ| ≤ γ`, then
`(T + ΔT) x̂ = b` with `|ΔT| ≤ γ |T|` entrywise. -/
theorem exists_add_mulVec_eq_of_forall_row_eq {γ : K} (hγ : 0 ≤ γ) {T : Matrix n n K}
    (hT : T.IsLowerTriangular) {b xhat : n → K}
    (h : ∀ i, ∃ (θ₀ : K) (θ : n → K), |θ₀| ≤ γ ∧ (∀ j, j < i → |θ j| ≤ γ) ∧
      T i i * xhat i * (1 + θ₀) = b i - ∑ j ∈ univ.filter (· < i), T i j * xhat j * (1 + θ j)) :
    ∃ ΔT : Matrix n n K, (∀ i j, |ΔT i j| ≤ γ * |T i j|) ∧ (T + ΔT) *ᵥ xhat = b := by
  choose θ₀ θ hθ₀ hθ heq using h
  refine ⟨Matrix.of fun i j => if j < i then T i j * θ i j else if j = i then T i i * θ₀ i else 0,
    fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply]
    split_ifs with hji hji'
    · rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hθ i j hji) (abs_nonneg _)
    · subst hji'
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hθ₀ j) (abs_nonneg _)
    · rw [abs_zero]
      exact mul_nonneg hγ (abs_nonneg _)
  · have hT' : (T + Matrix.of fun i j =>
        if j < i then T i j * θ i j else if j = i then T i i * θ₀ i else 0).IsLowerTriangular := by
      intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      rw [Matrix.add_apply, hT hij, Matrix.of_apply, ite_eq_right hij'.not_gt,
        ite_eq_right hij'.ne', add_zero]
    ext i
    rw [Matrix.mulVec_apply_of_isLowerTriangular hT', Matrix.add_apply, Matrix.of_apply,
      ite_eq_right (lt_irrefl i), ite_eq_left rfl]
    have hrow : ∑ j ∈ univ.filter (· < i), (T + Matrix.of fun i j =>
        if j < i then T i j * θ i j else if j = i then T i i * θ₀ i else 0) i j * xhat j =
        ∑ j ∈ univ.filter (· < i), T i j * xhat j * (1 + θ i j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Matrix.add_apply, Matrix.of_apply, ite_eq_left (mem_filter.1 hj).2]
      ring
    rw [hrow]
    linear_combination heq i

/-- **[higham2002accuracy] Theorem 8.5**, [quarteroni2000numerical] (3.24): the solution `x̂`
of a lower triangular system `T x = b` computed by forward substitution, in any order of the
operations, solves exactly a perturbed system `(T + ΔT) x̂ = b` with `|ΔT| ≤ γ_n |T|` entrywise,
`n` the order of the system. Row `i` of the conclusion is Lemma 8.4; the perturbation lives on the
entries `j ≤ i` of row `i`. The diagonal must be nonzero because the model rounds `t / t_ii` with
the junk value `t / 0 = 0`. -/
theorem exists_roundsForwardSubst_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {T : Matrix n n K} (hT : T.IsLowerTriangular)
    (hd : ∀ i, T i i ≠ 0) {b xhat : n → K} (h : RoundsForwardSubst m T b xhat) :
    ∃ ΔT : Matrix n n K, (∀ i j, |ΔT i j| ≤ gamma m.u (Fintype.card n) * |T i j|) ∧
      (T + ΔT) *ᵥ xhat = b :=
  exists_add_mulVec_eq_of_forall_row_eq (gamma_nonneg m.u_nonneg hcard) hT fun i =>
    exists_roundsForwardSubst_row_eq hu hcard h i (hd i)

/-! #### The inner-product order -/

/-- **Forward substitution in the inner-product order** ([golub2013matrix] Algorithm 3.1.1,
[higham2002accuracy] §8.1's "inner product form"): `RoundsForwardSubstDot m T b x̂` says that for
every `i`, if no index lies below `i` then `x̂ i` rounds `b i / T i i`; otherwise the products
`T i j * x̂ j`, `j < i`, are rounded (`p j`), added to `0` one after the other in some order `o`
with one rounding per addition (the first one, `fl(0 + p)`, included), the sum `s` is subtracted
from `b i` with one rounding (`t`) and the difference is divided by `T i i` with one more rounding.
As for `FloatingPoint.RoundsForwardSubst`, the order is existentially quantified. -/
def RoundsForwardSubstDot (m : RoundingModel K) (T : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, (IsMin i → m.Rounds (b i / T i i) (xhat i)) ∧
    (¬ IsMin i → ∃ (o : List n) (p : n → K) (s t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ j < i) ∧
      (∀ j ∈ o, m.Rounds (T i j * xhat j) (p j)) ∧ RoundsSumFrom m 0 (o.map p) s ∧
      m.Rounds (b i - s) t ∧ m.Rounds (t / T i i) (xhat i))

/-- **One row of forward substitution in the inner-product order**: a computed row satisfies
`t_ii x̂_i (1 + θ₀) = b_i - ∑_{j < i} t_ij x̂_j (1 + θ_j)` with every `|θ| ≤ γ_n`, `n` the order of
the system. The first row has one rounded division (order `1`); every other row has the order `2`
of the subtraction and the division on the diagonal, which needs `n ≥ 2`, and the order
`#{j ≤ i} ≤ n` on the terms (`FloatingPoint.exists_rounds_sub_dotFrom_div_eq`). -/
theorem exists_roundsForwardSubstDot_row_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {T : Matrix n n K} {b xhat : n → K}
    (h : RoundsForwardSubstDot m T b xhat) (i : n) (hd : T i i ≠ 0) :
    ∃ (θ₀ : K) (θ : n → K), |θ₀| ≤ gamma m.u (Fintype.card n) ∧
      (∀ j, j < i → |θ j| ≤ gamma m.u (Fintype.card n)) ∧
      T i i * xhat i * (1 + θ₀) =
        b i - ∑ j ∈ univ.filter (· < i), T i j * xhat j * (1 + θ j) := by
  by_cases hi : IsMin i
  · obtain ⟨δ, hδ, hxδ⟩ := ((h i).1 hi).exists_delta
    have h1 : 1 ≤ Fintype.card n := Fintype.card_pos_iff.2 ⟨i⟩
    have hlu1 : ((0 + 1 : ℕ) : K) * m.u < 1 := by simpa using hu
    have hempty : univ.filter (· < i) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun j _ => hi.not_lt
    have hd₁ : (1 : K) + δ ≠ 0 := by linarith [neg_le_of_abs_le hδ]
    refine ⟨(1 + 0) / (1 + δ) - 1, fun _ => 0,
      (abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu1 (by simp) hδ).trans
        (gamma_mono m.u_nonneg h1 hcard), fun j hj => absurd hj hi.not_lt, ?_⟩
    rw [hempty, Finset.sum_empty, sub_zero, hxδ]
    field_simp
    ring
  · obtain ⟨o, p, s, t, hnd, ho, hp, hs, ht, hx⟩ := (h i).2 hi
    obtain ⟨j₀, hj₀⟩ := not_isMin_iff.1 hi
    have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
    have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
    have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard
    have h2n : 2 ≤ Fintype.card n := Fintype.one_lt_card_iff.2 ⟨j₀, i, hj₀.ne⟩
    have h2 : 2 * m.u < 1 := by
      have : (2 : K) * m.u ≤ (Fintype.card n : K) * m.u :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h2n) m.u_nonneg
      linarith
    obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_rounds_sub_dotFrom_div_eq hu hnd hp hd hs ht hx hlu h2
    refine ⟨θ₀, θ, hθ₀.trans (gamma_mono m.u_nonneg h2n hcard),
      fun j hj => (hθ j ((ho j).2 hj)).trans (gamma_mono m.u_nonneg hle hcard), ?_⟩
    rw [← hset]
    exact heq

/-- **Backward error of forward substitution in the inner-product order**, the rigorous form of
[golub2013matrix] (3.1.1): the solution `x̂` of a lower triangular system computed by
[golub2013matrix] Algorithm 3.1.1 solves exactly `(T + ΔT) x̂ = b` with `|ΔT| ≤ γ_n |T|`
entrywise — the same constant as `FloatingPoint.exists_roundsForwardSubst_eq`. -/
theorem exists_roundsForwardSubstDot_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {T : Matrix n n K} (hT : T.IsLowerTriangular)
    (hd : ∀ i, T i i ≠ 0) {b xhat : n → K} (h : RoundsForwardSubstDot m T b xhat) :
    ∃ ΔT : Matrix n n K, (∀ i j, |ΔT i j| ≤ gamma m.u (Fintype.card n) * |T i j|) ∧
      (T + ΔT) *ᵥ xhat = b :=
  exists_add_mulVec_eq_of_forall_row_eq (gamma_nonneg m.u_nonneg hcard) hT fun i =>
    exists_roundsForwardSubstDot_row_eq hu hcard h i (hd i)

end Forward

/-! ### Backward substitution -/

section Backward

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **Backward substitution in floating-point arithmetic**, [quarteroni2000numerical] (3.23): as
`FloatingPoint.RoundsForwardSubst` with the products over the indices `j > i`. It is forward
substitution on the dual order (`FloatingPoint.roundsBackSubst_iff_roundsForwardSubst_toDual`). -/
def RoundsBackSubst (m : RoundingModel K) (U : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, ∃ (o : List n) (t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ i < j) ∧
    RoundsRunningDiff m o (U i) xhat (b i) t ∧ m.Rounds (t / U i i) (xhat i)

omit [Fintype n] in
/-- Backward substitution is forward substitution on the dual order. -/
theorem roundsBackSubst_iff_roundsForwardSubst_toDual {m : RoundingModel K} {U : Matrix n n K}
    {b xhat : n → K} :
    RoundsBackSubst m U b xhat ↔ RoundsForwardSubst (n := nᵒᵈ) m U b xhat :=
  Iff.rfl

/-- **[higham2002accuracy] Theorem 8.5 for backward substitution**, [quarteroni2000numerical]
(3.24): the computed solution of an upper triangular system solves exactly `(U + ΔU) x̂ = b` with
`|ΔU| ≤ γ_n |U|`, by transport along the dual order. -/
theorem exists_roundsBackSubst_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {U : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) {b xhat : n → K} (h : RoundsBackSubst m U b xhat) :
    ∃ ΔU : Matrix n n K, (∀ i j, |ΔU i j| ≤ gamma m.u (Fintype.card n) * |U i j|) ∧
      (U + ΔU) *ᵥ xhat = b :=
  exists_roundsForwardSubst_eq (n := nᵒᵈ) hu hcard hU.isLowerTriangular_orderDual hd
    (roundsBackSubst_iff_roundsForwardSubst_toDual.1 h)

/-- **Backward substitution in the inner-product order** ([golub2013matrix] Algorithm 3.1.2): as
`FloatingPoint.RoundsForwardSubstDot` with the products over the indices `j > i`, the last row
divided only. It is `RoundsForwardSubstDot` on the dual order
(`FloatingPoint.roundsBackSubstDot_iff_roundsForwardSubstDot_toDual`). -/
def RoundsBackSubstDot (m : RoundingModel K) (U : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, (IsMax i → m.Rounds (b i / U i i) (xhat i)) ∧
    (¬ IsMax i → ∃ (o : List n) (p : n → K) (s t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ i < j) ∧
      (∀ j ∈ o, m.Rounds (U i j * xhat j) (p j)) ∧ RoundsSumFrom m 0 (o.map p) s ∧
      m.Rounds (b i - s) t ∧ m.Rounds (t / U i i) (xhat i))

omit [Fintype n] in
/-- Backward substitution in the inner-product order is forward substitution in the inner-product
order on the dual order. -/
theorem roundsBackSubstDot_iff_roundsForwardSubstDot_toDual {m : RoundingModel K}
    {U : Matrix n n K} {b xhat : n → K} :
    RoundsBackSubstDot m U b xhat ↔ RoundsForwardSubstDot (n := nᵒᵈ) m U b xhat :=
  Iff.rfl

/-- **Backward error of backward substitution in the inner-product order**, the rigorous form of
[golub2013matrix] (3.1.2): the computed solution of an upper triangular system solves exactly
`(U + ΔU) x̂ = b` with `|ΔU| ≤ γ_n |U|`, by transport along the dual order. -/
theorem exists_roundsBackSubstDot_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {U : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) {b xhat : n → K} (h : RoundsBackSubstDot m U b xhat) :
    ∃ ΔU : Matrix n n K, (∀ i j, |ΔU i j| ≤ gamma m.u (Fintype.card n) * |U i j|) ∧
      (U + ΔU) *ᵥ xhat = b :=
  exists_roundsForwardSubstDot_eq (n := nᵒᵈ) hu hcard hU.isLowerTriangular_orderDual hd
    (roundsBackSubstDot_iff_roundsForwardSubstDot_toDual.1 h)

/-- **The componentwise forward error of a perturbed solve**: if `U x = b` and
`(U + ΔU) x̂ = b` with `|ΔU| ≤ γ |U|`, then `|x - x̂| ≤ γ |U⁻¹| |U| |x̂|` entrywise, since
`x - x̂ = U⁻¹ ΔU x̂` ([higham2002accuracy], the first line of the proof of Theorem 8.7). -/
theorem abs_sub_le_of_mulVec_eq_of_abs_le {U ΔU : Matrix n n K} (hU : IsUnit U) {x xhat b : n → K}
    (hx : U *ᵥ x = b) (hxhat : (U + ΔU) *ᵥ xhat = b) {γ : K}
    (hΔ : ∀ i j, |ΔU i j| ≤ γ * |U i j|) :
    |x - xhat| ≤ γ • ((U⁻¹.abs * U.abs) *ᵥ |xhat|) := by
  have hUd : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).1 hU
  have hdiff : x - xhat = U⁻¹ *ᵥ (ΔU *ᵥ xhat) := by
    have h1 : U *ᵥ (x - xhat) = ΔU *ᵥ xhat := by
      rw [Matrix.add_mulVec] at hxhat
      rw [Matrix.mulVec_sub, hx, ← hxhat]
      abel
    rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul U hUd, Matrix.one_mulVec]
  have h2 : |ΔU *ᵥ xhat| ≤ (γ • U.abs) *ᵥ |xhat| := by
    refine (Matrix.abs_mulVec_le ΔU xhat).trans (Pi.le_def.2 fun i => ?_)
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.abs_apply, smul_eq_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hΔ i j) (abs_nonneg _)
  calc |x - xhat| = |U⁻¹ *ᵥ (ΔU *ᵥ xhat)| := by rw [hdiff]
    _ ≤ U⁻¹.abs *ᵥ |ΔU *ᵥ xhat| := Matrix.abs_mulVec_le _ _
    _ ≤ U⁻¹.abs *ᵥ ((γ • U.abs) *ᵥ |xhat|) :=
        (Matrix.entrywiseNonneg_abs U⁻¹).mulVec_mono h2
    _ = γ • ((U⁻¹.abs * U.abs) *ᵥ |xhat|) := by
        rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

/-- The row-`i` form of `FloatingPoint.abs_sub_le_of_mulVec_eq_of_abs_le` for an upper
triangular `U`, with the entries of `|x̂|` at or after `i` bounded by `c`:
`|x_i - x̂_i| ≤ γ c ∑_j (|U⁻¹| |U|)_ij`. -/
theorem abs_sub_apply_le_of_mulVec_eq_of_abs_le {U ΔU : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) {x xhat b : n → K} (hx : U *ᵥ x = b) (hxhat : (U + ΔU) *ᵥ xhat = b)
    {γ : K} (hγ : 0 ≤ γ) (hΔ : ∀ i j, |ΔU i j| ≤ γ * |U i j|) {i : n} {c : K}
    (hc : ∀ j, i ≤ j → |xhat j| ≤ c) :
    |x i - xhat i| ≤ γ * c * ∑ j, (U⁻¹.abs * U.abs) i j := by
  have hUu : IsUnit U := (Matrix.isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).2 hd
  have h := abs_sub_le_of_mulVec_eq_of_abs_le hUu hx hxhat hΔ i
  simp only [Pi.abs_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct] at h
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hγ
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt i j with hij | hji
  · rw [mul_comm c]
    refine mul_le_mul_of_nonneg_left (hc j hij) ?_
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · rw [Matrix.abs_inv_mul_abs_apply_of_lt hU hji, zero_mul, mul_zero]

/-- **[higham2002accuracy] Theorem 8.7**, the improved bound of [quarteroni2000numerical]
§3.2.2: if the upper triangular `U` has `|u_ii| ≥ |u_ij|` for `j > i` (as the triangular factors of
Gaussian elimination with partial pivoting do), `U x = b`, and `x̂` is computed by backward
substitution, then `|x_i - x̂_i| ≤ 2^{#{j ≥ i}} γ_n max_{j ≥ i} |x̂_j|` — the book's `2^{n-i+1}`,
the maximum being any bound `c` on the entries `|x̂_j|`, `j ≥ i`. From Theorem 8.5 and Lemma 8.6
(`Matrix.sum_abs_inv_mul_abs_apply_le_two_pow`). -/
theorem abs_sub_le_of_roundsBackSubst_of_abs_le_diag {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {U : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hrow : ∀ i j, i < j → |U i j| ≤ |U i i|) {x b xhat : n → K}
    (hx : U *ᵥ x = b) (h : RoundsBackSubst m U b xhat) {i : n} {c : K}
    (hc : ∀ j, i ≤ j → |xhat j| ≤ c) :
    |x i - xhat i| ≤ 2 ^ #{j | i ≤ j} * gamma m.u (Fintype.card n) * c := by
  obtain ⟨ΔU, hΔ, hxhat⟩ := exists_roundsBackSubst_eq hu hcard hU hd h
  have hγ := gamma_nonneg m.u_nonneg hcard
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc i le_rfl)
  refine (abs_sub_apply_le_of_mulVec_eq_of_abs_le hU hd hx hxhat hγ hΔ hc).trans ?_
  calc gamma m.u (Fintype.card n) * c * ∑ j, (U⁻¹.abs * U.abs) i j
      ≤ gamma m.u (Fintype.card n) * c * (2 ^ #{j | i ≤ j} - 1) :=
        mul_le_mul_of_nonneg_left (Matrix.sum_abs_inv_mul_abs_apply_le_two_pow hU hd hrow i)
          (mul_nonneg hγ hc0)
    _ ≤ gamma m.u (Fintype.card n) * c * 2 ^ #{j | i ≤ j} :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hγ hc0)
    _ = 2 ^ #{j | i ≤ j} * gamma m.u (Fintype.card n) * c := by ring

/-- **The row diagonally dominant case** of [quarteroni2000numerical] §3.2.2 ("the same result
holds … if `L` and `U` are diagonally dominant"): for a row diagonally dominant upper triangular
`U`, `U x = b` and `x̂` computed by backward substitution, `|x_i - x̂_i| ≤ (2n - 1) γ_n ‖x̂‖_∞`, the
maximum norm being any bound `c` on the entries of `x̂`. From Theorem 8.5 and [higham2002accuracy]
Lemma 8.8 (`Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant'`); the bound is linear in
`n`, better than the `2^{n-i+1}` the book's sentence suggests. -/
theorem abs_sub_le_of_roundsBackSubst_of_isDiagDominant {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {U : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |U i j| ≤ |U i i|) {x b xhat : n → K}
    (hx : U *ᵥ x = b) (h : RoundsBackSubst m U b xhat) {c : K} (hc : ∀ j, |xhat j| ≤ c) (i : n) :
    |x i - xhat i| ≤ (2 * Fintype.card n - 1) * gamma m.u (Fintype.card n) * c := by
  obtain ⟨ΔU, hΔ, hxhat⟩ := exists_roundsBackSubst_eq hu hcard hU hd h
  have hγ := gamma_nonneg m.u_nonneg hcard
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc i)
  refine (abs_sub_apply_le_of_mulVec_eq_of_abs_le hU hd hx hxhat hγ hΔ
    fun j _ => hc j).trans ?_
  calc gamma m.u (Fintype.card n) * c * ∑ j, (U⁻¹.abs * U.abs) i j
      ≤ gamma m.u (Fintype.card n) * c * (2 * Fintype.card n - 1) :=
        mul_le_mul_of_nonneg_left
          (Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant' hU hd hdom i)
          (mul_nonneg hγ hc0)
    _ = (2 * Fintype.card n - 1) * gamma m.u (Fintype.card n) * c := by ring

end Backward

/-! ### The exact model

At `RoundingModel.exact` every rounding is the identity, and the substitution relations collapse to
the recurrences `Matrix.forwardSubst` and `Matrix.backSubst`, with no hypothesis on the matrix
(both sides divide by a zero diagonal entry with the same junk value). This is how the exact
specification of a substitution program is read off its rounding bridge. -/

section Exact

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **The forward-substitution recurrence determines its solution**: a vector satisfying
`x i = (b i - ∑_{j < i} t_ij x_j) / t_ii` for every `i` is `Matrix.forwardSubst T b`, junk division
by a zero diagonal entry included. -/
theorem _root_.Matrix.eq_forwardSubst_of_forall_apply_eq {T : Matrix n n K} {b x : n → K}
    (h : ∀ i, x i = (b i - ∑ j ∈ univ.filter (· < i), T i j * x j) / T i i) :
    x = T.forwardSubst b := by
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
  rw [h i, Matrix.forwardSubst_apply]
  congr 2
  exact Finset.sum_congr rfl fun j hj => by rw [ih j (mem_filter.1 hj).2]

/-- In the exact model, the running difference of `c` and the terms `p j`, `j ∈ o`, is
`c - ∑_{j ∈ o} p j`. -/
theorem roundsSumFrom_exact_map_neg_iff {o : List ι} (hnd : o.Nodup) {p : ι → K} {c t : K} :
    RoundsSumFrom (RoundingModel.exact K) c (o.map fun j => -p j) t ↔
      t = c - ∑ j ∈ o.toFinset, p j := by
  rw [roundsSumFrom_exact_iff, ← List.sum_toFinset _ hnd, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- **Exact-model characterization of forward substitution**:
`RoundsForwardSubst exact T b x ↔ x = Matrix.forwardSubst T b`, with no hypothesis on `T`. -/
theorem roundsForwardSubst_exact_iff {T : Matrix n n K} {b x : n → K} :
    RoundsForwardSubst (RoundingModel.exact K) T b x ↔ x = T.forwardSubst b := by
  constructor
  · intro h
    refine Matrix.eq_forwardSubst_of_forall_apply_eq fun i => ?_
    obtain ⟨o, t, hnd, ho, ht, hx⟩ := h i
    rw [RoundingModel.exact_rounds_iff] at hx
    rw [hx, ht.eq_of_exact hnd, toFinset_eq_filter_lt_of_forall_mem_iff ho]
  · rintro rfl i
    refine ⟨(univ.filter (· < i)).toList,
      b i - ∑ j ∈ (univ.filter (· < i)).toList.toFinset, T i j * T.forwardSubst b j,
      Finset.nodup_toList _, fun j => by simp, ?_, ?_⟩
    · rw [roundsRunningDiff_exact_iff, List.sum_toFinset _ (Finset.nodup_toList _)]
    · rw [RoundingModel.exact_rounds_iff, Finset.toList_toFinset]
      exact Matrix.forwardSubst_apply T b i

/-- **Exact-model characterization of backward substitution**:
`RoundsBackSubst exact U b x ↔ x = Matrix.backSubst U b`, the dual of
`FloatingPoint.roundsForwardSubst_exact_iff`. -/
theorem roundsBackSubst_exact_iff {U : Matrix n n K} {b x : n → K} :
    RoundsBackSubst (RoundingModel.exact K) U b x ↔ x = U.backSubst b := by
  rw [roundsBackSubst_iff_roundsForwardSubst_toDual, Matrix.backSubst_eq_forwardSubst_toDual]
  exact roundsForwardSubst_exact_iff (n := nᵒᵈ)

/-- **Exact-model characterization of forward substitution in the inner-product order**:
`RoundsForwardSubstDot exact T b x ↔ x = Matrix.forwardSubst T b` (`0 + ∑` and `b - ∑` are exact at
`u = 0`). -/
theorem roundsForwardSubstDot_exact_iff {T : Matrix n n K} {b x : n → K} :
    RoundsForwardSubstDot (RoundingModel.exact K) T b x ↔ x = T.forwardSubst b := by
  constructor
  · intro h
    refine Matrix.eq_forwardSubst_of_forall_apply_eq fun i => ?_
    by_cases hi : IsMin i
    · rw [Finset.filter_eq_empty_iff.2 fun j _ => hi.not_lt, Finset.sum_empty, sub_zero]
      exact (h i).1 hi
    · obtain ⟨o, p, s, t, hnd, ho, hp, hs, ht, hx⟩ := (h i).2 hi
      rw [roundsSumFrom_exact_iff, zero_add, ← List.sum_toFinset _ hnd,
        toFinset_eq_filter_lt_of_forall_mem_iff ho] at hs
      rw [RoundingModel.exact_rounds_iff] at ht hx
      rw [hx, ht, hs]
      congr 2
      exact Finset.sum_congr rfl fun j hj => hp j ((ho j).2 (mem_filter.1 hj).2)
  · rintro rfl i
    refine ⟨fun hi => ?_, fun _ => ⟨(univ.filter (· < i)).toList,
      fun j => T i j * T.forwardSubst b j,
      ∑ j ∈ (univ.filter (· < i)).toList.toFinset, T i j * T.forwardSubst b j,
      b i - ∑ j ∈ (univ.filter (· < i)).toList.toFinset, T i j * T.forwardSubst b j,
      Finset.nodup_toList _, fun j => by simp, fun _ _ => rfl, ?_, rfl, ?_⟩⟩
    · rw [RoundingModel.exact_rounds_iff, Matrix.forwardSubst_apply,
        Finset.filter_eq_empty_iff.2 fun j _ => hi.not_lt, Finset.sum_empty, sub_zero]
    · rw [roundsSumFrom_exact_iff, zero_add, List.sum_toFinset _ (Finset.nodup_toList _)]
    · rw [RoundingModel.exact_rounds_iff, Finset.toList_toFinset]
      exact Matrix.forwardSubst_apply T b i

/-- **Exact-model characterization of backward substitution in the inner-product order**:
`RoundsBackSubstDot exact U b x ↔ x = Matrix.backSubst U b`, by duality. -/
theorem roundsBackSubstDot_exact_iff {U : Matrix n n K} {b x : n → K} :
    RoundsBackSubstDot (RoundingModel.exact K) U b x ↔ x = U.backSubst b := by
  rw [roundsBackSubstDot_iff_roundsForwardSubstDot_toDual, Matrix.backSubst_eq_forwardSubst_toDual]
  exact roundsForwardSubstDot_exact_iff (n := nᵒᵈ)

end Exact

end FloatingPoint

/-! ### Column-oriented forward substitution as a program

The loop "for `j` in increasing order, `b(j) = b(j)/L(j,j)`, then `b(i) = b(i) - b(j) L(i,j)` for
every `i > j`" ([golub2013matrix] Algorithm 3.1.3, over any linear order: Algorithm 3.1.4 is its
instance on the dual order) computes, in every run of the relational model, a
`FloatingPoint.RoundsForwardSubst`: row `i` receives its subtractions over `j < i` one at a time,
each from the finished `x̂ j`, which is a running difference in the order of the outer loop. -/

namespace FloatingPoint

universe u

section ColSubst

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι : Type u} [LinearOrder ι] [DecidableEq ι]

/-- The loop invariant of column-oriented forward substitution: indices outside the remaining
list `l` are finished rows of `RoundsForwardSubst`; an index `i` in `l` holds the running
difference of `b i` over the finished indices. -/
private def ColInv (fp : RoundingModel K) (L : Matrix ι ι K) (b : ι → K) (l : List ι)
    (s : ι → K) : Prop :=
  (∀ i, i ∉ l → ∃ (o : List ι) (t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ j < i) ∧
      RoundsRunningDiff fp o (L i) s (b i) t ∧ fp.Rounds (t / L i i) (s i)) ∧
  (∀ i, i ∈ l → ∃ o : List ι, o.Nodup ∧ (∀ j, j ∈ o ↔ j ∉ l) ∧
      RoundsRunningDiff fp o (L i) s (b i) (s i))

/-- One step of the outer loop keeps the invariant. -/
private theorem colInv_step (fp : RoundingModel K) (L : Matrix ι ι K) (b : ι → K) (j : ι)
    (c : List ι) (hcm : ∀ i, i ∈ c ↔ j < i) (l : List ι)
    (hsort : (j :: l).Pairwise (· < ·)) (hup : ∀ i ∈ j :: l, ∀ k, i ≤ k → k ∈ j :: l)
    (s : ι → K) (hs : ColInv fp L b (j :: l) s) (y : K) (hy : fp.Rounds (s j / L j j) y)
    (s₂ : ι → K)
    (h₂ : (∀ i, i ∉ c → s₂ i = Function.update s j y i) ∧
      ∀ i ∈ c, ∃ p, fp.Rounds (Function.update s j y j * L i j) p ∧
        fp.Rounds (Function.update s j y i - p) (s₂ i)) :
    ColInv fp L b l s₂ := by
  have hlt : ∀ k, k ∉ j :: l ↔ k < j := by
    intro k
    constructor
    · intro hk
      by_contra h
      exact hk (hup j List.mem_cons_self k (not_lt.1 h))
    · intro hk hmem
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact lt_irrefl _ hk
      · exact lt_asymm hk (List.rel_of_pairwise_cons hsort hmem)
  have hjl : j ∉ l := fun h => lt_irrefl _ (List.rel_of_pairwise_cons hsort h)
  have hbelow : ∀ k, k < j → s₂ k = s k := by
    intro k hk
    rw [h₂.1 k (by rw [hcm]; exact lt_asymm hk), Function.update_of_ne (ne_of_lt hk)]
  have hj₂ : s₂ j = y := by
    rw [h₂.1 j (by rw [hcm]; exact lt_irrefl _), Function.update_self]
  obtain ⟨hfin, hrun⟩ := hs
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · by_cases hij : i = j
    · subst hij
      obtain ⟨o, hnd, ho, hrd⟩ := hrun i List.mem_cons_self
      refine ⟨o, s i, hnd, fun k => (ho k).trans (hlt k),
        hrd.congr (fun _ _ => rfl) fun k hk => hbelow k ((hlt k).1 ((ho k).1 hk)), ?_⟩
      rw [hj₂]
      exact hy
    · have hi' : i ∉ j :: l := by
        intro h
        rcases List.mem_cons.1 h with h | h
        · exact hij h
        · exact hi h
      have hij' : i < j := (hlt i).1 hi'
      obtain ⟨o, t, hnd, ho, hrd, hr⟩ := hfin i hi'
      refine ⟨o, t, hnd, ho,
        hrd.congr (fun _ _ => rfl) fun k hk => hbelow k (lt_trans ((ho k).1 hk) hij'), ?_⟩
      rw [hbelow i hij']
      exact hr
  · have hji : j < i := List.rel_of_pairwise_cons hsort hi
    obtain ⟨o, hnd, ho, hrd⟩ := hrun i (List.mem_cons_of_mem _ hi)
    obtain ⟨q, hq, hq'⟩ := h₂.2 i ((hcm i).2 hji)
    rw [Function.update_of_ne (ne_of_gt hji)] at hq'
    rw [Function.update_self] at hq
    have hjo : j ∉ o := fun h => (ho j).1 h List.mem_cons_self
    refine ⟨o ++ [j], hnd.append (List.nodup_singleton _) (List.disjoint_singleton.2 hjo),
      fun k => ?_, ?_⟩
    · rw [List.mem_append, ho k, List.mem_singleton]
      constructor
      · rintro (h | rfl)
        · exact fun h' => h (List.mem_cons_of_mem _ h')
        · exact hjl
      · intro h
        by_cases hkj : k = j
        · exact Or.inr hkj
        · exact Or.inl fun h' => by
            rcases List.mem_cons.1 h' with h' | h'
            · exact hkj h'
            · exact h h'
    · refine (hrd.congr (b' := s₂) (fun _ _ => rfl) fun k hk =>
        hbelow k ((hlt k).1 ((ho k).1 hk))).append_singleton hjo ?_ hq'
      rw [hj₂, mul_comm]
      exact hq

/-- The outer loop, by induction on the remaining list. -/
private theorem colInv_foldlM (fp : RoundingModel K) (L : Matrix ι ι K) (b : ι → K)
    (c : ι → List ι) (hc : ∀ j, (c j).Nodup) (hcm : ∀ j i, i ∈ c j ↔ j < i) :
    ∀ (l : List ι) (s s' : ι → K), l.Pairwise (· < ·) →
    (∀ i ∈ l, ∀ k, i ≤ k → k ∈ l) → ColInv fp L b l s →
    s' ∈ (l.foldlM (fun (b : ι → K) j => do
      let bj ← fp.round (b j / L j j)
      (c j).foldlM (fun (b : ι → K) i => do
          let p ← fp.round (b j * L i j)
          let bi ← fp.round (b i - p)
          pure (Function.update b i bi))
        (Function.update b j bj)) s).run →
    ColInv fp L b [] s' := by
  intro l
  induction l with
  | nil =>
    intro s s' _ _ hs h
    rw [List.foldlM_nil, SetM.mem_run_pure] at h
    exact h ▸ hs
  | cons j l ih =>
    intro s s' hsort hup hs h
    simp only [List.foldlM_cons, bind_assoc] at h
    rw [SetM.mem_run_bind] at h
    obtain ⟨y, hy, h⟩ := h
    rw [SetM.mem_run_bind] at h
    obtain ⟨s₂, h₂, h⟩ := h
    have key := SetM.mem_run_foldlM_update_of_nodup
      (fun a v (z : ι → K) => fp.round (z j * L a j) >>= fun p => fp.round (v - p)) (c j) (hc j)
      (fun a _ v z z' hz => by rw [hz j fun h => lt_irrefl j ((hcm j j).1 h)])
      (Function.update s j y) s₂
    simp only [bind_assoc] at key
    obtain ⟨hout, hin⟩ := key.1 h₂
    have hin' : ∀ i ∈ c j, ∃ p, fp.Rounds (Function.update s j y j * L i j) p ∧
        fp.Rounds (Function.update s j y i - p) (s₂ i) := fun i hi => by
      obtain ⟨p, hp, hq⟩ := SetM.mem_run_bind.1 (hin i hi)
      exact ⟨p, hp, hq⟩
    refine ih s₂ s' (List.pairwise_cons.1 hsort).2 (fun i hi k hik => ?_)
      (colInv_step fp L b j (c j) (hcm j) l hsort hup s hs y hy s₂ ⟨hout, hin'⟩) h
    rcases List.mem_cons.1 (hup i (List.mem_cons_of_mem _ hi) k hik) with rfl | hk
    · exact absurd (lt_of_lt_of_le (List.rel_of_pairwise_cons hsort hi) hik) (lt_irrefl _)
    · exact hk

/-- **Column-oriented forward substitution, over any linear order**: the loop "for `j` in
increasing order, `b(j) = b(j)/L(j,j)`, then `b(i) = b(i) - b(j) L(i,j)` for every `i > j`" (the
inner list `c j` enumerating the indices above `j` in any order) computes, in every run of the
relational model, an admissible forward substitution `FloatingPoint.RoundsForwardSubst`: row `i`
receives its subtractions over `j < i` one at a time, each from the finished `x̂ j`
([golub2013matrix] Algorithm 3.1.3; Algorithm 3.1.4 on the dual order through
`roundsBackSubst_iff_roundsForwardSubst_toDual`). -/
theorem roundsForwardSubst_of_mem_run_colSubst (fp : RoundingModel K) (L : Matrix ι ι K)
    {l : List ι} (hl : l.Pairwise (· < ·)) (hall : ∀ i, i ∈ l) (c : ι → List ι)
    (hc : ∀ j, (c j).Nodup) (hcm : ∀ j i, i ∈ c j ↔ j < i) (b x : ι → K)
    (hx : x ∈ (l.foldlM (fun (b : ι → K) j => do
      let bj ← fp.round (b j / L j j)
      (c j).foldlM (fun (b : ι → K) i => do
          let p ← fp.round (b j * L i j)
          let bi ← fp.round (b i - p)
          pure (Function.update b i bi))
        (Function.update b j bj)) b).run) :
    RoundsForwardSubst fp L b x := by
  have h0 : ColInv fp L b l b := by
    refine ⟨fun i hi => absurd (hall i) hi, fun i _ => ?_⟩
    exact ⟨[], List.nodup_nil, fun j => by simp [hall j], fun _ => 0, by simp, .nil _⟩
  have := colInv_foldlM fp L b c hc hcm l b x hl (fun _ _ k _ => hall k) h0 hx
  exact fun i => this.1 i (by simp)

end ColSubst

end FloatingPoint
