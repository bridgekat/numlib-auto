import Numlib.Direct.Substitution
import Numlib.FloatingPoint.InnerProduct

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
Theorem 8.5 is exactly `γ_n`. An implementation that first accumulates the inner product and then
subtracts it from `b i` (Program 1) performs the same roundings except for the first row, where it
rounds `b i - 0`; the relational model cannot know that this rounding is exact, so that order is
covered by the same theorems with `γ_n` replaced by `γ_{n+1}` (`Numlib/FloatingPoint/LU` uses
that order for the Doolittle recurrence, where the extra rounding costs nothing).

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
  (`Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant'`).

Backward substitution is forward substitution on the dual order
(`FloatingPoint.roundsBackSubst_iff_roundsForwardSubst_toDual`), as in
`Numlib/Direct/Substitution`. The normwise consequence [quarteroni2000numerical] (3.25) needs a
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

/-- **[higham2002accuracy] Lemma 8.4**: if `ŷ = (c - ∑_{j ∈ o} a_j b_j) / d` is evaluated with
rounded products, running differences in the order `o`, and a final division, then
`d ŷ (1 + θ₀) = c - ∑_{j ∈ o} a_j b_j (1 + θ_j)` with every `|θ| ≤ γ_{k+1}`, `k` the number of
terms — no matter what the order `o`. The divisor must be nonzero, since the model rounds
`t / d` with the junk value `t / 0 = 0`. -/
theorem exists_rounds_sub_dot_div_eq {m : RoundingModel K} (hu : m.u < 1) {a b p : ι → K}
    {o : List ι} (hnd : o.Nodup) (hp : ∀ j ∈ o, m.Rounds (a j * b j) (p j)) {c d t y : K}
    (hd : d ≠ 0) (ht : RoundsSumFrom m c (o.map fun j => -p j) t) (hy : m.Rounds (t / d) y)
    (hlu : ((o.length + 1 : ℕ) : K) * m.u < 1) :
    ∃ (θ₀ : K) (θ : ι → K), |θ₀| ≤ gamma m.u (o.length + 1) ∧
      (∀ j ∈ o, |θ j| ≤ gamma m.u (o.length + 1)) ∧
      d * y * (1 + θ₀) = c - ∑ j ∈ o.toFinset, a j * b j * (1 + θ j) := by
  classical
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

/-! ### Forward substitution -/

section Forward

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **Forward substitution in floating-point arithmetic.** `RoundsForwardSubst m T b x̂` says that
every `x̂ i` is an admissible computed value of `(b i - ∑_{j < i} T i j x̂ j) / T i i`
([quarteroni2000numerical] (3.22)), computed as in [higham2002accuracy] Lemma 8.4: the products
`T i j x̂ j` are rounded (`p j`), subtracted from `b i` one after the other in some order `o` of
the indices `j < i` with one rounding per subtraction (`RoundsSumFrom`), and the result `t` is
divided by `T i i` with one more rounding. The order is existentially quantified, so a theorem
about `RoundsForwardSubst` holds for every order an implementation may use. -/
def RoundsForwardSubst (m : RoundingModel K) (T : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, ∃ (o : List n) (p : n → K) (t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ j < i) ∧
    (∀ j ∈ o, m.Rounds (T i j * xhat j) (p j)) ∧
    RoundsSumFrom m (b i) (o.map fun j => -p j) t ∧ m.Rounds (t / T i i) (xhat i)

/-- The number of indices `≤ i` is at most the number of indices. -/
theorem card_filter_le_le_card (i : n) : #{j | j ≤ i} ≤ Fintype.card n := by
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.filter_subset _ _)

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
  obtain ⟨o, p, t, hnd, ho, hp, ht, hx⟩ := h i
  have hset : o.toFinset = univ.filter (· < i) := by
    ext j
    simp [ho]
  have hlen : o.length + 1 = #{j | j ≤ i} := by
    rw [← List.toFinset_card_of_nodup hnd, hset, Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
      Matrix.sum_filter_le_eq_add]
  have hle : o.length + 1 ≤ Fintype.card n := hlen ▸ card_filter_le_le_card i
  have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard
  obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_rounds_sub_dot_div_eq hu hnd hp hd ht hx hlu
  have hmono := gamma_mono m.u_nonneg hle hcard
  refine ⟨θ₀, θ, hθ₀.trans hmono, fun j hj => (hθ j ((ho j).2 hj)).trans hmono, ?_⟩
  rw [← hset]
  exact heq

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
      (T + ΔT) *ᵥ xhat = b := by
  choose θ₀ θ hθ₀ hθ heq using fun i => exists_roundsForwardSubst_row_eq hu hcard h i (hd i)
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
      exact mul_nonneg (gamma_nonneg m.u_nonneg hcard) (abs_nonneg _)
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

end Forward

/-! ### Backward substitution -/

section Backward

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **Backward substitution in floating-point arithmetic**, [quarteroni2000numerical] (3.23): as
`FloatingPoint.RoundsForwardSubst` with the products over the indices `j > i`. It is forward
substitution on the dual order (`FloatingPoint.roundsBackSubst_iff_roundsForwardSubst_toDual`). -/
def RoundsBackSubst (m : RoundingModel K) (U : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, ∃ (o : List n) (p : n → K) (t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ i < j) ∧
    (∀ j ∈ o, m.Rounds (U i j * xhat j) (p j)) ∧
    RoundsSumFrom m (b i) (o.map fun j => -p j) t ∧ m.Rounds (t / U i i) (xhat i)

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

end FloatingPoint
