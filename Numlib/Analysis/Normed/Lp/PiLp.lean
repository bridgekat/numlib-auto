/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Lp.PiLp`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Comparison of the `ℓ^p` norms on a finite product

For `x` in a finite product `PiLp p β` of seminormed groups, the `p`-norms
`‖x‖_p = (∑ ‖x i‖ ^ p) ^ (1 / p)` are compared with each other:

* `PiLp.norm_le_norm_of_le`: `‖x‖_q ≤ ‖x‖_p` for `1 ≤ p ≤ q ≤ ∞` — the `p`-norms decrease in
  `p`, because `t ↦ t ^ (q / p)` is superadditive on `[0, ∞)`
  (`NNReal.sum_rpow_le_rpow_sum`);
* `PiLp.norm_le_card_rpow_mul_norm`: `‖x‖_p ≤ (card ι) ^ (1 / p - 1 / q) ‖x‖_q` for
  `1 ≤ p ≤ q ≤ ∞`, from the power-mean inequality `NNReal.rpow_sum_le_const_mul_sum_rpow`
  (Hölder with exponents `q / p` and its conjugate);
* `PiLp.tendsto_norm_toLp_atTop`: `‖x‖_p → ‖x‖_∞` as `p → ∞`, by squeezing between the two.

The six instances with `p, q ∈ {1, 2, ∞}` are the equivalence constants `1`, `√n`, `n` of
[quarteroni2000numerical] Table 1.1 and are stated as corollaries
(`PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two`, …). Mathlib has the `∞`-versus-`p`
comparison as the Lipschitz constants `PiLp.lipschitzWith_toLp` / `PiLp.antilipschitzWith_ofLp`
only; the matrix consequences (the operator-norm comparison table) are in
`Numlib/Analysis/Matrix/OperatorNorm`.
-/

open Filter Topology WithLp
open scoped ENNReal NNReal

/-- `t ↦ t ^ p` is superadditive on `ℝ≥0` for `1 ≤ p`: `∑ (f i) ^ p ≤ (∑ f i) ^ p`. The finite-sum
form of `NNReal.add_rpow_le_rpow_add`. -/
theorem NNReal.sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0) {p : ℝ}
    (hp : 1 ≤ p) : ∑ i ∈ s, f i ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    calc f j ^ p + ∑ i ∈ s, f i ^ p ≤ f j ^ p + (∑ i ∈ s, f i) ^ p := by gcongr
      _ ≤ (f j + ∑ i ∈ s, f i) ^ p := NNReal.add_rpow_le_rpow_add _ _ hp

namespace PiLp

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)]

/-- `1 ≤ p.toReal` for a finite exponent `p` with `Fact (1 ≤ p)`. -/
private theorem one_le_toReal {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (h : p ≠ ∞) : 1 ≤ p.toReal := by
  simpa using ENNReal.toReal_mono h hp.out

/-- **The `p`-norms decrease in `p`**: `‖x‖_q ≤ ‖x‖_p` for `1 ≤ p ≤ q ≤ ∞`. For finite `q` this
is the superadditivity of `t ↦ t ^ (q / p)`, `∑ ‖x i‖ ^ q ≤ (∑ ‖x i‖ ^ p) ^ (q / p)`; for
`q = ∞` it is `PiLp.norm_apply_le`. These are the constants `c_pq = 1` of
[quarteroni2000numerical] Table 1.1. -/
theorem norm_le_norm_of_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q)
    (x : ∀ i, β i) : ‖toLp q x‖ ≤ ‖toLp p x‖ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [norm_toLp]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_apply_le (toLp p x) i
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := zero_lt_one.trans_le (one_le_toReal hp)
  have hQ : 0 < q.toReal := zero_lt_one.trans_le (one_le_toReal hq)
  have hr : 1 ≤ q.toReal / p.toReal := (one_le_div hP).2 (ENNReal.toReal_mono hq hpq)
  have key : ‖toLp q x‖₊ ≤ ‖toLp p x‖₊ := by
    rw [nnnorm_eq_sum hq, nnnorm_eq_sum hp]
    calc (∑ i, ‖x i‖₊ ^ q.toReal) ^ (1 / q.toReal)
        = (∑ i, (‖x i‖₊ ^ p.toReal) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← NNReal.rpow_mul, mul_div_cancel₀ _ hP.ne']
      _ ≤ ((∑ i, ‖x i‖₊ ^ p.toReal) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) :=
          NNReal.rpow_le_rpow (NNReal.sum_rpow_le_rpow_sum _ _ hr) (by positivity)
      _ = (∑ i, ‖x i‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [← NNReal.rpow_mul]
          congr 1
          field_simp
  exact_mod_cast key

/-- **The `p`-norms are equivalent with the constants `(card ι) ^ (1 / p - 1 / q)`**:
`‖x‖_p ≤ (card ι) ^ (1 / p - 1 / q) ‖x‖_q` for `1 ≤ p ≤ q ≤ ∞` (with `1 / ∞ = 0`). For finite
`q` this is the power-mean inequality `NNReal.rpow_sum_le_const_mul_sum_rpow` with exponent
`q / p`; for `q = ∞` it is the Lipschitz constant `PiLp.lipschitzWith_toLp`. These are the
constants `C_pq` of [quarteroni2000numerical] Table 1.1. -/
theorem norm_le_card_rpow_mul_norm {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q)
    (x : ∀ i, β i) :
    ‖toLp p x‖ ≤ (Fintype.card ι : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖toLp q x‖ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [norm_toLp, ENNReal.toReal_top, div_zero, sub_zero]
    have h := (lipschitzWith_toLp p β).norm_le_mul (toLp_zero p) x
    rwa [NNReal.coe_rpow, NNReal.coe_natCast, one_div, ENNReal.toReal_inv, ← one_div] at h
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := zero_lt_one.trans_le (one_le_toReal hp)
  have hQ : 0 < q.toReal := zero_lt_one.trans_le (one_le_toReal hq)
  have hr : 1 ≤ q.toReal / p.toReal := (one_le_div hP).2 (ENNReal.toReal_mono hq hpq)
  have key : ‖toLp p x‖₊ ≤
      (Fintype.card ι : ℝ≥0) ^ (1 / p.toReal - 1 / q.toReal) * ‖toLp q x‖₊ := by
    rw [nnnorm_eq_sum hq, nnnorm_eq_sum hp]
    have hmean := NNReal.rpow_sum_le_const_mul_sum_rpow Finset.univ
      (fun i => ‖x i‖₊ ^ p.toReal) hr
    simp only [Finset.card_univ, ← NNReal.rpow_mul, mul_div_cancel₀ _ hP.ne'] at hmean
    calc (∑ i, ‖x i‖₊ ^ p.toReal) ^ (1 / p.toReal)
        = ((∑ i, ‖x i‖₊ ^ p.toReal) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
          rw [← NNReal.rpow_mul]
          congr 1
          field_simp
      _ ≤ ((Fintype.card ι : ℝ≥0) ^ (q.toReal / p.toReal - 1) * ∑ i, ‖x i‖₊ ^ q.toReal) ^
            (1 / q.toReal) := NNReal.rpow_le_rpow hmean (by positivity)
      _ = (Fintype.card ι : ℝ≥0) ^ (1 / p.toReal - 1 / q.toReal) *
            (∑ i, ‖x i‖₊ ^ q.toReal) ^ (1 / q.toReal) := by
          rw [NNReal.mul_rpow, ← NNReal.rpow_mul]
          congr 2
          field_simp
  exact_mod_cast key

/-- **`‖x‖_p → ‖x‖_∞` as `p → ∞`**: the maximum norm is the limit of the `p`-norms, squeezed
between `‖x‖_∞ ≤ ‖x‖_p ≤ (card ι + 1) ^ (1 / p) ‖x‖_∞`. The `p`-norm of the statement is the
`Norm` instance of `PiLp`, which is defined for every exponent; the bounds hold for `p ≥ 1`.
[quarteroni2000numerical] §1.10. -/
theorem tendsto_norm_toLp_atTop (x : ∀ i, β i) :
    Tendsto (fun p : ℝ => ‖toLp (ENNReal.ofReal p) x‖) atTop (𝓝 ‖toLp ∞ x‖) := by
  have hn : Tendsto (fun p : ℝ => ((Fintype.card ι : ℝ) + 1) ^ (1 / p)) atTop (𝓝 1) := by
    have h := (Real.continuousAt_const_rpow
      (by positivity : ((Fintype.card ι : ℝ) + 1) ≠ 0)).tendsto.comp tendsto_inv_atTop_zero
    simpa [Function.comp_def, one_div] using h
  have hfact : ∀ p : ℝ, 1 ≤ p → Fact (1 ≤ ENNReal.ofReal p) := fun p hp =>
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => ‖toLp ∞ x‖)
    (h := fun p => ((Fintype.card ι : ℝ) + 1) ^ (1 / p) * ‖toLp ∞ x‖) tendsto_const_nhds
    (by simpa only [one_mul] using hn.mul_const ‖toLp ∞ x‖) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with p hp
    have := hfact p hp
    exact norm_le_norm_of_le le_top x
  · filter_upwards [eventually_ge_atTop 1] with p hp
    have := hfact p hp
    have h := norm_le_card_rpow_mul_norm (p := ENNReal.ofReal p) (q := ∞) le_top x
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_top, div_zero, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by positivity)

/-! ### The constants of Table 1.1

The six comparisons between the `1`-, `2`- and `∞`-norms, [quarteroni2000numerical] Table 1.1:
`‖x‖_∞ ≤ ‖x‖_2 ≤ ‖x‖_1` with constant `1`, and `‖x‖_1 ≤ √n ‖x‖_2`, `‖x‖_2 ≤ √n ‖x‖_∞`,
`‖x‖_1 ≤ n ‖x‖_∞`. -/

/-- `‖x‖_2 ≤ ‖x‖_1`. -/
theorem norm_toLp_two_le_norm_toLp_one (x : ∀ i, β i) : ‖toLp 2 x‖ ≤ ‖toLp 1 x‖ :=
  norm_le_norm_of_le (by norm_num) x

/-- `‖x‖_∞ ≤ ‖x‖_2`. -/
theorem norm_toLp_top_le_norm_toLp_two (x : ∀ i, β i) : ‖toLp ∞ x‖ ≤ ‖toLp 2 x‖ :=
  norm_le_norm_of_le le_top x

/-- `‖x‖_∞ ≤ ‖x‖_1`. -/
theorem norm_toLp_top_le_norm_toLp_one (x : ∀ i, β i) : ‖toLp ∞ x‖ ≤ ‖toLp 1 x‖ :=
  norm_le_norm_of_le le_top x

/-- `‖x‖_1 ≤ √n ‖x‖_2`, `n` the number of coordinates. -/
theorem norm_toLp_one_le_sqrt_card_mul_norm_toLp_two (x : ∀ i, β i) :
    ‖toLp 1 x‖ ≤ √(Fintype.card ι : ℝ) * ‖toLp 2 x‖ := by
  have h := norm_le_card_rpow_mul_norm (p := 1) (q := 2) (by norm_num) x
  rw [Real.sqrt_eq_rpow]
  convert h using 3
  norm_num

/-- `‖x‖_2 ≤ √n ‖x‖_∞`, `n` the number of coordinates. -/
theorem norm_toLp_two_le_sqrt_card_mul_norm_toLp_top (x : ∀ i, β i) :
    ‖toLp 2 x‖ ≤ √(Fintype.card ι : ℝ) * ‖toLp ∞ x‖ := by
  have h := norm_le_card_rpow_mul_norm (p := 2) (q := ∞) le_top x
  rw [Real.sqrt_eq_rpow]
  convert h using 3
  norm_num

/-- `‖x‖_1 ≤ n ‖x‖_∞`, `n` the number of coordinates. -/
theorem norm_toLp_one_le_card_mul_norm_toLp_top (x : ∀ i, β i) :
    ‖toLp 1 x‖ ≤ Fintype.card ι * ‖toLp ∞ x‖ := by
  have h := norm_le_card_rpow_mul_norm (p := 1) (q := ∞) le_top x
  simpa using h

end PiLp
