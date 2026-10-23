import Numlib.Optimization.TrustRegion.HighOrder.Complexity
import Numlib.Analysis.Calculus.TaylorModel.Scalar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Approximation.Hermite.Endpoint

/-!
# Finite jets for sharp arbitrary-order trust-region examples

The objective drop equals the predicted degree-`q` decrease. The initial objective
value is four, accommodating the ceiling in the number of steps. The grid starts
at the origin. These corrections give a unit prediction ratio and bounded data.
-/

namespace HighOrderTrustRegion.Sharpness
open Set

/-- Number of nonterminal trials in the example. -/
noncomputable def length (q : ℕ) (ε : ℝ) : ℕ := ⌈1 / ε ^ (q + 1)⌉₊

/-- Equally spaced iterates starting at zero. -/
def point (ε : ℝ) (k : ℕ) : ℝ := k * ε

/-- The coefficient decreases from two to one. -/
noncomputable def weight (K k : ℕ) : ℝ := 2 - (k : ℝ) / K

/-- Objective values with the same drop as the degree-`q` model. -/
noncomputable def value (q : ℕ) (ε : ℝ) (K k : ℕ) : ℝ :=
  4 - ε ^ (q + 1) * ∑ i ∈ Finset.range k, weight K i

/-- Prescribed scalar derivative jets, including the objective value. -/
noncomputable def jet (q : ℕ) (ε : ℝ) (K k j : ℕ) : ℝ :=
  if j = 0 then value q ε K k else if j = q then -(q.factorial : ℝ) * ε * weight K k else 0

/-- Matching refers to actual iterated derivatives of a scalar function. -/
def MatchesJets (f : ℝ → ℝ) (q : ℕ) (ε : ℝ) (K : ℕ) : Prop :=
  ∀ k ≤ K, ∀ j ≤ q, iteratedDeriv j f (point ε k) = jet q ε K k j

/-- Matching the interpolation data is exactly matching each actual finite jet. -/
theorem matchesJets_iff {f : ℝ → ℝ} {q K : ℕ} {ε : ℝ} :
    MatchesJets f q ε K ↔
      ∀ k ≤ K, ∀ j ≤ q, iteratedDeriv j f (point ε k) = jet q ε K k j := Iff.rfl

/-- Actual function values agree with the zeroth interpolation jet. -/
theorem MatchesJets.value_eq {f : ℝ → ℝ} {q K k : ℕ} {ε : ℝ}
    (h : MatchesJets f q ε K) (hk : k ≤ K) : f (point ε k) = value q ε K k := by
  simpa [jet] using h k hk 0 (Nat.zero_le _)

/-- The example's grid is strictly increasing for positive accuracy. -/
theorem point_strictMono {ε : ℝ} (hε : 0 < ε) : StrictMono (point ε) := by
  intro i j hij
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hε

/-- The grid begins at the origin. -/
@[simp] theorem point_zero (ε : ℝ) : point ε 0 = 0 := by simp [point]

/-- Each trial moves by exactly one grid spacing. -/
theorem point_succ (ε : ℝ) (k : ℕ) : point ε (k + 1) = point ε k + ε := by
  simp [point, Nat.cast_add, add_mul]

/-- The ceiling gives at least the inverse-accuracy power number of trials. -/
theorem inverse_pow_le_length (q : ℕ) (ε : ℝ) :
    1 / ε ^ (q + 1) ≤ (length q ε : ℝ) := Nat.le_ceil _

/-- Positive accuracy gives a nonempty example. -/
theorem length_pos (q : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < length q ε := by
  rw [length, Nat.pos_iff_ne_zero, ne_eq, Nat.ceil_eq_zero]
  exact not_le_of_gt (by positivity)

/-- The product of the trial count and the per-trial accuracy power is below two. -/
theorem length_mul_pow_lt_two (q : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (length q ε : ℝ) * ε ^ (q + 1) < 2 := by
  have hp : 0 < ε ^ (q + 1) := by positivity
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 1 / ε ^ (q + 1) by positivity)
  have hpow : ε ^ (q + 1) ≤ 1 := pow_le_one₀ hε.le hε1
  have hh := mul_lt_mul_of_pos_right hc hp
  dsimp [length]
  calc
    (⌈1 / ε ^ (q + 1)⌉₊ : ℝ) * ε ^ (q + 1) <
      (1 / ε ^ (q + 1) + 1) * ε ^ (q + 1) := hh
    _ = 1 + ε ^ (q + 1) := by field_simp
    _ ≤ 2 := by linarith

/-- Weights on the finite interpolation grid lie between one and two. -/
theorem weight_mem_Icc {K k : ℕ} (hK : 0 < K) (hk : k ≤ K) : weight K k ∈ Icc 1 2 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hkr : (k : ℝ) ≤ K := by exact_mod_cast hk
  have hr : (k : ℝ) / K ≤ 1 := (div_le_one hKr).2 hkr
  have h0 : 0 ≤ (k : ℝ) / K := by positivity
  exact ⟨by dsimp [weight]; linarith, by dsimp [weight]; linarith⟩

/-- Before the final grid point, the coefficient is strictly larger than one. -/
theorem one_lt_weight {K k : ℕ} (hk : k < K) : 1 < weight K k := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  have hr : (k : ℝ) / K < 1 := (div_lt_one hKr).2 (by exact_mod_cast hk)
  dsimp [weight]
  linarith

/-- The coefficient at the final grid point is one. -/
theorem weight_last {K : ℕ} (hK : 0 < K) : weight K K = 1 := by
  norm_num [weight, ne_of_gt (show (0 : ℝ) < K by exact_mod_cast hK)]

/-- Adjacent weights have difference exactly `1/K`. -/
theorem weight_succ (K k : ℕ) : weight K (k + 1) = weight K k - 1 / K := by
  simp only [weight, Nat.cast_add, Nat.cast_one, add_div]
  ring

/-- The objective recurrence agrees exactly with the predicted model decrease. -/
theorem value_succ (q : ℕ) (ε : ℝ) (K k : ℕ) :
    value q ε K (k + 1) = value q ε K k - ε ^ (q + 1) * weight K k := by
  simp only [value, Finset.sum_range_succ]
  ring

/-- The initial objective value is the fixed number four. -/
@[simp] theorem value_zero (q : ℕ) (ε : ℝ) (K : ℕ) : value q ε K 0 = 4 := by
  simp [value]

/-- All objective data are uniformly bounded independently of the accuracy. -/
theorem value_mem_Icc (q : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {k : ℕ} (hk : k ≤ length q ε) : value q ε (length q ε) k ∈ Icc 0 4 := by
  have hK := length_pos q hε
  have hs0 : 0 ≤ ∑ i ∈ Finset.range k, weight (length q ε) i :=
    Finset.sum_nonneg fun i hi => (weight_mem_Icc hK
      ((Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk)).1.trans' (by norm_num)
  have hs2 : ∑ i ∈ Finset.range k, weight (length q ε) i ≤ (k : ℝ) * 2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) := Finset.sum_le_sum fun i hi =>
        (weight_mem_Icc hK ((Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk)).2
      _ = (k : ℝ) * 2 := by simp
  have hkr : (k : ℝ) ≤ length q ε := by exact_mod_cast hk
  have hp : 0 ≤ ε ^ (q + 1) := by positivity
  have hl := length_mul_pow_lt_two q hε hε1
  have hprod := mul_le_mul_of_nonneg_left hs2 hp
  have hcnt := mul_le_mul_of_nonneg_right hkr hp
  dsimp [value]
  constructor <;> nlinarith [mul_nonneg hp hs0]

/-- Positive-order jets below the maximal order vanish. -/
theorem jet_lower (q : ℕ) (ε : ℝ) (K k : ℕ) {j : ℕ} (hj : 0 < j) (hjq : j < q) :
    jet q ε K k j = 0 := by simp [jet, Nat.ne_of_gt hj, Nat.ne_of_lt hjq]

/-- The highest-order prescribed derivative has its stated factorial factor. -/
theorem jet_top {q : ℕ} (hq : 0 < q) (ε : ℝ) (K k : ℕ) :
    jet q ε K k q = -(q.factorial : ℝ) * ε * weight K k := by
  simp [jet, Nat.ne_of_gt hq]

/-- All interpolation data lie in a fixed cube depending only on the order. -/
theorem jet_bound {q : ℕ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {k j : ℕ} (hk : k ≤ length q ε) :
    |jet q ε (length q ε) k j| ≤ max 4 (2 * (q.factorial : ℝ)) := by
  by_cases hj : j = 0
  · subst j
    have hv := value_mem_Icc q hε hε1 hk
    simpa [jet, abs_of_nonneg hv.1] using hv.2.trans (le_max_left 4 _)
  · by_cases hjq : j = q
    · subst j
      rw [jet_top hq, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity),
        abs_of_pos hε, abs_of_nonneg (by linarith [(weight_mem_Icc (length_pos q hε) hk).1])]
      have hw := (weight_mem_Icc (length_pos q hε) hk).2
      calc
        (q.factorial : ℝ) * ε * weight (length q ε) k ≤ (q.factorial : ℝ) * 1 * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hε1 (by positivity)) hw
            (by linarith [(weight_mem_Icc (length_pos q hε) hk).1]) (by positivity)
        _ ≤ max 4 (2 * (q.factorial : ℝ)) := by nlinarith [le_max_right 4 (2 * (q.factorial : ℝ))]
    · simp [jet, hj, hjq, le_max_iff]

/-- A matched finite jet determines its actual lower-order Taylor model. -/
theorem eval_lower_of_matches {f : ℝ → ℝ} {q K k p : ℕ} {ε t : ℝ}
    (h : MatchesJets f q ε K) (hk : k ≤ K) (hp : p < q) :
    TaylorModel.eval f p (point ε k) t = value q ε K k := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv, Finset.sum_eq_single 0]
  · simp [h k hk 0 (by omega), jet]
  · intro i hi hi0
    rw [h k hk i (by have := Finset.mem_range.mp hi; omega),
      jet_lower q ε K k (Nat.pos_of_ne_zero hi0) (by have := Finset.mem_range.mp hi; omega)]
    simp
  · simp

/-- A matched finite jet determines the genuine degree-`q` monomial model. -/
theorem eval_top_of_matches {f : ℝ → ℝ} {q K k : ℕ} {ε t : ℝ}
    (hq : 0 < q) (h : MatchesJets f q ε K) (hk : k ≤ K) :
    TaylorModel.eval f q (point ε k) t = value q ε K k - ε * weight K k * t ^ q := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv, Finset.sum_range_succ]
  have hlo : ∑ i ∈ Finset.range q, t ^ i * iteratedDeriv i f (point ε k) / i.factorial =
      value q ε K k := by
    have hh := eval_lower_of_matches (t := t) h hk (Nat.sub_lt hq (by omega : 0 < 1))
    rw [TaylorModel.eval_eq_sum_iteratedDeriv, Nat.sub_add_cancel hq] at hh
    exact hh
  rw [hlo, h k hk q le_rfl, jet_top hq]
  have hf : (q.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The actual lower-order model decrements vanish. -/
theorem decrement_lower_of_matches {f : ℝ → ℝ} {q K k p : ℕ} {ε t : ℝ}
    (h : MatchesJets f q ε K) (hk : k ≤ K) (hp : p < q) :
    TaylorModel.decrement f p (point ε k) t = 0 := by
  simp [TaylorModel.decrement, eval_lower_of_matches h hk hp]

/-- The actual top-order Taylor decrement is the prescribed monomial. -/
theorem decrement_top_of_matches {f : ℝ → ℝ} {q K k : ℕ} {ε t : ℝ}
    (hq : 0 < q) (h : MatchesJets f q ε K) (hk : k ≤ K) :
    TaylorModel.decrement f q (point ε k) t = ε * weight K k * t ^ q := by
  rw [TaylorModel.decrement, eval_top_of_matches hq h hk, eval_top_of_matches hq h hk]
  simp [zero_pow (Nat.ne_of_gt hq)]

/-- All genuine lower-order criticality measures vanish on nonnegative radii. -/
theorem criticality_lower_of_matches {f : ℝ → ℝ} {q K k p : ℕ} {ε δ : ℝ}
    (h : MatchesJets f q ε K) (hk : k ≤ K) (hp : p < q) (hδ : 0 ≤ δ) :
    TaylorModel.criticality f p (point ε k) δ = 0 := by
  apply (TaylorModel.criticality_eq_zero_iff f p (point ε k) hδ).2
  intro t ht
  rw [decrement_lower_of_matches h hk hp]

/-- The monomial's genuine criticality is attained at the positive endpoint,
including odd orders and the zero-radius case. -/
theorem criticality_top_of_matches {f : ℝ → ℝ} {q K k : ℕ} {ε δ : ℝ}
    (hq : 0 < q) (h : MatchesJets f q ε K) (hk : k ≤ K)
    (hc : 0 ≤ ε * weight K k) (hδ : 0 ≤ δ) :
    TaylorModel.criticality f q (point ε k) δ = ε * weight K k * δ ^ q := by
  apply le_antisymm
  · obtain ⟨t,ht,heq⟩ := TaylorModel.exists_decrement_eq_criticality f q (point ε k) hδ
    rw [← heq, decrement_top_of_matches hq h hk]
    apply mul_le_mul_of_nonneg_left _ hc
    calc
      t ^ q ≤ |t| ^ q := le_trans (le_abs_self _) (by rw [abs_pow])
      _ ≤ δ ^ q := pow_le_pow_left₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using ht) q
  · rw [← decrement_top_of_matches hq h hk (t := δ)]
    exact TaylorModel.decrement_le_criticality f q (point ε k) (by simp
      [Real.norm_eq_abs, abs_of_nonneg hδ])

/-- The actual initial Hermite polynomial for the prescribed jet is a constant
minus one monomial. -/
theorem initialPolynomial_eq {q : ℕ} (hq : 0 < q) (ε : ℝ) (K k : ℕ) :
    Hermite.initialPolynomial q (jet q ε K k) =
      Polynomial.C (value q ε K k) - Polynomial.C (ε * weight K k) * Polynomial.X ^ q := by
  open Polynomial in
  change ∑ i ∈ Finset.range (q + 1), C (jet q ε K k i / i.factorial) * (X - C 0) ^ i = _
  rw [Finset.sum_range_succ]
  have hlo : ∑ i ∈ Finset.range q, C (jet q ε K k i / i.factorial) * (X - C 0) ^ i =
      C (value q ε K k) := by
    rw [Finset.sum_eq_single 0]
    · simp [jet]
    · intro i hi hi0
      rw [jet_lower q ε K k (Nat.pos_of_ne_zero hi0) (Finset.mem_range.mp hi)]
      simp
    · simp [Nat.ne_of_gt hq]
  rw [hlo, jet_top hq]
  have hf : (q.factorial : ℝ) ≠ 0 := by positivity
  have hc : -(q.factorial : ℝ) * ε * weight K k / q.factorial = -(ε * weight K k) := by
    field_simp
  rw [hc]
  simp [sub_eq_add_neg]

/-- The positive derivatives of the actual initial Hermite polynomial have the
correct descending-factorial coefficient. -/
theorem initialPolynomial_derivative {q j : ℕ} (hq : 0 < q) (hj : 0 < j)
    (ε t : ℝ) (K k : ℕ) :
    (Polynomial.derivative^[j] (Hermite.initialPolynomial q (jet q ε K k))).eval t =
      -(q.descFactorial j : ℝ) * ε * weight K k * t ^ (q - j) := by
  rw [initialPolynomial_eq hq]
  simp only [Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_C hj,
    Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul,
    Polynomial.eval_sub, Polynomial.eval_zero, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- Descending factorial coefficients are bounded by the full factorial. -/
theorem descFactorial_le_factorial {q j : ℕ} (hj : j ≤ q) :
    q.descFactorial j ≤ q.factorial := by
  have hf := Nat.factorial_mul_descFactorial hj
  have hp := Nat.factorial_pos (q - j)
  nlinarith

/-- The corrected endpoint objective data have zero Taylor residual. -/
theorem objective_residual_zero {q : ℕ} (hq : 0 < q) (ε : ℝ) (K k : ℕ) :
    jet q ε K (k + 1) 0 -
      (Hermite.initialPolynomial q (jet q ε K k)).eval ε = 0 := by
  rw [initialPolynomial_eq hq]
  simp only [jet, ite_true, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, value_succ]
  rw [pow_succ]
  ring

/-- All endpoint Taylor residuals obey a uniform order-dependent bound. This
includes the highest-order residual, which is nonzero and proportional to `1/K`. -/
theorem endpoint_residual_bound {q : ℕ} (hq : 0 < q) {ε : ℝ}
    (hε : 0 < ε) {k j : ℕ} (hk : k < length q ε) (hj : j ≤ q) :
    |jet q ε (length q ε) (k + 1) j -
      (Polynomial.derivative^[j] (Hermite.initialPolynomial q (jet q ε (length q ε) k))).eval ε| ≤
      (2 * (q.factorial : ℝ)) * ε ^ (q - j + 1) := by
  by_cases hj0 : j = 0
  · subst j
    rw [Function.iterate_zero_apply, objective_residual_zero hq]
    simp only [abs_zero]
    positivity
  have hjp : 0 < j := Nat.pos_of_ne_zero hj0
  rw [initialPolynomial_derivative hq hjp]
  by_cases hjq : j = q
  · subst j
    rw [jet_top hq, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one,
      weight_succ]
    have heq : -(q.factorial : ℝ) * ε * (weight (length q ε) k - 1 / length q ε) -
        -(q.factorial : ℝ) * ε * weight (length q ε) k =
        (q.factorial : ℝ) * ε / length q ε := by ring
    rw [heq, abs_of_nonneg (by positivity)]
    have hK : (1 : ℝ) ≤ length q ε := by exact_mod_cast length_pos q hε
    have hd : (q.factorial : ℝ) * ε / length q ε ≤ (q.factorial : ℝ) * ε :=
      div_le_self (by positivity) hK
    simp only [zero_add, pow_one]
    nlinarith [show 0 ≤ (q.factorial : ℝ) * ε by positivity]
  · rw [jet_lower q ε (length q ε) (k + 1) hjp (by omega)]
    have hw := weight_mem_Icc (length_pos q hε) (Nat.le_of_lt hk)
    have hw1 : 1 ≤ weight (length q ε) k := hw.1
    have hd : (q.descFactorial j : ℝ) ≤ q.factorial := by
      exact_mod_cast descFactorial_le_factorial hj
    rw [zero_sub, abs_neg, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ (q.descFactorial j : ℝ)), abs_of_pos hε,
      abs_of_nonneg (by linarith : 0 ≤ weight (length q ε) k),
      abs_of_nonneg (by positivity : 0 ≤ ε ^ (q - j))]
    calc
      (q.descFactorial j : ℝ) * ε * weight (length q ε) k * ε ^ (q - j) ≤
        (q.factorial : ℝ) * ε * 2 * ε ^ (q - j) :=
          mul_le_mul_of_nonneg_right (mul_le_mul
            (mul_le_mul_of_nonneg_right hd hε.le) hw.2 (by linarith [hw.1]) (by positivity))
            (by positivity)
      _ = (2 * (q.factorial : ℝ)) * ε ^ (q - j + 1) := by rw [pow_succ]; ring

/-- An approximate maximizer whose decrease is exactly the prescribed fraction
of the largest model decrease. This also makes the final computed test an equality. -/
noncomputable def direction (q : ℕ) (ε ζ : ℝ) : ℝ := ε * ζ ^ ((q : ℝ)⁻¹)

/-- The approximate maximizer stays inside the optimality ball. -/
theorem direction_norm_le {q : ℕ} {ε ζ : ℝ} (hε : 0 ≤ ε)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) : ‖direction q ε ζ‖ ≤ ε := by
  have hroot := Real.rpow_nonneg hζ ((q : ℝ)⁻¹)
  have hroot1 := Real.rpow_le_one hζ hζ1 (show 0 ≤ (q : ℝ)⁻¹ by positivity)
  rw [direction, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε hroot)]
  nlinarith

/-- The `q`th power of the approximate maximizer scales the boundary power by `ζ`. -/
theorem direction_pow {q : ℕ} (hq : 0 < q) (ε : ℝ) {ζ : ℝ} (hζ : 0 ≤ ζ) :
    direction q ε ζ ^ q = ε ^ q * ζ := by
  rw [direction, mul_pow, Real.rpow_inv_natCast_pow hζ (Nat.ne_of_gt hq)]

/-- The selected model index represents order `q`. -/
def topIndex {q : ℕ} (hq : 0 < q) : Fin q := ⟨q - 1, by omega⟩

/-- The final positive-order index represents the full criticality order. -/
@[simp] theorem modelOrder_topIndex {q : ℕ} (hq : 0 < q) : modelOrder (topIndex hq) = q := by
  simp only [modelOrder, topIndex]
  omega

/-- Earlier indices have strictly smaller Taylor order. -/
theorem modelOrder_lt_of_lt_topIndex {q : ℕ} (hq : 0 < q) {a : Fin q}
    (ha : a < topIndex hq) : modelOrder a < q := by
  have h := Fin.lt_def.mp ha
  dsimp [topIndex, modelOrder] at *
  omega

/-- The checked oracle property is proved from actual monomial Taylor models. -/
theorem checkedOracle_of_matches {q : ℕ} {f : ℝ → ℝ} (P : Parameters q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : P.theta = 1)
    (h : MatchesJets f q ε (length q ε)) {k : ℕ} (hk : k ≤ length q ε) :
    CheckedOracle f P (point ε k) ε (fun _ => direction q ε P.zeta) := by
  have hδ : optimalityRadius P ε = ε := by simp [optimalityRadius, hθ, min_eq_left hε1]
  intro a
  rw [hδ]
  refine ⟨direction_norm_le hε.le P.zeta_pos.le P.zeta_le_one, ?_⟩
  by_cases ha : modelOrder a = q
  · rw [ha, criticality_top_of_matches P.order_pos h hk
        (mul_nonneg hε.le (by linarith [(weight_mem_Icc (length_pos q hε) hk).1])) hε.le,
      decrement_top_of_matches P.order_pos h hk, direction_pow P.order_pos ε P.zeta_pos.le]
    exact le_of_eq (by ring)
  · have hal : modelOrder a < q := lt_of_le_of_ne (modelOrder_le a) ha
    rw [criticality_lower_of_matches h hk hal hε.le, decrement_lower_of_matches h hk hal]
    simp

/-- The exact factorial-normalized stopping threshold at any order. -/
theorem threshold_eq {q : ℕ} (P : Parameters q) {ε : ℝ} (hε1 : ε ≤ 1)
    (hθ : P.theta = 1) (hacc : ∀ a, P.accuracy a = ((modelOrder a).factorial : ℝ) * ε)
    (a : Fin q) :
    P.zeta * P.accuracy a * optimalityRadius P ε ^ modelOrder a / (modelOrder a).factorial =
      P.zeta * ε * ε ^ modelOrder a := by
  rw [hacc, optimalityRadius_eq_radius P (by simpa [hθ] using hε1)]
  have hf : ((modelOrder a).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Every preterminal grid segment is an actual legal trust-region trial.
No update, acceptance, decrease, or iterate claim is assumed in the jet interface. -/
theorem trial_of_matches {q : ℕ} {f : ℝ → ℝ} (P : Parameters q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : P.theta = 1)
    (hmax : ε ≤ P.radiusMax)
    (hacc : ∀ a, P.accuracy a = ((modelOrder a).factorial : ℝ) * ε)
    (h : MatchesJets f q ε (length q ε)) {k : ℕ} (hk : k < length q ε) :
    Trial f P (point ε k) ε (fun _ => direction q ε P.zeta) (topIndex P.order_pos)
      ε (point ε (k + 1)) ε 1 := by
  have hζ := P.zeta_pos
  have hkle := Nat.le_of_lt hk
  have hδ : optimalityRadius P ε = ε := by simp [optimalityRadius, hθ, min_eq_left hε1]
  have hw := weight_mem_Icc (length_pos q hε) hkle
  have hw1 : 1 < weight (length q ε) k := one_lt_weight hk
  have hc : 0 < ε * weight (length q ε) k := mul_pos hε (by linarith)
  have hη : P.eta1 ≤ 1 := P.eta1_le_eta2.trans P.eta2_lt_one.le
  have hη2 : P.eta2 ≤ 1 := P.eta2_lt_one.le
  have hcheck := checkedOracle_of_matches P hε hε1 hθ h hkle
  refine ⟨hε, fun a _ => (hcheck a).1, fun a _ => (hcheck a).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [decrement_lower_of_matches h hkle (modelOrder_lt_of_lt_topIndex P.order_pos ha),
      threshold_eq P hε1 hθ hacc]
    positivity
  · rw [threshold_eq P hε1 hθ hacc, modelOrder_topIndex,
      decrement_top_of_matches P.order_pos h hkle, direction_pow P.order_pos ε P.zeta_pos.le]
    have hp : 0 < P.zeta * ε * ε ^ q := by positivity
    nlinarith
  · simp [Real.norm_eq_abs, abs_of_pos hε]
  · rw [modelOrder_topIndex, decrement_top_of_matches P.order_pos h hkle,
      decrement_top_of_matches P.order_pos h hkle, direction_pow P.order_pos ε P.zeta_pos.le]
    nlinarith [mul_nonneg (mul_nonneg hc.le (pow_nonneg hε.le q)) (sub_nonneg.mpr P.zeta_le_one)]
  · have hfv (i : ℕ) (hi : i ≤ length q ε) : f (point ε i) = value q ε (length q ε) i := by
      simpa [jet] using h i hi 0 (by omega)
    rw [modelOrder_topIndex, decrement_top_of_matches P.order_pos h hkle]
    rw [← point_succ, hfv k hkle, hfv (k + 1) (by omega), value_succ]
    have hden : ε * weight (length q ε) k * ε ^ q ≠ 0 := by positivity
    have heq : value q ε (length q ε) k -
        (value q ε (length q ε) k - ε ^ (q + 1) * weight (length q ε) k) =
        ε * weight (length q ε) k * ε ^ q := by rw [pow_succ]; ring
    rw [heq, div_self hden]
  · simp [hη, point_succ]
  · simp only [hη2, ite_true, mem_Icc, le_refl, true_and, le_min_iff]
    exact ⟨hmax, by nlinarith [P.one_le_gamma3]⟩

/-- The prescribed finite sequence is a genuine nonterminal algorithm run. -/
theorem run_of_matches {q : ℕ} {f : ℝ → ℝ} (P : Parameters q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : P.theta = 1)
    (hmax : ε ≤ P.radiusMax)
    (hacc : ∀ a, P.accuracy a = ((modelOrder a).factorial : ℝ) * ε)
    (h : MatchesJets f q ε (length q ε)) :
    Run f P (point ε) (fun _ => ε) (fun _ _ => direction q ε P.zeta)
      (fun _ => topIndex P.order_pos) (fun _ => ε) (fun _ => 1) (length q ε) :=
  ⟨hε, hmax, fun _ hk => trial_of_matches P hε hε1 hθ hmax hacc h hk⟩

/-- All computed tests pass at the final grid point. -/
theorem testsPass_last_of_matches {q : ℕ} {f : ℝ → ℝ} (P : Parameters q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : P.theta = 1)
    (hacc : ∀ a, P.accuracy a = ((modelOrder a).factorial : ℝ) * ε)
    (h : MatchesJets f q ε (length q ε)) :
    TestsPass f P (point ε (length q ε)) ε (fun _ => direction q ε P.zeta) := by
  have hζ := P.zeta_pos
  intro a
  rw [threshold_eq P hε1 hθ hacc]
  by_cases ha : modelOrder a = q
  · rw [ha, decrement_top_of_matches P.order_pos h le_rfl,
      direction_pow P.order_pos ε P.zeta_pos.le, weight_last (length_pos q hε)]
    exact le_of_eq (by ring)
  · rw [decrement_lower_of_matches h le_rfl (lt_of_le_of_ne (modelOrder_le a) ha)]
    positivity

/-- No earlier grid point passes every actual computed test. -/
theorem not_testsPass_of_matches {q : ℕ} {f : ℝ → ℝ} (P : Parameters q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : P.theta = 1)
    (hacc : ∀ a, P.accuracy a = ((modelOrder a).factorial : ℝ) * ε)
    (h : MatchesJets f q ε (length q ε)) {k : ℕ} (hk : k < length q ε) :
    ¬TestsPass f P (point ε k) ε (fun _ => direction q ε P.zeta) := by
  have hζ := P.zeta_pos
  intro ht
  have hh := ht (topIndex P.order_pos)
  rw [threshold_eq P hε1 hθ hacc, modelOrder_topIndex,
    decrement_top_of_matches P.order_pos h (Nat.le_of_lt hk),
    direction_pow P.order_pos ε P.zeta_pos.le] at hh
  have hp : 0 < P.zeta * ε * ε ^ q := by positivity
  have hw := one_lt_weight hk
  nlinarith

/-- True criticality tests hold at the final point and fail at every earlier
point, independently of the approximation fraction used by the checked oracle. -/
theorem true_first_stopping_index {q : ℕ} {f : ℝ → ℝ} (P : Parameters q)
    {ε : ℝ} (hε : 0 < ε)
    (hacc : ∀ a, P.accuracy a = ((modelOrder a).factorial : ℝ) * ε)
    (h : MatchesJets f q ε (length q ε)) :
    (∀ k < length q ε, ¬∀ a, TaylorModel.criticality f (modelOrder a) (point ε k) ε ≤
      P.accuracy a * ε ^ modelOrder a / (modelOrder a).factorial) ∧
    (∀ a, TaylorModel.criticality f (modelOrder a) (point ε (length q ε)) ε ≤
      P.accuracy a * ε ^ modelOrder a / (modelOrder a).factorial) := by
  have hthr (a : Fin q) : P.accuracy a * ε ^ modelOrder a / (modelOrder a).factorial =
      ε * ε ^ modelOrder a := by
    rw [hacc]
    have hf : ((modelOrder a).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have hc (k : ℕ) (hk : k ≤ length q ε) : 0 ≤ ε * weight (length q ε) k :=
    mul_nonneg hε.le (by linarith [(weight_mem_Icc (length_pos q hε) hk).1])
  constructor
  · intro k hk ht
    have hh := ht (topIndex P.order_pos)
    rw [hthr, modelOrder_topIndex,
      criticality_top_of_matches P.order_pos h hk.le (hc k hk.le) hε.le] at hh
    have hp : 0 < ε * ε ^ q := by positivity
    have hw := one_lt_weight hk
    nlinarith
  · intro a
    rw [hthr]
    by_cases ha : modelOrder a = q
    · rw [ha, criticality_top_of_matches P.order_pos h le_rfl (hc _ le_rfl) hε.le,
        weight_last (length_pos q hε)]
      simp
    · rw [criticality_lower_of_matches h le_rfl (lt_of_le_of_ne (modelOrder_le a) ha) hε.le]
      positivity

/-- At every preterminal point the genuine order-`q` measure fails its
accuracy requirement for every positive radius, including radii other than the
algorithm's current optimality radius. -/
theorem not_approximate_at_any_radius {q : ℕ} {f : ℝ → ℝ} (P : Parameters q)
    {ε : ℝ} (hε : 0 < ε)
    (hacc : ∀ a, P.accuracy a = ((modelOrder a).factorial : ℝ) * ε)
    (h : MatchesJets f q ε (length q ε)) {k : ℕ} (hk : k < length q ε)
    {δ : ℝ} (hδ : 0 < δ) :
    ¬∀ a, TaylorModel.criticality f (modelOrder a) (point ε k) δ ≤
      P.accuracy a * δ ^ modelOrder a / (modelOrder a).factorial := by
  intro ht
  have hh := ht (topIndex P.order_pos)
  have hc : 0 ≤ ε * weight (length q ε) k :=
    mul_nonneg hε.le (by linarith [(weight_mem_Icc (length_pos q hε) hk.le).1])
  rw [hacc, modelOrder_topIndex,
    criticality_top_of_matches P.order_pos h hk.le hc hδ.le] at hh
  have hf : (q.factorial : ℝ) ≠ 0 := by positivity
  have heq : (q.factorial : ℝ) * ε * δ ^ q / q.factorial = ε * δ ^ q := by field_simp
  rw [heq] at hh
  have hp : 0 < ε * δ ^ q := by positivity
  have hw := one_lt_weight hk
  nlinarith

/-- Every trial succeeds, so the actual initialized counts are exactly `K+1`. -/
theorem initialized_counts {q : ℕ} (P : Parameters q) (K : ℕ) :
    functionEvaluations K = K + 1 ∧ derivativeEvaluations P (fun _ => 1) K = K + 1 := by
  have hη : P.eta1 ≤ 1 := P.eta1_le_eta2.trans P.eta2_lt_one.le
  simp [functionEvaluations, derivativeEvaluations,
    EvaluationComplexity.successfulIterations, hη]

/-- Each initialized evaluation count exceeds the inverse-accuracy trial lower bound. -/
theorem initialized_counts_lower {q : ℕ} (P : Parameters q) (ε : ℝ) :
    1 / ε ^ (q + 1) < (functionEvaluations (length q ε) : ℝ) ∧
      1 / ε ^ (q + 1) < (derivativeEvaluations P (fun _ => 1) (length q ε) : ℝ) := by
  obtain ⟨hF,hD⟩ := initialized_counts P (length q ε)
  rw [hF,hD]
  have hc := inverse_pow_le_length q ε
  push_cast
  constructor <;> linarith

/-- One fixed order-dependent interpolation cube controls the grid, every jet,
and all genuine initial-polynomial endpoint residuals. -/
theorem uniform_data {q : ℕ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let κ := max 4 (2 * (q.factorial : ℝ))
    0 < κ ∧ 0 < length q ε ∧ StrictMono (point ε) ∧ ε ≤ κ ∧
      (∀ k ≤ length q ε, ∀ j ≤ q, |jet q ε (length q ε) k j| ≤ κ) ∧
      (∀ k < length q ε, ∀ j ≤ q,
        |jet q ε (length q ε) (k + 1) j -
          (Polynomial.derivative^[j] (Hermite.initialPolynomial q (jet q ε (length q
            ε) k))).eval ε| ≤
          κ * ε ^ (q - j + 1)) := by
  dsimp only
  have hκ : 4 ≤ max 4 (2 * (q.factorial : ℝ)) := le_max_left _ _
  refine ⟨by linarith, length_pos q hε, point_strictMono hε, by linarith, ?_, ?_⟩
  · intro k hk j _
    exact jet_bound hq hε hε1 hk
  · intro k hk j hj
    exact (endpoint_residual_bound hq hε hk hj).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- The source accuracy restriction implies `ε≤1`. -/
theorem accuracy_le_one {q : ℕ} {ε : ℝ} (hεq : ε ≤ 1 / (q.factorial : ℝ)) : ε ≤ 1 := by
  have hf : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hi : 1 / (q.factorial : ℝ) ≤ 1 := (div_le_one (by positivity)).2 hf
  exact hεq.trans hi

/-- The factorial-scaled accuracies lie in the required unit interval. -/
theorem factorial_accuracy_le_one {q : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hεq : ε ≤ 1 / (q.factorial : ℝ)) (a : Fin q) :
    ((modelOrder a).factorial : ℝ) * ε ≤ 1 := by
  have hm : ((modelOrder a).factorial : ℝ) ≤ q.factorial := by
    exact_mod_cast Nat.factorial_le (modelOrder_le a)
  calc
    ((modelOrder a).factorial : ℝ) * ε ≤ (q.factorial : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hm hε
    _ ≤ (q.factorial : ℝ) * (1 / (q.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hεq (by positivity)
    _ = 1 := by field_simp

/-- A fixed legal choice of algorithm parameters, with arbitrary permitted
approximation fraction and enlargement endpoint `γ₃=1`. Only the accuracies vary. -/
noncomputable def parameters {q : ℕ} (hq : 0 < q) {ε ζ : ℝ} (hε : 0 < ε)
    (hεq : ε ≤ 1 / (q.factorial : ℝ)) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) : Parameters q where
  order_pos := hq
  accuracy a := ((modelOrder a).factorial : ℝ) * ε
  accuracy_pos a := by positivity
  accuracy_le_one := factorial_accuracy_le_one hε.le hεq
  zeta := ζ
  zeta_pos := hζ
  zeta_le_one := hζ1
  theta := 1
  theta_pos := by norm_num
  theta_le_one := le_rfl
  min_accuracy_le_theta := ⟨⟨0,hq⟩, by simpa [modelOrder] using accuracy_le_one hεq⟩
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 4
  gamma2 := 1 / 2
  gamma3 := 1
  radiusMax := 1
  eta1_pos := by norm_num
  eta1_le_eta2 := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_le_gamma2 := by norm_num
  gamma2_lt_one := by norm_num
  one_le_gamma3 := le_rfl

/-- An actual function with the prescribed scalar derivatives realizes the
whole finite run and the exact first stopping index, for fixed legal settings. -/
theorem execution_of_matches {q : ℕ} {f : ℝ → ℝ} (hq : 0 < q) {ε ζ : ℝ}
    (hε : 0 < ε) (hεq : ε ≤ 1 / (q.factorial : ℝ)) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (h : MatchesJets f q ε (length q ε)) :
    let P := parameters hq hε hεq hζ hζ1
    Run f P (point ε) (fun _ => ε) (fun _ _ => direction q ε ζ)
      (fun _ => topIndex hq) (fun _ => ε) (fun _ => 1) (length q ε) ∧
    (∀ k < length q ε, ¬TestsPass f P (point ε k) ε (fun _ => direction q ε ζ)) ∧
    TestsPass f P (point ε (length q ε)) ε (fun _ => direction q ε ζ) ∧
    (∀ k ≤ length q ε, CheckedOracle f P (point ε k) ε (fun _ => direction q ε ζ)) ∧
    functionEvaluations (length q ε) = length q ε + 1 ∧
    derivativeEvaluations P (fun _ => 1) (length q ε) = length q ε + 1 := by
  let P := parameters hq hε hεq hζ hζ1
  have hε1 := accuracy_le_one hεq
  have hacc : ∀ a, P.accuracy a = ((modelOrder a).factorial : ℝ) * ε := fun _ => rfl
  refine ⟨run_of_matches P hε hε1 rfl hε1 hacc h,
    fun _ hk => not_testsPass_of_matches P hε hε1 rfl hacc h hk,
    testsPass_last_of_matches P hε hε1 rfl hacc h,
    fun _ hk => checkedOracle_of_matches P hε hε1 rfl h hk, ?_⟩
  exact initialized_counts P (length q ε)

/-- A globally bounded interpolant is bounded below, with an initial gap
independent of the accuracy and of the number of interpolation points. -/
theorem initial_objective_gap {f : ℝ → ℝ} {q : ℕ} {ε B : ℝ}
    (h : MatchesJets f q ε (length q ε)) (hB : ∀ y, |f y| ≤ B) :
    (∀ y, -B ≤ f y) ∧ f 0 - (-B) = 4 + B := by
  have hv := h.value_eq (Nat.zero_le (length q ε))
  simp only [point_zero, value_zero] at hv
  exact ⟨fun y => (abs_le.mp (hB y)).1, by rw [hv]; ring⟩

end HighOrderTrustRegion.Sharpness
