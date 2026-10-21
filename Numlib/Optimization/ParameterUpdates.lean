import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith

/-!
# Multiplicative parameter updates

Radius contraction in trust-region methods and parameter expansion in regularization methods
are reciprocal versions of the same counting argument. This file isolates the scalar argument
from the objective, model and step computation. Counts refer to `range n`, so the endpoint
parameter is the value after precisely those `n` updates.

The motivating results are Cartis–Gould–Toint, *Evaluation Complexity of Algorithms for
Nonconvex Optimization* (2022), Lemmas 2.3.1 and 2.4.1.
-/

noncomputable section

namespace Optimization.ParameterUpdates

open Classical in
/-- The number of successful iterations before the endpoint `n`. -/
def successCount (success : ℕ → Prop) (n : ℕ) : ℕ :=
  ((Finset.range n).filter success).card

open Classical in
/-- The number of unsuccessful iterations before the endpoint `n`. -/
def unsuccessfulCount (success : ℕ → Prop) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun k => ¬ success k).card

/-- Every iteration before the endpoint is either successful or unsuccessful. -/
theorem successCount_add_unsuccessfulCount (success : ℕ → Prop) (n : ℕ) :
    successCount success n + unsuccessfulCount success n = n := by
  classical
  simpa [successCount, unsuccessfulCount] using
    Finset.card_filter_add_card_filter_not (s := Finset.range n) success

/-- A positive parameter sequence with a branch-dependent multiplicative lower update bound.
Upper update bounds are obtained by applying this interface to reciprocal parameters. -/
structure UpdateBounds (u : ℕ → ℝ) (success : ℕ → Prop) (a b : ℝ) : Prop where
  /-- Parameters remain positive. -/
  pos : ∀ k, 0 < u k
  /-- The lower update bound at successful iterations. -/
  on_success : ∀ k, success k → a * u k ≤ u (k + 1)
  /-- The lower update bound at unsuccessful iterations. -/
  on_unsuccessful : ∀ k, ¬ success k → b * u k ≤ u (k + 1)

/-- Multiplicative update bounds become an additive budget in logarithmic coordinates. -/
theorem UpdateBounds.log_budget {u : ℕ → ℝ} {success : ℕ → Prop} {a b : ℝ}
    (h : UpdateBounds u success a b) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (successCount success n : ℝ) * Real.log a +
      (unsuccessfulCount success n : ℝ) * Real.log b ≤ Real.log (u n / u 0) := by
  classical
  have hstep : ∀ k, (if success k then Real.log a else Real.log b) ≤
      Real.log (u (k + 1)) - Real.log (u k) := by
    intro k
    by_cases hk : success k
    · rw [ite_eq_left hk]
      have hh := Real.log_le_log (mul_pos ha (h.pos k)) (h.on_success k hk)
      rw [Real.log_mul ha.ne' (h.pos k).ne'] at hh
      linarith
    · rw [ite_eq_right hk]
      have hh := Real.log_le_log (mul_pos hb (h.pos k)) (h.on_unsuccessful k hk)
      rw [Real.log_mul hb.ne' (h.pos k).ne'] at hh
      linarith
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun k _ => hstep k)
  rw [show (∑ k ∈ Finset.range n, (Real.log (u (k + 1)) - Real.log (u k))) =
    Real.log (u n) - Real.log (u 0) from Finset.sum_range_sub (fun k => Real.log (u k)) n] at hsum
  rw [Real.log_div (h.pos n).ne' (h.pos 0).ne']
  simpa [Finset.sum_ite, successCount, unsuccessfulCount] using hsum

/-- When unsuccessful iterations expand the parameter, a terminal upper bound limits how
many of them can occur. The successful-iteration factor may be any positive number. -/
theorem unsuccessful_count_le_of_upper_bound {u : ℕ → ℝ} {success : ℕ → Prop} {a b M : ℝ}
    (h : UpdateBounds u success a b) (ha : 0 < a) (hb : 0 < b) (n : ℕ) (hM : u n ≤ M) :
    (unsuccessfulCount success n : ℝ) * Real.log b ≤
      -(successCount success n : ℝ) * Real.log a + Real.log (M / u 0) := by
  have hlog := h.log_budget ha hb n
  have hratio : u n / u 0 ≤ M / u 0 := div_le_div_of_nonneg_right hM (h.pos 0).le
  have hMlog := Real.log_le_log (div_pos (h.pos n) (h.pos 0)) hratio
  linarith

/-- The reciprocal form of the logarithmic budget: contractions at unsuccessful iterations
are limited by a lower bound on the terminal parameter. -/
theorem unsuccessful_count_le_of_lower_bound {u : ℕ → ℝ} {success : ℕ → Prop} {a b m : ℝ}
    (hpos : ∀ k, 0 < u k) (ha : 0 < a) (hb : 0 < b)
    (hsuccess : ∀ k, success k → u (k + 1) ≤ a * u k)
    (hunsuccessful : ∀ k, ¬ success k → u (k + 1) ≤ b * u k)
    (n : ℕ) (hm : 0 < m) (hmin : m ≤ u n) :
    (unsuccessfulCount success n : ℝ) * (-Real.log b) ≤
      (successCount success n : ℝ) * Real.log a + Real.log (u 0 / m) := by
  have hinv : UpdateBounds (fun k => (u k)⁻¹) success a⁻¹ b⁻¹ := by
    refine ⟨fun k => inv_pos.mpr (hpos k), ?_, ?_⟩
    · intro k hk
      simpa [one_div, mul_inv, mul_comm] using
        one_div_le_one_div_of_le (hpos (k + 1)) (hsuccess k hk)
    · intro k hk
      simpa [one_div, mul_inv, mul_comm] using
        one_div_le_one_div_of_le (hpos (k + 1)) (hunsuccessful k hk)
  have hh := unsuccessful_count_le_of_upper_bound hinv (inv_pos.mpr ha) (inv_pos.mpr hb) n
    (M := m⁻¹) (by simpa only [one_div] using one_div_le_one_div_of_le hm hmin)
  have heq : m⁻¹ / (u 0)⁻¹ = u 0 / m := by
    rw [div_inv_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq] at hh
  simpa only [Real.log_inv, mul_neg, neg_mul, neg_neg] using hh

/-- With expansion at unsuccessful iterations, all iterations are bounded in terms of the
successful count and the logarithmic range of the parameter. -/
theorem total_count_le_of_upper_bound {u : ℕ → ℝ} {success : ℕ → Prop} {a b M : ℝ}
    (h : UpdateBounds u success a b) (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : 1 < b)
    (n : ℕ) (hM : u n ≤ M) :
    (n : ℝ) ≤ (successCount success n : ℝ) * (1 + |Real.log a| / Real.log b) +
      Real.log (M / u 0) / Real.log b := by
  have hh := unsuccessful_count_le_of_upper_bound h ha.1 (zero_lt_one.trans hb) n hM
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hsplit : (successCount success n : ℝ) + (unsuccessfulCount success n : ℝ) = n := by
    exact_mod_cast successCount_add_unsuccessfulCount success n
  rw [abs_of_neg (Real.log_neg ha.1 ha.2)]
  calc
    (n : ℝ) ≤ ((successCount success n : ℝ) * (Real.log b - Real.log a) +
        Real.log (M / u 0)) / Real.log b := (le_div_iff₀ hlogb).mpr (by nlinarith)
    _ = _ := by field_simp; ring

/-- With contraction at unsuccessful iterations, a terminal lower bound similarly controls
the total count. This exact signed logarithmic bound can be weakened using absolute values. -/
theorem total_count_le_of_lower_bound {u : ℕ → ℝ} {success : ℕ → Prop} {a b m : ℝ}
    (hpos : ∀ k, 0 < u k) (ha : 0 < a) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hsuccess : ∀ k, success k → u (k + 1) ≤ a * u k)
    (hunsuccessful : ∀ k, ¬ success k → u (k + 1) ≤ b * u k)
    (n : ℕ) (hm : 0 < m) (hmin : m ≤ u n) :
    (n : ℝ) ≤ (successCount success n : ℝ) * (1 + Real.log a / |Real.log b|) +
      Real.log (u 0 / m) / |Real.log b| := by
  have hh := unsuccessful_count_le_of_lower_bound hpos ha hb.1 hsuccess hunsuccessful n hm hmin
  have hlogb : 0 < -Real.log b := neg_pos.mpr (Real.log_neg hb.1 hb.2)
  have hsplit : (successCount success n : ℝ) + (unsuccessfulCount success n : ℝ) = n := by
    exact_mod_cast successCount_add_unsuccessfulCount success n
  rw [abs_of_neg (Real.log_neg hb.1 hb.2)]
  calc
    (n : ℝ) ≤ ((successCount success n : ℝ) * (-Real.log b + Real.log a) +
        Real.log (u 0 / m)) / (-Real.log b) := (le_div_iff₀ hlogb).mpr (by nlinarith)
    _ = _ := by field_simp [(Real.log_neg hb.1 hb.2).ne]; ring

/-- If the parameter cannot increase above a threshold, and increases by at most `γ` below
it, every value is bounded by the larger of its initial value and `γ * threshold`. -/
theorem le_max_of_nonincrease_above {u : ℕ → ℝ} {threshold γ : ℝ} (hγ : 0 ≤ γ)
    (habove : ∀ k, threshold ≤ u k → u (k + 1) ≤ u k)
    (hbelow : ∀ k, u k < threshold → u (k + 1) ≤ γ * u k) (n : ℕ) :
    u n ≤ max (u 0) (γ * threshold) := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
    by_cases hn : threshold ≤ u n
    · exact (habove n hn).trans ih
    · exact (hbelow n (lt_of_not_ge hn)).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_ge hn) hγ).trans (le_max_right _ _))

/-- The lower-bound counterpart: below a threshold the parameter cannot decrease; above it
each decrease preserves at least the fraction `γ`. -/
theorem min_le_of_nondecrease_below {u : ℕ → ℝ} {threshold γ : ℝ} (hγ : 0 ≤ γ)
    (hbelow : ∀ k, u k ≤ threshold → u k ≤ u (k + 1))
    (habove : ∀ k, threshold < u k → γ * u k ≤ u (k + 1)) (n : ℕ) :
    min (u 0) (γ * threshold) ≤ u n := by
  induction n with
  | zero => exact min_le_left _ _
  | succ n ih =>
    by_cases hn : u n ≤ threshold
    · exact ih.trans (hbelow n hn)
    · exact ((min_le_right _ _).trans
        (mul_le_mul_of_nonneg_left (le_of_not_ge hn) hγ)).trans (habove n (lt_of_not_ge hn))

end Optimization.ParameterUpdates

namespace Optimization.ParameterUpdates

/-- Ordered constants for three-way regularization-parameter updates. -/
structure RegularizationParameters where
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  sigmaMin : ℝ
  eta1_pos : 0 < eta1
  eta_le : eta1 ≤ eta2
  eta2_lt_one : eta2 < 1
  gamma1_pos : 0 < gamma1
  gamma1_lt_one : gamma1 < 1
  one_lt_gamma2 : 1 < gamma2
  gamma2_lt_gamma3 : gamma2 < gamma3
  sigmaMin_pos : 0 < sigmaMin

/-- The parameter mechanism common to adaptive regularization at every model order. -/
structure RegularizationUpdates (p : RegularizationParameters) (rho sigma : ℕ → ℝ) : Prop where
  initial_lower : p.sigmaMin ≤ sigma 0
  update : ∀ k, if p.eta2 ≤ rho k
    then sigma (k + 1) ∈ Set.Icc (max p.sigmaMin (p.gamma1 * sigma k)) (sigma k)
    else if p.eta1 ≤ rho k
    then sigma (k + 1) ∈ Set.Icc (sigma k) (p.gamma2 * sigma k)
    else sigma (k + 1) ∈ Set.Icc (p.gamma2 * sigma k) (p.gamma3 * sigma k)

variable {p : RegularizationParameters} {rho sigma : ℕ → ℝ}

/-- Every interval update preserves the positive parameter floor. -/
theorem RegularizationUpdates.lower (h : RegularizationUpdates p rho sigma) (k : ℕ) :
    p.sigmaMin ≤ sigma k := by
  induction k with
  | zero => exact h.initial_lower
  | succ k ih =>
    have hu := h.update k
    split_ifs at hu
    · exact (le_max_left _ _).trans hu.1
    · exact ih.trans hu.1
    · exact ih.trans ((le_mul_of_one_le_left (p.sigmaMin_pos.le.trans ih)
        p.one_lt_gamma2.le).trans hu.1)

/-- Every regularization parameter is positive. -/
theorem RegularizationUpdates.pos (h : RegularizationUpdates p rho sigma) (k : ℕ) :
    0 < sigma k := p.sigmaMin_pos.trans_le (h.lower k)

/-- The branch intervals imply the common multiplicative counting interface. -/
theorem RegularizationUpdates.updateBounds (h : RegularizationUpdates p rho sigma) :
    UpdateBounds sigma (fun k => p.eta1 ≤ rho k) p.gamma1 p.gamma2 := by
  refine ⟨h.pos, ?_, ?_⟩
  · intro k hk
    have hu := h.update k
    split_ifs at hu
    · exact (le_max_right _ _).trans hu.1
    · exact (mul_le_of_le_one_left (h.pos k).le p.gamma1_lt_one.le).trans hu.1
  · intro k hk
    have hn : ¬p.eta2 ≤ rho k := fun h2 => hk (p.eta_le.trans h2)
    have hu := h.update k
    simp only [ite_eq_right hn, ite_eq_right hk] at hu
    exact hu.1

/-- Total trials are bounded in terms of accepted trials and a terminal parameter upper bound. -/
theorem RegularizationUpdates.total_count_le (h : RegularizationUpdates p rho sigma)
    (n : ℕ) {M : ℝ} (hM : sigma n ≤ M) :
    (n : ℝ) ≤ (successCount (fun k => p.eta1 ≤ rho k) n : ℝ) *
      (1 + |Real.log p.gamma1| / Real.log p.gamma2) +
      Real.log (M / sigma 0) / Real.log p.gamma2 :=
  total_count_le_of_upper_bound h.updateBounds
    ⟨p.gamma1_pos, p.gamma1_lt_one⟩ p.one_lt_gamma2 n hM

/-- If large parameters force very successful trials, every parameter is uniformly bounded. -/
theorem RegularizationUpdates.upper (h : RegularizationUpdates p rho sigma) {T : ℝ}
    (hlarge : ∀ k, T ≤ sigma k → p.eta2 ≤ rho k) (n : ℕ) :
    sigma n ≤ max (sigma 0) (p.gamma3 * T) := by
  apply le_max_of_nonincrease_above
    (zero_lt_one.trans (p.one_lt_gamma2.trans p.gamma2_lt_gamma3)).le
  · intro k hk
    have hu := h.update k
    simp only [ite_eq_left (hlarge k hk)] at hu
    exact hu.2
  · intro k _
    have hu := h.update k
    split_ifs at hu
    · exact hu.2.trans (le_mul_of_one_le_left (h.pos k).le
        (p.one_lt_gamma2.trans p.gamma2_lt_gamma3).le)
    · exact hu.2.trans (mul_le_mul_of_nonneg_right p.gamma2_lt_gamma3.le (h.pos k).le)
    · exact hu.2

end Optimization.ParameterUpdates
