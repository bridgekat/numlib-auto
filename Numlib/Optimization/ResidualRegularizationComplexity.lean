import Numlib.Optimization.ResidualRegularizationQuality
import Numlib.Optimization.ResidualPowerDecrease

/-!
# Residual-root evaluation complexity

The enabled tests retain their individual tolerance powers. Accepted objective decrease
bounds the actual normalized successor derivatives and then the dyadic residual-root
potential. Rejected trials preserve the iterate and reuse its residual derivatives.
-/

noncomputable section
namespace Optimization.ResidualRegularization
open HigherOrderRegularization ParameterUpdates

/-- Minimum of the residual threshold and precisely the enabled derivative thresholds. -/
def enabledMin (q : ℕ) (b : ℝ) (a : Fin 3 → ℝ) : ℝ :=
  min b (min (a 0) (if 2 ≤ q then min (a 1) (if 3 ≤ q then a 2 else a 1) else a 0))

/-- Maximum of the residual contribution and precisely the enabled derivative contributions. -/
def enabledMax (q : ℕ) (b : ℝ) (a : Fin 3 → ℝ) : ℝ :=
  max b (max (a 0) (if 2 ≤ q then max (a 1) (if 3 ≤ q then a 2 else a 1) else a 0))

/-- The residual entry bounds the enabled minimum. -/
theorem enabledMin_le_residual (q : ℕ) (b : ℝ) (a : Fin 3 → ℝ) : enabledMin q b a ≤ b :=
  min_le_left _ _

/-- Each enabled derivative entry bounds the enabled minimum. -/
theorem enabledMin_le {q : ℕ} {b : ℝ} {a : Fin 3 → ℝ} (j : Fin 3) (hj : j.val < q) :
    enabledMin q b a ≤ a j := by
  fin_cases j
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · change 1 < q at hj
    simp only [enabledMin, ite_eq_left (by omega : 2 ≤ q)]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · change 2 < q at hj
    simp only [enabledMin, ite_eq_left (by omega : 2 ≤ q), ite_eq_left (by omega : 3 ≤ q)]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

/-- Positive enabled entries give a positive minimum; disabled tolerances are irrelevant. -/
theorem enabledMin_pos {q : ℕ} {b : ℝ} {a : Fin 3 → ℝ} (hq : 1 ≤ q)
    (hb : 0 < b) (ha : ∀ j : Fin 3, j.val < q → 0 < a j) : 0 < enabledMin q b a := by
  have h0 := ha 0 (by omega)
  unfold enabledMin
  split_ifs with h2 h3
  · exact lt_min hb (lt_min h0 (lt_min (ha 1 (by omega)) (ha 2 (by omega))))
  · exact lt_min hb (lt_min h0 (lt_min (ha 1 (by omega)) (ha 1 (by omega))))
  · exact lt_min hb (lt_min h0 h0)

/-- The residual entry is bounded by the enabled maximum. -/
theorem residual_le_enabledMax (q : ℕ) (b : ℝ) (a : Fin 3 → ℝ) : b ≤ enabledMax q b a :=
  le_max_left _ _

/-- Every enabled derivative entry is bounded by the enabled maximum. -/
theorem le_enabledMax {q : ℕ} {b : ℝ} {a : Fin 3 → ℝ} (j : Fin 3) (hj : j.val < q) :
    a j ≤ enabledMax q b a := by
  fin_cases j
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · change 1 < q at hj
    simp only [enabledMax, ite_eq_left (by omega : 2 ≤ q)]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · change 2 < q at hj
    simp only [enabledMax, ite_eq_left (by omega : 2 ≤ q), ite_eq_left (by omega : 3 ≤ q)]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Positive scaling commutes with the enabled maximum. -/
theorem mul_enabledMax (q : ℕ) (b : ℝ) (a : Fin 3 → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    c * enabledMax q b a = enabledMax q (c * b) (fun j => c * a j) := by
  unfold enabledMax
  split_ifs <;> simp only [mul_max_of_nonneg _ _ hc]

/-- The actual derivative-to-step exponent at zero-based derivative index `j`. -/
def derivativeExponent (p : ℕ) (j : Fin 3) : ℝ := ((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)

/-- The exact beta-dependent coefficient for the residual-root decrease. -/
def rootDecreaseCoefficient (params : RegularizationParameters) (p i : ℕ)
    (ell beta L S : ℝ) (theta : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  decreaseConstant params p (j.val + 1) L S (theta j) *
    beta ^ ((ell - 1) * derivativeExponent p j) / (2 : ℝ) ^ i

/-- Uniform root decrease, including the residual-only branch and enabled derivative tests. -/
def rootDecrease (params : RegularizationParameters) (q p i : ℕ)
    (ell beta L S epsilon0 a0 : ℝ) (theta epsilon : Fin 3 → ℝ) : ℝ :=
  enabledMin q (1 - beta ^ ((1 : ℝ) / (2 : ℝ) ^ i))
    (rootDecreaseCoefficient params p i ell beta L S theta) *
      enabledMin q (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
        (fun j => epsilon j ^ derivativeExponent p j) /
      enabledMax q 1 (fun j => a0 ^ Optimization.residualDescentExponent p ell i (j.val + 1))

/-- Congruent enabled entries yield the same maximum; disabled entries are irrelevant. -/
theorem enabledMax_congr {q : ℕ} {a b : Fin 3 → ℝ} {c : ℝ} (hq : 1 ≤ q)
    (h : ∀ j : Fin 3, j.val < q → a j = b j) : enabledMax q c a = enabledMax q c b := by
  have h0 := h 0 (by omega)
  unfold enabledMax
  split_ifs with h2 h3
  · rw [h0, h 1 (by omega), h 2 (by omega)]
  · rw [h0, h 1 (by omega)]
  · rw [h0]

/-- The exact initial-residual dependence after telescoping the root potential. -/
def initialResidualFactor (q p i : ℕ) (ell a0 : ℝ) : ℝ :=
  enabledMax q (a0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
    (fun j => a0 ^ (1 - (j.val + 1 : ℕ) * (ell - 1) / ((p : ℝ) - j.val)))

/-- Multiplying by the initial root potential gives precisely the printed residual powers. -/
theorem initialResidualFactor_eq {q p i : ℕ} {ell a0 : ℝ} (hq : 1 ≤ q)
    (ha0 : 0 ≤ a0) (hi : ∀ j : Fin 3, j.val < q →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1)) :
    initialResidualFactor q p i ell a0 = a0 ^ ((1 : ℝ) / (2 : ℝ) ^ i) *
      enabledMax q 1 (fun j => a0 ^
        Optimization.residualDescentExponent p ell i (j.val + 1)) := by
  rw [mul_enabledMax _ _ _ (Real.rpow_nonneg ha0 _), mul_one]
  apply enabledMax_congr hq
  intro j hj
  rw [← Real.rpow_add_of_nonneg ha0 (by positivity) (hi j hj)]
  congr 1
  rw [Optimization.residualDescentExponent_eq_sub_inv]
  push_cast
  have hden : (p : ℝ) - ((j.val : ℝ) + 1) + 1 = (p : ℝ) - j.val := by ring
  rw [hden]
  ring

/-- The inverse accepted-root coefficient is independent of all requested tolerances. -/
def complexityConstant (params : RegularizationParameters) (q p i : ℕ)
    (ell beta L S : ℝ) (theta : Fin 3 → ℝ) : ℝ :=
  (enabledMin q (1 - beta ^ ((1 : ℝ) / (2 : ℝ) ^ i))
    (rootDecreaseCoefficient params p i ell beta L S theta))⁻¹

/-- Enabled tolerance powers with their exact distinct exponents. -/
def toleranceFactor (q p i : ℕ) (epsilon0 : ℝ) (epsilon : Fin 3 → ℝ) : ℝ :=
  enabledMin q (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
    (fun j => epsilon j ^ derivativeExponent p j)

/-- The source inverse coefficient is strictly positive and independent of tolerances. -/
theorem complexityConstant_pos {params : RegularizationParameters} {q p i : ℕ}
    {ell beta L S : ℝ} {theta : Fin 3 → ℝ} (hq : 1 ≤ q)
    (hb0 : 0 < beta) (hb1 : beta < 1) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (htheta : ∀ j : Fin 3, 0 < theta j) :
    0 < complexityConstant params q p i ell beta L S theta := by
  apply inv_pos.mpr
  apply enabledMin_pos hq
  · exact sub_pos.mpr (Real.rpow_lt_one hb0.le hb1 (by positivity))
  · intro j _
    exact div_pos (mul_pos (decreaseConstant_pos params p (j.val + 1) hL hS (htheta j))
      (Real.rpow_pos_of_pos hb0 _)) (by positivity)

/-- The root-potential budget is exactly the source maximum of initial residual powers
multiplied by a tolerance-independent coefficient and divided by enabled tolerance powers. -/
theorem root_budget_eq {params : RegularizationParameters} {q p i : ℕ}
    {ell beta L S epsilon0 a0 : ℝ} {theta epsilon : Fin 3 → ℝ}
    (hq : 1 ≤ q) (ha0 : 0 ≤ a0) (hi : ∀ j : Fin 3, j.val < q →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1)) :
    a0 ^ ((1 : ℝ) / (2 : ℝ) ^ i) /
        rootDecrease params q p i ell beta L S epsilon0 a0 theta epsilon =
      complexityConstant params q p i ell beta L S theta *
        (initialResidualFactor q p i ell a0 / toleranceFactor q p i epsilon0 epsilon) := by
  rw [initialResidualFactor_eq hq ha0 hi]
  simp only [rootDecrease, complexityConstant, toleranceFactor, div_eq_mul_inv,
    mul_inv_rev, inv_inv]
  ring

/-- First-order complexity uses only its residual and gradient tolerance powers. -/
@[simp] theorem toleranceFactor_one (p i : ℕ) (epsilon0 : ℝ) (epsilon : Fin 3 → ℝ) :
    toleranceFactor 1 p i epsilon0 epsilon =
      min (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
        (epsilon 0 ^ (((p + 1 : ℕ) : ℝ) / p)) := by
  simp [toleranceFactor, enabledMin, derivativeExponent]

/-- Second-order complexity adds precisely the negative-curvature tolerance power. -/
@[simp] theorem toleranceFactor_two (p i : ℕ) (epsilon0 : ℝ) (epsilon : Fin 3 → ℝ) :
    toleranceFactor 2 p i epsilon0 epsilon =
      min (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
        (min (epsilon 0 ^ (((p + 1 : ℕ) : ℝ) / p))
          (epsilon 1 ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))) := by
  simp [toleranceFactor, enabledMin, derivativeExponent]

/-- The four tolerance powers in the printed third-order bound. -/
@[simp] theorem toleranceFactor_three (p i : ℕ) (epsilon0 : ℝ) (epsilon : Fin 3 → ℝ) :
    toleranceFactor 3 p i epsilon0 epsilon =
      min (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
        (min (epsilon 0 ^ (((p + 1 : ℕ) : ℝ) / p))
          (min (epsilon 1 ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
            (epsilon 2 ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))))) := by
  simp [toleranceFactor, enabledMin, derivativeExponent]

/-- The four initial residual powers in the printed third-order numerator. -/
@[simp] theorem initialResidualFactor_three (p i : ℕ) (ell a0 : ℝ) :
    initialResidualFactor 3 p i ell a0 =
      max (a0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
        (max (a0 ^ (1 - (ell - 1) / p))
          (max (a0 ^ (1 - 2 * (ell - 1) / ((p : ℝ) - 1)))
            (a0 ^ (1 - 3 * (ell - 1) / ((p : ℝ) - 2))))) := by
  norm_num [initialResidualFactor, enabledMax]

variable {E : Type} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F]
  {params : RegularizationParameters} {q p N : ℕ} {theta epsilon : Fin 3 → ℝ}
  {epsilon0 ell : ℝ} {r : E → F} {x s : ℕ → E} {sigma : ℕ → ℝ}

/-- All coefficients in the exact uniform residual-root decrease are positive. -/
theorem rootDecrease_pos
    (h : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    {beta L S : ℝ} {i : ℕ} (hb0 : 0 < beta) (hb1 : beta < 1)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (a0 : ℝ) :
    0 < rootDecrease params q p i ell beta L S epsilon0 a0 theta epsilon := by
  have hq := h.toARpPrefix.order_pos
  have hK : 0 < enabledMin q (1 - beta ^ ((1 : ℝ) / (2 : ℝ) ^ i))
      (rootDecreaseCoefficient params p i ell beta L S theta) := by
    apply enabledMin_pos hq
    · exact sub_pos.mpr (Real.rpow_lt_one hb0.le hb1 (by positivity))
    · intro j _
      exact div_pos (mul_pos (decreaseConstant_pos params p (j.val + 1) hL hS
        (h.toARpPrefix.theta_pos j)) (Real.rpow_pos_of_pos hb0 _)) (by positivity)
  have hT : 0 < enabledMin q (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
      (fun j => epsilon j ^ derivativeExponent p j) := by
    exact enabledMin_pos hq (Real.rpow_pos_of_pos h.residual_tolerance_pos _)
      (fun j hj => Real.rpow_pos_of_pos (h.toARpPrefix.epsilon_pos j hj) _)
  exact div_pos (mul_pos hK hT)
    (lt_of_lt_of_le zero_lt_one (residual_le_enabledMax _ _ _))

/-- Actual objective decrease transfers to the normalized residual-root estimate. -/
theorem RunPrefix.root_decrease_from_derivative
    (h : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    {k i : ℕ} (hk : k < N) {beta L S c : ℝ} (hb0 : 0 < beta)
    (hrel : beta * ‖r (x k)‖ ≤ ‖r (x (k + 1))‖)
    (hb : 0 < ‖r (x (k + 1))‖) (j : Fin 3) (hj : j.val < q)
    (hc : 0 ≤ c) (hK : 0 ≤ decreaseConstant params p (j.val + 1) L S (theta j))
    (hdec : decreaseConstant params p (j.val + 1) L S (theta j) *
      c ^ derivativeExponent p j ≤ residualPowerObjective r ell (x k) -
        residualPowerObjective r ell (x (k + 1))) :
    rootDecreaseCoefficient params p i ell beta L S theta j *
      (c / ‖r (x (k + 1))‖ ^ (ell - 1)) ^ derivativeExponent p j /
      ‖r (x k)‖ ^ Optimization.residualDescentExponent p ell i (j.val + 1) ≤
        ‖r (x k)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) -
          ‖r (x (k + 1))‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) := by
  have hqp := h.toARpPrefix.degree_ge_order
  have hpj : j.val + 1 ≤ p := by omega
  have hD : (0 : ℝ) < (p : ℝ) - (j.val + 1 : ℕ) + 1 := by
    have hpr : (j.val + 1 : ℕ) ≤ (p : ℝ) := by exact_mod_cast hpj
    linarith
  have hden : ((p - j.val : ℕ) : ℝ) = (p : ℝ) - (j.val + 1 : ℕ) + 1 := by
    rw [Nat.cast_sub (by omega : j.val ≤ p), Nat.cast_add, Nat.cast_one]
    ring
  have hba := h.residual_norm_nonincrease hk
  have ha := hb.trans_le hba
  have hell : 0 < ell := by linarith [h.exponent_ge_two]
  have hd := Optimization.normalized_power_decrease hell hb hc hdec
  simpa only [rootDecreaseCoefficient, derivativeExponent, hden, Nat.cast_add, Nat.cast_one]
    using Optimization.residual_root_decrease hD (by linarith [h.exponent_ge_two]) ha hb.le
      hba hb0 hrel (div_nonneg hc (Real.rpow_nonneg hb.le _)) hK (by positivity)
      (by simpa only [derivativeExponent, hden, Nat.cast_add, Nat.cast_one] using hd)

/-- Uniformization uses only the actual derivative violation, monotonic residual norms and
nonnegative descent exponents. -/
theorem uniform_root_decrease {K T D k e c alpha a a0 v : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hD : 0 < D) (hk : K ≤ k) (he : T ≤ e ^ alpha)
    (he0 : 0 ≤ e) (hec : e ≤ c) (halpha : 0 ≤ alpha) (ha : 0 < a)
    (haa0 : a ≤ a0) (hv : 0 ≤ v) (ha0D : a0 ^ v ≤ D) :
    K * T / D ≤ k * c ^ alpha / a ^ v := by
  have hk0 : 0 ≤ k := hK.trans hk
  have hnum : K * T ≤ k * c ^ alpha :=
    mul_le_mul hk (he.trans (Real.rpow_le_rpow he0 hec halpha)) hT hk0
  have hden : a ^ v ≤ D := (Real.rpow_le_rpow ha.le haa0 hv).trans ha0D
  exact (div_le_div_of_nonneg_right hnum hD.le).trans
    (div_le_div_of_nonneg_left (mul_nonneg hk0 (Real.rpow_nonneg (he0.trans hec) _))
      (Real.rpow_pos_of_pos ha _) hden)



section Finite
variable [FiniteDimensional ℝ E] [Nontrivial E]

set_option maxHeartbeats 1200000 in
-- Four normalized derivative cases each elaborate actual higher-order derivative estimates.
/-- Every accepted trial whose successor fails quality pays the uniform residual-root
amount. The flat-Hessian case is derived from the actual model step as well. -/
theorem RunPrefix.root_decrease_of_not_quality
    (h : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    {L beta : ℝ} {i k : ℕ} (hf : DiagonalLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : ∀ j : Fin 3, j.val < q →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1))
    (hk : k < N)
    (hs : params.eta1 ≤ ratio (residualPowerObjective r ell) p (x k) (s k))
    (hn : ¬Quality q epsilon0 epsilon r ell (x (k + 1))
      (directionSequence p (theta 1) (epsilon 1)
        (residualPowerObjective r ell) x s sigma (k + 1))) :
    rootDecrease params q p i ell beta L
      (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))))
      epsilon0 ‖r (x 0)‖ theta epsilon ≤
        ‖r (x k)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) -
          ‖r (x (k + 1))‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) := by
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let t := (1 : ℝ) / (2 : ℝ) ^ i
  let K0 := 1 - beta ^ t
  let KR := rootDecreaseCoefficient params p i ell beta L S theta
  let K := enabledMin q K0 KR
  let T := enabledMin q (epsilon0 ^ t) (fun j => epsilon j ^ derivativeExponent p j)
  let D := enabledMax q 1 (fun j => ‖r (x 0)‖ ^
    Optimization.residualDescentExponent p ell i (j.val + 1))
  change K * T / D ≤ _
  have hS : 0 ≤ S :=
    (h.toARpPrefix.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hsigma : sigma k ≤ S := h.toARpPrefix.toTrialPrefix.sigma_upper hf
    (h.toARpPrefix.order_pos.trans h.toARpPrefix.degree_ge_order) (by omega)
  have hKr : ∀ j : Fin 3, 0 < KR j := fun j =>
    div_pos (mul_pos (decreaseConstant_pos params p (j.val + 1) hf.nonneg hS
      (h.toARpPrefix.theta_pos j)) (Real.rpow_pos_of_pos hb0 _)) (by positivity)
  have hK0 : 0 < K0 := sub_pos.mpr (Real.rpow_lt_one hb0.le hb1 (by positivity))
  have hK : 0 < K := enabledMin_pos h.toARpPrefix.order_pos hK0 (fun j _ => hKr j)
  have hT : 0 < T := enabledMin_pos h.toARpPrefix.order_pos
    (Real.rpow_pos_of_pos h.residual_tolerance_pos _)
    (fun j hj => Real.rpow_pos_of_pos (h.toARpPrefix.epsilon_pos j hj) _)
  have hD1 : 1 ≤ D := residual_le_enabledMax _ _ _
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have hbtest : epsilon0 < ‖r (x (k + 1))‖ :=
    lt_of_not_ge (fun hb => hn (Or.inl hb))
  have hb : 0 < ‖r (x (k + 1))‖ := h.residual_tolerance_pos.trans hbtest
  have hba := h.residual_norm_nonincrease hk
  have ha := hb.trans_le hba
  by_cases hrel : beta * ‖r (x k)‖ < ‖r (x (k + 1))‖
  · have hr : r (x (k + 1)) ≠ 0 := norm_ne_zero_iff.mp hb.ne'
    have hm := normalizedResidualMeasures_of_ne_zero (ell := ell) hr
    obtain ⟨_, hbad⟩ := not_quality_witness hm hn
    have huniform (j : Fin 3) (hj : j.val < q) (c : ℝ) (hc : 0 ≤ c)
        (hfail : epsilon j ≤ c / ‖r (x (k + 1))‖ ^ (ell - 1))
        (hdec : decreaseConstant params p (j.val + 1) L S (theta j) *
          c ^ derivativeExponent p j ≤ residualPowerObjective r ell (x k) -
            residualPowerObjective r ell (x (k + 1))) : K * T / D ≤
          ‖r (x k)‖ ^ t - ‖r (x (k + 1))‖ ^ t := by
      have hraw := h.root_decrease_from_derivative (i := i) hk hb0 hrel.le hb j hj hc
        (decreaseConstant_pos params p (j.val + 1) hf.nonneg hS
          (h.toARpPrefix.theta_pos j)).le hdec
      have hpower : 0 ≤ derivativeExponent p j := by unfold derivativeExponent; positivity
      exact (uniform_root_decrease hK.le hT.le hD (enabledMin_le j hj)
        (enabledMin_le j hj) (h.toARpPrefix.epsilon_pos j hj).le hfail hpower ha
        (h.residual_norm_le_initial (by omega)) (hi j hj) (le_enabledMax (a := fun j => ‖r (x 0)‖ ^
          Optimization.residualDescentExponent p ell i (j.val + 1)) j hj)).trans hraw
    rcases hbad with hg | hc | ⟨hq, d, hd, hc⟩
    · apply huniform 0 (by have := h.toARpPrefix.order_pos; omega)
        ‖fderiv ℝ (residualPowerObjective r ell) (x (k + 1))‖ (norm_nonneg _) hg.le
      simpa only [derivativeExponent, Fin.val_zero, Nat.sub_zero, zero_add] using
        h.toARpPrefix.gradient_decrease hf hk hs hsigma
    · have hmax : epsilon 1 ≤ max 0 (-leastCurvature
          (fderiv ℝ (fderiv ℝ (residualPowerObjective r ell)) (x (k + 1)))) /
          ‖r (x (k + 1))‖ ^ (ell - 1) := by
        simpa only [Optimization.max_neg_div_eq (Real.rpow_nonneg hb.le _)] using hc.2.le
      apply huniform 1 (by have := hc.1; omega) _ (le_max_left _ _) hmax
      simpa only [derivativeExponent, Fin.val_one] using
        h.toARpPrefix.curvature_decrease hf hc.1 hk hs hsigma
    · have hdir : d ∈ smallCurvatureDirections
          (model (residualPowerObjective r ell) p (x k) (sigma k))
          (s k) (theta 1 * ‖s k‖ ^ (p - 1)) := hd
      rcases hc with hc | hc
      · apply huniform 2 (by omega) _ (abs_nonneg _) hc.le
        simpa only [derivativeExponent, Fin.val_two] using
          h.toARpPrefix.cubic_decrease hf hq hk hs hsigma hdir
      · apply huniform 1 (by omega) _ (abs_nonneg _) hc.le
        simpa only [derivativeExponent, Fin.val_one] using
          h.toARpPrefix.flat_hessian_decrease hf hq hk hs hsigma hdir
  · have hsmall := Real.root_sub_root_ge_of_le_mul (norm_nonneg (r (x k)))
      (norm_nonneg (r (x (k + 1)))) hb0.le (le_of_not_gt hrel) (by positivity : 0 ≤ t)
    have hbt : epsilon0 ^ t ≤ ‖r (x k)‖ ^ t :=
      Real.rpow_le_rpow h.residual_tolerance_pos.le (hbtest.le.trans hba) (by positivity)
    have hKT : K * T ≤ K0 * ‖r (x k)‖ ^ t :=
      mul_le_mul (enabledMin_le_residual _ _ _)
        ((enabledMin_le_residual _ _ _).trans hbt) hT.le hK0.le
    exact (div_le_self (mul_nonneg hK.le hT.le) hD1).trans (hKT.trans hsmall)


/-- Exact residual-root telescope and cached residual oracle counts on every finite legal
prefix before first quality. One final accepted step is counted separately. -/
theorem RunPrefix.quality_evaluation_bounds
    (h : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    {L beta : ℝ} {i : ℕ} (hf : DiagonalLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : ∀ j : Fin 3, j.val < q →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1))
    (hfirst : ∀ k < N, ¬Quality q epsilon0 epsilon r ell (x k)
      (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell) x s sigma k)) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := ‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) /
      rootDecrease params q p i ell beta L S epsilon0 ‖r (x 0)‖ theta epsilon
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    (residualFunctionEvaluations N : ℝ) ≤ C * Q + C + D + 1 ∧
      (residualDerivativeEvaluations params p r ell x s N : ℝ) ≤ Q + 2 := by
  dsimp only
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let delta := rootDecrease params q p i ell beta L S epsilon0 ‖r (x 0)‖ theta epsilon
  let u := fun k => ‖r (x k)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i)
  let accepted := fun k => params.eta1 ≤ ratio (residualPowerObjective r ell) p (x k) (s k)
  have hS : 0 ≤ S :=
    (h.toARpPrefix.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hd : 0 < delta := rootDecrease_pos h hb0 hb1 hf.nonneg hS _
  have hmono : ∀ k < N, u (k + 1) ≤ u k := fun k hk =>
    Real.rpow_le_rpow (norm_nonneg _) (h.residual_norm_nonincrease hk) (by positivity)
  have hdec : ∀ k < N, accepted k →
      ¬Quality q epsilon0 epsilon r ell (x (k + 1))
        (directionSequence p (theta 1) (epsilon 1)
          (residualPowerObjective r ell) x s sigma (k + 1)) →
      delta ≤ u k - u (k + 1) := fun k hk hs hn =>
    h.root_decrease_of_not_quality hf hb0 hb1 hi hk hs hn
  have hcount : (successCount accepted N : ℝ) ≤ u 0 / delta + 1 := by
    classical
    cases N with
    | zero =>
      simp only [successCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty,
        Nat.cast_zero]
      exact le_add_of_nonneg_of_le (div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hd.le)
        zero_le_one
    | succ n =>
      have hb : (successCount accepted n : ℝ) ≤ u 0 / delta := by
        apply (le_div_iff₀ hd).mpr
        have hc := EvaluationComplexity.card_mul_le_gap (u := u) (n := n)
          (S := (Finset.range n).filter accepted) (low := 0) (δ := delta)
          (Finset.filter_subset _ _) (Real.rpow_nonneg (norm_nonneg _) _)
          (fun k hk => hmono k (by omega))
          (fun k hk => hdec k
            (by have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega)
            (Finset.mem_filter.mp hk).2
            (hfirst (k + 1)
              (by have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega)))
        simpa only [successCount, sub_zero] using hc
      have hs : (successCount accepted (n + 1) : ℝ) ≤
          (successCount accepted n : ℝ) + 1 := by exact_mod_cast successCount_succ_le accepted n
      linarith
  have hp : 1 ≤ p := h.toARpPrefix.order_pos.trans h.toARpPrefix.degree_ge_order
  have ht := h.toARpPrefix.toRegularizationPrefix.total_count_le le_rfl
    (h.toARpPrefix.toTrialPrefix.sigma_upper hf hp le_rfl)
  have hC : 0 ≤ 1 + |Real.log params.gamma1| / Real.log params.gamma2 :=
    add_nonneg zero_le_one
      (div_nonneg (abs_nonneg _) (Real.log_pos params.one_lt_gamma2).le)
  have hm := mul_le_mul_of_nonneg_right hcount hC
  simp only [residualFunctionEvaluations, residualDerivativeEvaluations,
    functionEvaluations, derivativeEvaluations, Nat.cast_add, Nat.cast_one]
  constructor <;> linarith

/-- Any quality point in an actual finite prefix has a first quality predecessor within
the residual-root and cached evaluation budgets. -/
theorem RunPrefix.exists_first_quality_of_attainment
    (h : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    {L beta : ℝ} {i : ℕ} (hf : DiagonalLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : ∀ j : Fin 3, j.val < q →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1))
    (hattain : ∃ K ≤ N, Quality q epsilon0 epsilon r ell (x K)
      (directionSequence p (theta 1) (epsilon 1)
        (residualPowerObjective r ell) x s sigma K)) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := ‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) /
      rootDecrease params q p i ell beta L S epsilon0 ‖r (x 0)‖ theta epsilon
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K ≤ N, Quality q epsilon0 epsilon r ell (x K)
        (directionSequence p (theta 1) (epsilon 1)
          (residualPowerObjective r ell) x s sigma K) ∧
      (∀ k < K, ¬Quality q epsilon0 epsilon r ell (x k)
        (directionSequence p (theta 1) (epsilon 1)
          (residualPowerObjective r ell) x s sigma k)) ∧
      (residualFunctionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (residualDerivativeEvaluations params p r ell x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  classical
  let P := fun k => Quality q epsilon0 epsilon r ell (x k)
    (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell) x s sigma k)
  obtain ⟨K, hKN, hK⟩ := hattain
  have hex : ∃ k, P k := ⟨K, hK⟩
  let first := Nat.find hex
  have hfN : first ≤ N := (Nat.find_min' hex hK).trans hKN
  have hfirst : ∀ k < first, ¬P k := fun k hk => Nat.find_min hex hk
  exact ⟨first, hfN, Nat.find_spec hex, hfirst,
    (h.restrict hfN).quality_evaluation_bounds hf hb0 hb1 hi hfirst⟩

/-- A sufficiently long actual local prefix contains a first quality point with the
stated cached evaluation bounds. This theorem requires no model-solver availability law. -/
theorem RunPrefix.exists_first_quality_of_long_prefix
    (h : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    {L beta : ℝ} {i : ℕ} (hf : DiagonalLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : ∀ j : Fin 3, j.val < q →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1))
    (hlong :
      (1 + |Real.log params.gamma1| / Real.log params.gamma2) *
        (‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) /
          rootDecrease params q p i ell beta L
            (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))))
            epsilon0 ‖r (x 0)‖ theta epsilon) +
        (1 + |Real.log params.gamma1| / Real.log params.gamma2) +
        Real.log (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) / sigma 0) /
          Real.log params.gamma2 + 1 < N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := ‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) /
      rootDecrease params q p i ell beta L S epsilon0 ‖r (x 0)‖ theta epsilon
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K ≤ N, Quality q epsilon0 epsilon r ell (x K)
        (directionSequence p (theta 1) (epsilon 1)
          (residualPowerObjective r ell) x s sigma K) ∧
      (∀ k < K, ¬Quality q epsilon0 epsilon r ell (x k)
        (directionSequence p (theta 1) (epsilon 1)
          (residualPowerObjective r ell) x s sigma k)) ∧
      (residualFunctionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (residualDerivativeEvaluations params p r ell x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  classical
  let P := fun k => Quality q epsilon0 epsilon r ell (x k)
    (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell) x s sigma k)
  have hex : ∃ K ≤ N, P K := by
    by_contra! hn
    have hc := (h.quality_evaluation_bounds hf hb0 hb1 hi
      (fun k hk => hn k hk.le)).1
    simp only [residualFunctionEvaluations, functionEvaluations, Nat.cast_add,
      Nat.cast_one] at hc
    linarith
  exact h.exists_first_quality_of_attainment hf hb0 hb1 hi hex

/-- Availability of actual local trial laws before first quality forces first attained
quality. No decrease, quality or evaluation bound is assumed in the availability premise. -/
theorem exists_first_quality_with_cost
    {L beta : ℝ} {i : ℕ} (hf : DiagonalLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : ∀ j : Fin 3, j.val < q →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1))
    (hprefix : ∀ N, (∀ k < N, ¬Quality q epsilon0 epsilon r ell (x k)
      (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell) x s sigma k)) →
      RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := ‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) /
      rootDecrease params q p i ell beta L S epsilon0 ‖r (x 0)‖ theta epsilon
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K : ℕ, Quality q epsilon0 epsilon r ell (x K)
        (directionSequence p (theta 1) (epsilon 1)
          (residualPowerObjective r ell) x s sigma K) ∧
      (∀ k < K, ¬Quality q epsilon0 epsilon r ell (x k)
        (directionSequence p (theta 1) (epsilon 1)
          (residualPowerObjective r ell) x s sigma k)) ∧
      (residualFunctionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (residualDerivativeEvaluations params p r ell x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  have hb := fun N hn => (hprefix N hn).quality_evaluation_bounds hf hb0 hb1 hi hn
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound
    (B := (1 + |Real.log params.gamma1| / Real.log params.gamma2) *
      (‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) / rootDecrease params q p i ell beta L
        (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))))
        epsilon0 ‖r (x 0)‖ theta epsilon) +
      (1 + |Real.log params.gamma1| / Real.log params.gamma2) +
      Real.log (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) / sigma 0) /
        Real.log params.gamma2 + 1)
    (fun N hn => (by
      have hc := (hb N hn).1
      simp only [residualFunctionEvaluations, functionEvaluations, Nat.cast_add,
        Nat.cast_one] at hc
      linarith))
  exact ⟨K, hK, hfirst, hb K hfirst⟩

/-- At orders one and two, genuine local trial availability forces an actual first
stopping run with the same residual-root and cached oracle budget. -/
theorem exists_first_stop_with_cost
    (hq : q ≤ 2) {L beta : ℝ} {i : ℕ}
    (hf : DiagonalLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : ∀ j : Fin 3, j.val < q →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1))
    (hprefix : ∀ N, (∀ k < N, ¬Stationary q epsilon0 epsilon r ell (x k)
      (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell) x s sigma k)) →
      RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := complexityConstant params q p i ell beta L S theta *
      (initialResidualFactor q p i ell ‖r (x 0)‖ / toleranceFactor q p i epsilon0 epsilon)
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K : ℕ, IsRun params q p theta epsilon epsilon0 r ell x s sigma K ∧
      (residualFunctionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (residualDerivativeEvaluations params p r ell x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  have hlegal : ∀ N, (∀ k < N, ¬Quality q epsilon0 epsilon r ell (x k)
      (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell) x s sigma k)) →
      RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N := by
    intro N hn
    exact hprefix N (fun k hk hs => hn k hk hs.quality)
  obtain ⟨K, hK, hfirst, hF, hD⟩ := exists_first_quality_with_cost hf hb0 hb1 hi hlegal
  have hpref := hprefix K (fun k hk hs => hfirst k hk hs.quality)
  have hid := root_budget_eq (params := params) (i := i)
    (ell := ell) (beta := beta) (L := L)
    (S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))))
    (epsilon0 := epsilon0) (theta := theta) (epsilon := epsilon)
    hpref.toARpPrefix.order_pos (norm_nonneg (r (x 0))) hi
  refine ⟨K, ?_, ?_, ?_⟩
  · exact { toResidualPrefix := hpref
            terminal := (quality_iff_stationary_of_order_le_two hq _ _ _ _ _ _).mp hK
            first := fun k hk hs => hfirst k hk hs.quality }
  · simpa only [hid] using hF
  · simpa only [hid] using hD

end Finite
end Optimization.ResidualRegularization
