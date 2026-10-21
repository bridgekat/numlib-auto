import Numlib.Optimization.ResidualRegularizationRun
import Numlib.Optimization.ResidualPowerDecrease
import Numlib.Optimization.ResidualDescentExponent
import Numlib.Data.Nat.OddTwoFactorization
import Numlib.Analysis.SpecialFunctions.Pow.Difference
import NumlibSurface.CartisGouldToint.Chapter04.Section01

/-!
# Chapter 5, Section 1: nonlinear least Euclidean norms

The objective and normalized derivative tests are actual norm powers and derivatives. Zero
residuals are checked before any ratio. The adaptive regularization relation retains local
model laws, rejection caching and its first genuine stop. Scalar root differences and
parameter arithmetic delegate to the reusable backbone.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section01
open Optimization
open Chapter01.Section03 Chapter02.Section04 Chapter04.Section01

variable {n m : ℕ}

/-- The actual objective (5.1.3), for a residual map with real exponent `ell`. -/
abbrev residualPowerObjective (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ell : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ := Optimization.residualPowerObjective r ell

/-- The normalized actual gradient, signed least Hessian curvature, and absolute quadratic
and cubic directional measures. `none` is the separate zero-residual branch before division. -/
abbrev normalizedResidualMeasures
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ell : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :=
  ResidualRegularization.normalizedResidualMeasures r ell x

/-- The exponents (5.1.21), (5.1.23), (5.1.25), indexed by derivative order. -/
abbrev residualDescentExponent (p : ℕ) (ell : ℝ) (i j : ℕ) : ℝ :=
  Optimization.residualDescentExponent p ell i j

/-- Algorithm 5.1.1: actual ARp on the norm-power objective with replacement normalized
stopping tests, genuine first stopping index and cached derivatives. `q=1,2,3` activates the
finite thresholds; the unused entries encode the source's infinity sentinels. -/
abbrev algorithm_5_1_1 (params : regularizationParameters) (q p : ℕ)
    (theta epsilon : Fin 3 → ℝ) (epsilon0 : ℝ)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ell : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ) (N : ℕ) : Prop :=
  ResidualRegularization.IsRun params q p theta epsilon epsilon0 r ell x s sigma N

/-- Finite executed local laws of ARpLE, independent of a termination assertion. -/
abbrev arpLEPrefix (params : regularizationParameters) (q p : ℕ)
    (theta epsilon : Fin 3 → ℝ) (epsilon0 : ℝ)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ell : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ) (N : ℕ) : Prop :=
  ResidualRegularization.RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N

/-- The first normalized measure agrees with the source's Euclidean gradient expression. -/
theorem normalizedResidualMeasures_gradient
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {ell : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : r x ≠ 0) :
    (normalizedResidualMeasures r ell x).map
      ResidualRegularization.NormalizedResidualMeasures.first =
      some (‖gradient (residualPowerObjective r ell) x‖ / ‖r x‖ ^ (ell - 1)) := by
  rw [normalizedResidualMeasures, ResidualRegularization.normalizedResidualMeasures_of_ne_zero hx]
  simp only [Option.map_some, EuclideanSpace.norm_gradient_eq]

/-- Zero residuals are genuine global minima of the objective. -/
theorem residualPowerObjective_global_minimum_of_zero
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {ell : ℝ}
    (hell : 0 < ell) {x : EuclideanSpace ℝ (Fin n)} (hx : r x = 0) :
    IsMinOn (residualPowerObjective r ell) Set.univ x :=
  Optimization.isMinOn_residualPowerObjective_of_zero hell hx

/-- Lemma 5.1.1. The even integer and real `ell>2p` branches are both valid at zero. -/
theorem lemma_5_1_1 {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {p : ℕ} {ell : ℝ} (hr : ContDiff ℝ p r)
    (hell : (∃ k : ℕ, ell = 2 * (k : ℝ)) ∨ 2 * (p : ℝ) < ell) :
    ContDiff ℝ p (residualPowerObjective r ell) := by
  rcases hell with ⟨k, rfl⟩ | hell
  · exact Optimization.contDiff_residualPowerObjective_even hr k
  · exact Optimization.contDiff_residualPowerObjective_of_two_mul_le hr hell.le

/-- Lemma 5.1.2. Every accepted actual trial gives all activated normalized decrease
bounds; the flat-direction clause also bounds the absolute objective Hessian. Zero residuals
already terminate and are excluded only in the normalized ratios. -/
theorem lemma_5_1_2 [NeZero n] {params : regularizationParameters} {q p N : ℕ}
    {theta epsilon : Fin 3 → ℝ} {epsilon0 ell : ℝ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {L : ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}
    (h : arpLEPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    (hf : higherOrderLipschitz (residualPowerObjective r ell) p L) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ HigherOrderRegularization.ratio
      (residualPowerObjective r ell) p (x k) (s k)) (hr : r (x (k + 1)) ≠ 0) :
    let f := residualPowerObjective r ell
    let a := ‖r (x k)‖
    let b := ‖r (x (k + 1))‖
    let S := max (sigma 0) (params.gamma3 * L / (1 - params.eta2))
    let kappa := fun j : Fin 3 => HigherOrderRegularization.decreaseConstant params p (j.val + 1)
      L S (theta j)
    (∀ j : Fin 3, 0 < kappa j) ∧
    kappa 0 * ell * (‖gradient f (x (k + 1))‖ / b ^ (ell - 1)) ^
      (((p + 1 : ℕ) : ℝ) / (p : ℝ)) * b ^ ((ell - 1) * (((p + 1 : ℕ) : ℝ) / (p : ℝ))) ≤
        a ^ ell - b ^ ell ∧
    (2 ≤ q → kappa 1 * ell * (max 0 (-(leastHessianEigenvalue f (x (k + 1)) /
      b ^ (ell - 1)))) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) *
        b ^ ((ell - 1) * (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))) ≤ a ^ ell - b ^ ell) ∧
    (3 ≤ q → ∀ d ∈ modelFlatDirections f p (x k) (sigma k) (theta 1) (s k),
      kappa 2 * ell * (|iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| /
        b ^ (ell - 1)) ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) *
          b ^ ((ell - 1) * (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))) ≤ a ^ ell - b ^ ell ∧
      (|iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ => d)| / b ^ (ell - 1)) *
        b ^ (ell - 1) ≤ HigherOrderRegularization.criticalityConstant p 2 L S (theta 1) *
          ‖s k‖ ^ (p - 1)) := by
  dsimp only
  have hell : 0 < ell := by linarith [h.exponent_ge_two]
  have hb : 0 < ‖r (x (k + 1))‖ := norm_pos_iff.mpr hr
  have hbase := h.toARpPrefix
  have hp : 1 ≤ p := hbase.order_pos.trans hbase.degree_ge_order
  have hdiag := hf.toDiagonalLipschitz hp
  let S := max (sigma 0) (params.gamma3 * L / (1 - params.eta2))
  have hS : sigma k ≤ S := by
    simpa only [S, mul_div_assoc] using hbase.toTrialPrefix.sigma_upper hdiag hp (by omega)
  have hS0 : 0 ≤ S := (hbase.toRegularizationPrefix.pos (by omega)).le.trans hS
  have hd := Chapter04.Section01.lemma_4_1_4 hbase hf hk hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    exact HigherOrderRegularization.decreaseConstant_pos params p (j.val + 1)
      (zero_le_one.trans hf.constant_ge_one) hS0 (hbase.theta_pos _)
  · exact Optimization.normalized_power_decrease hell hb (norm_nonneg _) hd.1
  · intro hq
    have hh := Optimization.normalized_power_decrease hell hb (le_max_left _ _)
      (hd.2.1 hq)
    simpa [Optimization.max_neg_div_eq (Real.rpow_nonneg hb.le _)] using hh
  · intro hq d hdmem
    refine ⟨Optimization.normalized_power_decrease hell hb (abs_nonneg _) (hd.2.2 hq d hdmem), ?_⟩
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hb _).ne']
    exact (hbase.flat_direction_bounds hdiag hq hk hs hS hdmem).2

/-- Lemma 5.1.3. At zero both sides vanish; at positive `a` the denominator is positive. -/
theorem lemma_5_1_3 {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ell i : ℕ)
    (hell : 1 ≤ ell) :
    (a ^ ell - b ^ ell) /
      ((2 : ℝ) ^ i * ell * a ^ (((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i + ell - 1)) ≤
        a ^ (1 / (2 : ℝ) ^ i) - b ^ (1 / (2 : ℝ) ^ i) := by
  have ht : 0 < (1 : ℝ) / (2 : ℝ) ^ i := by positivity
  have hT : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  have hte : (1 : ℝ) / (2 : ℝ) ^ i ≤ ell :=
    (div_le_one (by positivity : (0 : ℝ) < 2 ^ i)).2 hT |>.trans (by exact_mod_cast hell)
  rcases eq_or_lt_of_le (hb.trans hba) with ha | ha
  · have h0 : a = 0 := ha.symm
    have hb0 : b = 0 := by linarith
    simp [h0, hb0]
  have h := Real.root_sub_root_ge_div ha hb hba ht hte
  have hc : (ell : ℝ) / (1 / (2 : ℝ) ^ i) = (2 : ℝ) ^ i * ell := by
    field_simp
  have he : (ell : ℝ) - 1 / (2 : ℝ) ^ i =
      ((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i + ell - 1 := by
    field_simp
    ring
  simpa only [Real.rpow_natCast, hc, he] using h

/-- Lemma 5.1.4. The relative-successor branch has all three normalized criticality
bounds, with third-order directions restricted to the actual model directions. The other
branch gives both residual-root bounds (5.1.27). All four coefficients are positive. -/
theorem lemma_5_1_4 [NeZero n] {params : regularizationParameters} {q p N : ℕ}
    {theta epsilon : Fin 3 → ℝ} {epsilon0 ell beta : ℝ} {i : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {L : ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}
    (h : arpLEPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    (hf : higherOrderLipschitz (residualPowerObjective r ell) p L) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ HigherOrderRegularization.ratio
      (residualPowerObjective r ell) p (x k) (s k))
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    let a := ‖r (x k)‖
    let b := ‖r (x (k + 1))‖
    let t := (1 : ℝ) / (2 : ℝ) ^ i
    let S := max (sigma 0) (params.gamma3 * L / (1 - params.eta2))
    let alpha := fun j : Fin 3 => ((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)
    let kappaR := fun j : Fin 3 =>
      HigherOrderRegularization.decreaseConstant params p (j.val + 1) L S (theta j) *
        beta ^ ((ell - 1) * alpha j) / (2 : ℝ) ^ i
    0 < 1 - beta ^ t ∧ (∀ j, 0 < kappaR j) ∧
    (beta * a < b →
      ∀ measures : ResidualRegularization.NormalizedResidualMeasures (EuclideanSpace ℝ (Fin n)),
      normalizedResidualMeasures r ell (x (k + 1)) = some measures →
      ∀ j : Fin 3, j.val < q → ∀ d : EuclideanSpace ℝ (Fin n),
      (j.val = 2 → d ∈ modelFlatDirections (residualPowerObjective r ell) p (x k)
        (sigma k) (theta 1) (s k)) →
      kappaR j * measures.nonnegativeMeasure j d ^ (alpha j) /
        a ^ residualDescentExponent p ell i (j.val + 1) ≤ a ^ t - b ^ t) ∧
    (b ≤ beta * a → (1 - beta ^ t) * a ^ t ≤ a ^ t - b ^ t ∧
      (1 - beta ^ t) * b ^ t ≤ a ^ t - b ^ t) := by
  dsimp only
  have ht : 0 < (1 : ℝ) / (2 : ℝ) ^ i := by positivity
  have hell : 0 < ell := by linarith [h.exponent_ge_two]
  have hmono := h.toARpPrefix.toTrialPrefix.objective_nonincrease hk
  change ‖r (x (k + 1))‖ ^ ell / ell ≤ ‖r (x k)‖ ^ ell / ell at hmono
  have hba := (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hell).mp
    ((div_le_div_iff_of_pos_right hell).mp hmono)
  have hqp : q ≤ p := h.toARpPrefix.degree_ge_order
  have hsigma0 := h.toARpPrefix.toRegularizationPrefix.pos (by omega : 0 ≤ N)
  have hS0 : 0 ≤ max (sigma 0) (params.gamma3 * L / (1 - params.eta2)) :=
    hsigma0.le.trans (le_max_left _ _)
  have hcoef : ∀ j : Fin 3,
      0 < HigherOrderRegularization.decreaseConstant params p (j.val + 1) L
        (max (sigma 0) (params.gamma3 * L / (1 - params.eta2))) (theta j) *
        beta ^ ((ell - 1) * (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ))) / (2 : ℝ) ^ i := by
    intro j
    exact div_pos (mul_pos (HigherOrderRegularization.decreaseConstant_pos params p (j.val + 1)
      (zero_le_one.trans hf.constant_ge_one) hS0 (h.toARpPrefix.theta_pos j))
      (Real.rpow_pos_of_pos hbeta0 _)) (by positivity)
  refine ⟨sub_pos.mpr (Real.rpow_lt_one hbeta0.le hbeta1 ht), hcoef, ?_, ?_⟩
  · intro hrel measures hm j hj d hdir
    have hb : 0 < ‖r (x (k + 1))‖ :=
      (mul_nonneg hbeta0.le (norm_nonneg _)).trans_lt hrel
    have ha : 0 < ‖r (x k)‖ := hb.trans_le hba
    have hr : r (x (k + 1)) ≠ 0 := norm_ne_zero_iff.mp hb.ne'
    rw [normalizedResidualMeasures,
      ResidualRegularization.normalizedResidualMeasures_of_ne_zero hr] at hm
    have hme := Option.some.inj hm
    subst measures
    have hd := lemma_5_1_2 h hf hk hs hr
    simp only [EuclideanSpace.norm_gradient_eq] at hd
    have hpj : j.val + 1 ≤ p := by omega
    have hD : (0 : ℝ) < (p : ℝ) - (j.val + 1 : ℕ) + 1 := by
      have hpr : (j.val + 1 : ℕ) ≤ (p : ℝ) := by exact_mod_cast hpj
      linarith
    have hden : ((p - j.val : ℕ) : ℝ) = (p : ℝ) - (j.val + 1 : ℕ) + 1 := by
      rw [Nat.cast_sub (by omega : j.val ≤ p), Nat.cast_add, Nat.cast_one]
      ring
    have htransfer (c kappa : ℝ) (hc : 0 ≤ c) (hkappa : 0 ≤ kappa)
        (hdec : kappa * ell * c ^ (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)) *
          ‖r (x (k + 1))‖ ^ ((ell - 1) * (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ))) ≤
            ‖r (x k)‖ ^ ell - ‖r (x (k + 1))‖ ^ ell) :
        (kappa * beta ^ ((ell - 1) * (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ))) /
          (2 : ℝ) ^ i) * c ^ (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)) /
          ‖r (x k)‖ ^ residualDescentExponent p ell i (j.val + 1) ≤
            ‖r (x k)‖ ^ (1 / (2 : ℝ) ^ i) -
              ‖r (x (k + 1))‖ ^ (1 / (2 : ℝ) ^ i) := by
      simpa only [residualDescentExponent, hden, Nat.cast_add, Nat.cast_one] using
        Optimization.residual_root_decrease hD (by linarith [h.exponent_ge_two]) ha hb.le hba
          hbeta0 hrel.le hc hkappa (by positivity)
          (by simpa only [hden, Nat.cast_add, Nat.cast_one] using hdec)
    fin_cases j
    · norm_num at hj
      exact htransfer _ _ (div_nonneg (norm_nonneg _) (Real.rpow_nonneg hb.le _))
        (hd.1 0).le hd.2.1
    · change (1 : ℕ) < q at hj
      exact htransfer _ _ (le_max_left _ _) (hd.1 1).le (hd.2.2.1 (by omega))
    · change (2 : ℕ) < q at hj
      exact htransfer _ _ (div_nonneg (abs_nonneg _) (Real.rpow_nonneg hb.le _))
        (hd.1 2).le (hd.2.2.2 (by omega) d (hdir rfl)).1
  · intro hrel
    have hsmall := Real.root_sub_root_ge_of_le_mul (norm_nonneg _) (norm_nonneg _)
      hbeta0.le hrel ht.le
    exact ⟨hsmall, (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hba ht.le)
      (sub_pos.mpr (Real.rpow_lt_one hbeta0.le hbeta1 ht)).le).trans hsmall⟩

/-- Lemma 5.1.5. Positivity excludes the zero integer, which has no odd-part factorization. -/
theorem lemma_5_1_5 {p : ℕ} (hp : 0 < p) :
    ∃! oi : ℕ × ℕ, Odd oi.1 ∧ 0 < oi.1 ∧ p = oi.1 * 2 ^ oi.2 :=
  Nat.existsUnique_odd_mul_two_pow hp

/-- Lemma 5.1.6. All six parameter choices (5.1.38)–(5.1.43), including strict
positivity at every earlier derivative order. Positivity of `ell-1` excludes the unsuitable
odd/zero-root branches. Divisibility and odd-factorization conditions retain the source's
integer choices, independently of the rational exponent algebra. -/
theorem lemma_5_1_6 {p i : ℕ} {ell : ℝ} (hp : 1 ≤ p) (hell : 1 < ell) :
    (ell = p → Real.logb 2 p < i → 0 < residualDescentExponent p ell i 1) ∧
    ((∃ o : ℕ, Odd o ∧ p = o * 2 ^ i ∧ ell = 1 + (o : ℝ) * ((2 : ℝ) ^ i - 1)) →
      residualDescentExponent p ell i 1 = 0 ∧ 1 < ell) ∧
    (Even p → ell = (p : ℝ) / 2 → Real.logb 2 ((p : ℝ) - 1) < i →
      0 < residualDescentExponent p ell i 1 ∧ 0 < residualDescentExponent p ell i 2) ∧
    (4 ∣ p - 1 →
      (∃ o : ℕ, Odd o ∧ p - 1 = o * 2 ^ (i + 1) ∧
        ell = 1 + (o : ℝ) * ((2 : ℝ) ^ i - 1)) →
      0 < residualDescentExponent p ell i 1 ∧ residualDescentExponent p ell i 2 = 0 ∧
        1 < ell) ∧
    (3 ∣ p → ell = (p : ℝ) / 3 → Real.logb 2 ((p : ℝ) - 2) < i →
      0 < residualDescentExponent p ell i 1 ∧ 0 < residualDescentExponent p ell i 2 ∧
        0 < residualDescentExponent p ell i 3) ∧
    ((∃ o h : ℕ, Odd o ∧ 0 < h ∧ i = 2 * h ∧ p - 2 = o * 2 ^ i ∧
      ell = 1 + (o : ℝ) * ∑ k ∈ Finset.range h, (2 : ℝ) ^ (2 * k)) →
      0 < residualDescentExponent p ell i 1 ∧ 0 < residualDescentExponent p ell i 2 ∧
        residualDescentExponent p ell i 3 = 0 ∧ 1 < ell) := by
  simpa only [residualDescentExponent, Nat.cast_one, Nat.cast_ofNat] using
    Optimization.residualDescentExponent_good_choices hp hell

end CartisGouldToint.Chapter05.Section01
