import Numlib.Analysis.Calculus.HermiteInterpolation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Polynomial

/-!
# Uniform estimates for two-point Hermite interpolation

The right endpoint correction is expanded in a fixed basis on `[0,1]`. Consequently the
bounds on its derivatives depend on the interpolation order, never on the interval length.
-/

open Polynomial
open scoped NNReal

namespace Hermite

/-- The multiset prescribing derivatives through order `p` at both endpoints of `[0,1]`. -/
def unitNodes (p : ℕ) : Multiset ℝ :=
  Multiset.replicate (p + 1) 0 + Multiset.replicate (p + 1) 1

@[simp] theorem count_unitNodes_zero (p : ℕ) : (unitNodes p).count 0 = p + 1 := by
  simp [unitNodes, Multiset.count_replicate]

@[simp] theorem count_unitNodes_one (p : ℕ) : (unitNodes p).count 1 = p + 1 := by
  simp [unitNodes, Multiset.count_replicate]

/-- The fixed right endpoint Taylor coefficient basis on the unit interval. -/
noncomputable def unitRightBasis (p i : ℕ) : ℝ[X] :=
  interpolateJet (unitNodes p) (fun x j => if x = 1 ∧ j = i then 1 else 0)

/-- Each basis polynomial has zero Taylor jet at zero and one specified coefficient at one. -/
theorem coeff_taylor_unitRightBasis (p i j : ℕ) (hj : j ≤ p) (x : ℝ)
    (hx : x = 0 ∨ x = 1) :
    (taylor x (unitRightBasis p i)).coeff j = if x = 1 ∧ j = i then 1 else 0 := by
  apply isJetInterpolant_iff_coeff_taylor.mp
    (isJetInterpolant_interpolateJet (unitNodes p) _) x
  · rcases hx with rfl | rfl <;> simp [unitNodes]
  · rcases hx with rfl | rfl <;> simpa using Nat.lt_succ_of_le hj

/-- A polynomial correction with arbitrary right Taylor coefficients and vanishing left jet. -/
noncomputable def unitRightCorrection (p : ℕ) (d : ℕ → ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range (p + 1), d i • unitRightBasis p i

/-- The correction interpolates its prescribed Taylor coefficients. -/
theorem coeff_taylor_unitRightCorrection (p j : ℕ) (d : ℕ → ℝ) (hj : j ≤ p)
    (x : ℝ) (hx : x = 0 ∨ x = 1) :
    (taylor x (unitRightCorrection p d)).coeff j = if x = 1 then d j else 0 := by
  classical
  simp only [unitRightCorrection, map_sum, map_smul, finsetSum_coeff, coeff_smul,
    smul_eq_mul]
  simp_rw [coeff_taylor_unitRightBasis p _ j hj x hx]
  rcases hx with rfl | rfl
  · simp
  · simp [Finset.mem_range, Nat.lt_succ_of_le hj]

/-- Uniform bounds for finite linear combinations of a fixed polynomial family on a
compact real interval. The constant is independent of the coefficient data. -/
theorem exists_sum_smul_polynomial_derivative_bound (q : ℕ → ℝ[X]) (p m : ℕ)
    (a b : ℝ) :
    ∃ C > 0, ∀ (d : ℕ → ℝ) (κ : ℝ), 0 ≤ κ →
      (∀ i ≤ p, |d i| ≤ κ) → ∀ j ≤ m, ∀ x ∈ Set.Icc a b,
        |(derivative^[j] (∑ i ∈ Finset.range (p + 1), d i • q i)).eval x| ≤ κ * C := by
  classical
  have hb (i j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Set.Icc a b,
      |(derivative^[j] (q i)).eval x| ≤ B := by
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (derivative^[j] (q i)).continuous.continuousOn
    refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
    simpa only [Real.norm_eq_abs] using (hB x hx).trans (le_max_left B 0)
  choose B hB hbound using hb
  let C := 1 + ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (m + 1), B i j
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hB i j)
  refine ⟨C, hC, ?_⟩
  intro d κ hκ hd j hj x hx
  rw [iterate_derivative_sum, eval_finsetSum]
  calc
    |∑ i ∈ Finset.range (p + 1), (derivative^[j] (d i • q i)).eval x| ≤
        ∑ i ∈ Finset.range (p + 1),
          |(derivative^[j] (d i • q i)).eval x| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ i ∈ Finset.range (p + 1), κ * B i j := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [iterate_derivative_smul, eval_smul, smul_eq_mul, abs_mul]
      exact mul_le_mul (hd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
        (hbound i j x hx) (abs_nonneg _) hκ
    _ = κ * ∑ i ∈ Finset.range (p + 1), B i j := (Finset.mul_sum ..).symm
    _ ≤ κ * C := by
      apply mul_le_mul_of_nonneg_left _ hκ
      calc
        ∑ i ∈ Finset.range (p + 1), B i j ≤
            ∑ i ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (m + 1), B i k := by
          apply Finset.sum_le_sum
          intro i hi
          exact Finset.single_le_sum (fun k _ => hB i k)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
        _ ≤ C := by dsimp [C]; linarith

/-- The unit interval correction has bounds depending only on the interpolation order. -/
theorem exists_unitRightCorrection_derivative_bound (p m : ℕ) :
    ∃ C > 0, ∀ (d : ℕ → ℝ) (κ : ℝ), 0 ≤ κ →
      (∀ i ≤ p, |d i| ≤ κ) → ∀ j ≤ m, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |(derivative^[j] (unitRightCorrection p d)).eval x| ≤ κ * C :=
  exists_sum_smul_polynomial_derivative_bound (unitRightBasis p) p m 0 1

/-- Differentiating after rescaling the polynomial variable. -/
theorem iterate_derivative_comp_C_mul_X (q : ℝ[X]) (a : ℝ) (j : ℕ) :
    derivative^[j] (q.comp (C a * X)) = C (a ^ j) * (derivative^[j] q).comp (C a * X) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp,
      Function.iterate_succ_apply']
    simp only [derivative_C_mul, derivative_X, mul_one]
    simp only [pow_succ, map_mul]
    ring

/-- The rescaled correction on an interval of length `s`. Its amplitude is `s^(p+1)`,
which cancels the loss from taking `p+1` derivatives. -/
noncomputable def intervalRightCorrection (p : ℕ) (s : ℝ) (d : ℕ → ℝ) : ℝ[X] :=
  C (s ^ (p + 1)) * (unitRightCorrection p d).comp (C s⁻¹ * X)

/-- Exact derivative scaling for the interval correction. -/
theorem eval_iterate_derivative_intervalRightCorrection (p j : ℕ) (s x : ℝ)
    (d : ℕ → ℝ) :
    (derivative^[j] (intervalRightCorrection p s d)).eval x =
      s ^ (p + 1) * (s⁻¹) ^ j *
        (derivative^[j] (unitRightCorrection p d)).eval (x / s) := by
  simp only [intervalRightCorrection, iterate_derivative_C_mul,
    iterate_derivative_comp_C_mul_X, eval_mul, eval_C, eval_X, eval_comp]
  rw [div_eq_mul_inv, mul_comm x s⁻¹]
  ring

/-- Uniform estimates for the highest derivative of a scaled right endpoint correction.
The same constant works for every positive interval length. -/
theorem exists_intervalRightCorrection_top_derivative_bound (p : ℕ) :
    ∃ C > 0, ∀ (s κ : ℝ) (d : ℕ → ℝ), 0 < s → 0 ≤ κ →
      (∀ i ≤ p, |d i| ≤ κ) → ∀ x ∈ Set.Icc (0 : ℝ) s,
        |(derivative^[p + 1] (intervalRightCorrection p s d)).eval x| ≤ κ * C := by
  obtain ⟨C, hC, hb⟩ := exists_unitRightCorrection_derivative_bound p (p + 1)
  refine ⟨C, hC, ?_⟩
  intro s κ d hs hκ hd x hx
  rw [eval_iterate_derivative_intervalRightCorrection]
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hscale : s ^ (p + 1) * (s⁻¹) ^ (p + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hs0, one_pow]
  rw [hscale, one_mul]
  exact hb d κ hκ hd (p + 1) le_rfl (x / s)
    ⟨div_nonneg hx.1 hs.le, (div_le_one hs).mpr hx.2⟩

/-- The polynomial represented by an initial derivative jet through order `p`. -/
noncomputable def endpointTaylor (p : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  jetPoly (fun j => a j / j.factorial) 0 (p + 1)

/-- The initial Taylor polynomial realizes the prescribed derivative jet. -/
theorem eval_iterate_derivative_endpointTaylor (p j : ℕ) (a : ℕ → ℝ) (hj : j ≤ p) :
    (derivative^[j] (endpointTaylor p a)).eval 0 = a j := by
  have h := coeff_taylor_jetPoly (fun j => a j / (j.factorial : ℝ)) 0 (p + 1) j
  rw [ite_eq_left (Nat.lt_succ_of_le hj), coeff_taylor_eq_eval_iterate_derivative_div] at h
  exact (div_left_inj' (Nat.cast_ne_zero.mpr j.factorial_ne_zero)).mp h

/-- The normalized right endpoint discrepancy, in Taylor coefficient units. -/
noncomputable def normalizedDiscrepancy (p : ℕ) (s : ℝ) (a b : ℕ → ℝ) (j : ℕ) : ℝ :=
  (b j - (derivative^[j] (endpointTaylor p a)).eval s) /
    (s ^ (p + 1 - j) * j.factorial)

/-- The constructed two-point Hermite polynomial: Taylor polynomial plus the rescaled
unit interval correction. -/
noncomputable def intervalPolynomial (p : ℕ) (s : ℝ) (a b : ℕ → ℝ) : ℝ[X] :=
  endpointTaylor p a + intervalRightCorrection p s (normalizedDiscrepancy p s a b)

/-- Exact derivative values of the unit correction at its endpoints. -/
theorem eval_iterate_derivative_unitRightCorrection (p j : ℕ) (d : ℕ → ℝ) (hj : j ≤ p)
    (x : ℝ) (hx : x = 0 ∨ x = 1) :
    (derivative^[j] (unitRightCorrection p d)).eval x =
      if x = 1 then d j * j.factorial else 0 := by
  have h := coeff_taylor_unitRightCorrection p j d hj x hx
  rw [coeff_taylor_eq_eval_iterate_derivative_div] at h
  have hj0 : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  rw [div_eq_iff hj0] at h
  rw [h]
  split_ifs <;> simp_all

/-- Exact scaling in every derivative order up to the amplitude order. -/
theorem pow_mul_inv_pow_eq_sub (s : ℝ) (hs : s ≠ 0) (n j : ℕ) (hj : j ≤ n) :
    s ^ n * (s⁻¹) ^ j = s ^ (n - j) := by
  rw [pow_sub₀ s hs hj, inv_pow]

/-- The constructed interval polynomial interpolates the left derivative jet. -/
theorem eval_iterate_derivative_intervalPolynomial_zero (p j : ℕ) (s : ℝ)
    (a b : ℕ → ℝ) (hj : j ≤ p) :
    (derivative^[j] (intervalPolynomial p s a b)).eval 0 = a j := by
  rw [intervalPolynomial, ← Module.End.pow_apply, map_add, eval_add, Module.End.pow_apply,
    Module.End.pow_apply, eval_iterate_derivative_endpointTaylor p j a hj,
    eval_iterate_derivative_intervalRightCorrection]
  simp [eval_iterate_derivative_unitRightCorrection p j _ hj 0 (Or.inl rfl)]

/-- The constructed interval polynomial interpolates the right derivative jet. -/
theorem eval_iterate_derivative_intervalPolynomial_right (p j : ℕ) (s : ℝ)
    (a b : ℕ → ℝ) (hs : 0 < s) (hj : j ≤ p) :
    (derivative^[j] (intervalPolynomial p s a b)).eval s = b j := by
  rw [intervalPolynomial, ← Module.End.pow_apply, map_add, eval_add, Module.End.pow_apply,
    Module.End.pow_apply, eval_iterate_derivative_intervalRightCorrection,
    div_self (ne_of_gt hs),
    eval_iterate_derivative_unitRightCorrection p j _ hj 1 (Or.inr rfl), ite_eq_left rfl,
    pow_mul_inv_pow_eq_sub s (ne_of_gt hs) (p + 1) j (by omega)]
  simp only [normalizedDiscrepancy]
  have hs0 : s ^ (p + 1 - j) ≠ 0 := pow_ne_zero _ (ne_of_gt hs)
  have hj0 : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  field_simp
  ring

/-- Taylor discrepancy bounds give bounded normalized correction coefficients without
any factor involving the minimum interval length. -/
theorem abs_normalizedDiscrepancy_le (p : ℕ) (s κ : ℝ) (a b : ℕ → ℝ)
    (hs : 0 < s) (hκ : 0 ≤ κ)
    (h : ∀ j ≤ p, |b j - (derivative^[j] (endpointTaylor p a)).eval s| ≤
      κ * s ^ (p + 1 - j)) :
    ∀ j ≤ p, |normalizedDiscrepancy p s a b j| ≤ κ := by
  intro j hj
  rw [normalizedDiscrepancy, abs_div, abs_mul, abs_of_pos (pow_pos hs _),
    abs_of_pos (show (0 : ℝ) < j.factorial from Nat.cast_pos.mpr j.factorial_pos)]
  apply (div_le_iff₀ (mul_pos (pow_pos hs _) (Nat.cast_pos.mpr j.factorial_pos))).mpr
  calc
    |b j - (derivative^[j] (endpointTaylor p a)).eval s| ≤ κ * s ^ (p + 1 - j) := h j hj
    _ ≤ κ * (s ^ (p + 1 - j) * j.factorial) := by
      have hf : (1 : ℝ) ≤ j.factorial := by exact_mod_cast j.factorial_pos
      nlinarith [pow_pos hs (p + 1 - j), mul_nonneg hκ (pow_pos hs (p + 1 - j)).le]

/-- Degree bound on a unit right endpoint basis polynomial. -/
theorem natDegree_unitRightBasis_le (p i : ℕ) : (unitRightBasis p i).natDegree ≤ 2 * p + 1 := by
  by_cases h : unitRightBasis p i = 0
  · simp [h]
  have hd := (natDegree_lt_iff_degree_lt h).mpr
    (degree_interpolateJet_lt (unitNodes p) (fun x j => if x = 1 ∧ j = i then 1 else 0))
  simp only [unitNodes, Multiset.card_add, Multiset.card_replicate] at hd
  omega

/-- Degree bound on the right endpoint correction. -/
theorem natDegree_unitRightCorrection_le (p : ℕ) (d : ℕ → ℝ) :
    (unitRightCorrection p d).natDegree ≤ 2 * p + 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_smul_le _ _).trans (natDegree_unitRightBasis_le p i)

/-- Degree bound on the rescaled correction. -/
theorem natDegree_intervalRightCorrection_le (p : ℕ) (s : ℝ) (d : ℕ → ℝ) :
    (intervalRightCorrection p s d).natDegree ≤ 2 * p + 1 := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  calc
    (unitRightCorrection p d).natDegree * (C s⁻¹ * X).natDegree ≤
        (2 * p + 1) * 1 := Nat.mul_le_mul (natDegree_unitRightCorrection_le p d)
          (by simpa using natDegree_C_mul_le s⁻¹ (X : ℝ[X]))
    _ = 2 * p + 1 := Nat.mul_one _

/-- The Taylor polynomial has degree at most `p`. -/
theorem natDegree_endpointTaylor_le (p : ℕ) (a : ℕ → ℝ) :
    (endpointTaylor p a).natDegree ≤ p := by
  by_cases h : endpointTaylor p a = 0
  · simp [h]
  have hd := (natDegree_lt_iff_degree_lt h).mpr
    (degree_jetPoly_lt (fun j => a j / (j.factorial : ℝ)) 0 (p + 1))
  omega

/-- The constructed interpolant has the usual Hermite degree bound. -/
theorem natDegree_intervalPolynomial_le (p : ℕ) (s : ℝ) (a b : ℕ → ℝ) :
    (intervalPolynomial p s a b).natDegree ≤ 2 * p + 1 := by
  exact natDegree_add_le_of_degree_le (by exact (natDegree_endpointTaylor_le p a).trans (by omega))
    (natDegree_intervalRightCorrection_le p s _)

/-- Uniform bounds for the lower derivatives of an initial Taylor polynomial, assuming only
bounded initial derivatives and evaluation on a fixed compact interval. -/
theorem exists_endpointTaylor_derivative_bound (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ C > 0, ∀ (a : ℕ → ℝ), (∀ i ≤ p, |a i| ≤ κ) → ∀ j ≤ p,
      ∀ x ∈ Set.Icc (0 : ℝ) κ, |(derivative^[j] (endpointTaylor p a)).eval x| ≤ κ * C := by
  obtain ⟨C, hC, hb⟩ := exists_sum_smul_polynomial_derivative_bound
    (fun i => (X : ℝ[X]) ^ i) p p 0 κ
  refine ⟨C, hC, ?_⟩
  intro a ha j hj x hx
  have hd : ∀ i ≤ p, |a i / (i.factorial : ℝ)| ≤ κ := by
    intro i hi
    rw [abs_div, abs_of_pos (show (0 : ℝ) < i.factorial from Nat.cast_pos.mpr i.factorial_pos)]
    apply (div_le_iff₀ (Nat.cast_pos.mpr i.factorial_pos)).mpr
    have hf : (1 : ℝ) ≤ i.factorial := by exact_mod_cast i.factorial_pos
    exact (ha i hi).trans (by nlinarith)
  simpa only [endpointTaylor, jetPoly, C_0, sub_zero, smul_eq_C_mul] using
    hb (fun i => a i / (i.factorial : ℝ)) κ hκ hd j hj x hx

/-- A single order-dependent constant bounds the highest derivative of every interval
Hermite polynomial satisfying the scaled Taylor discrepancy inequalities. -/
theorem exists_intervalPolynomial_top_derivative_bound (p : ℕ) :
    ∃ C > 0, ∀ (s κ : ℝ) (a b : ℕ → ℝ), 0 < s → 0 ≤ κ →
      (∀ j ≤ p, |b j - (derivative^[j] (endpointTaylor p a)).eval s| ≤
        κ * s ^ (p + 1 - j)) → ∀ x ∈ Set.Icc (0 : ℝ) s,
        |(derivative^[p + 1] (intervalPolynomial p s a b)).eval x| ≤ κ * C := by
  obtain ⟨C, hC, hb⟩ := exists_intervalRightCorrection_top_derivative_bound p
  refine ⟨C, hC, ?_⟩
  intro s κ a b hs hκ h x hx
  have hT : derivative^[p + 1] (endpointTaylor p a) = 0 :=
    iterate_derivative_eq_zero (by have := natDegree_endpointTaylor_le p a; omega)
  rw [intervalPolynomial, ← Module.End.pow_apply, map_add, Module.End.pow_apply,
    Module.End.pow_apply, hT, zero_add]
  exact hb s κ _ hs hκ (abs_normalizedDiscrepancy_le p s κ a b hs hκ h) x hx

/-- Lower derivative bounds on the full interval polynomial. Both constants are chosen
before the endpoint data and spacing. -/
theorem exists_intervalPolynomial_lower_derivative_bound (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ B ≥ 0, ∀ (s : ℝ) (a b : ℕ → ℝ), 0 < s → s ≤ κ →
      (∀ i ≤ p, |a i| ≤ κ) →
      (∀ j ≤ p, |b j - (derivative^[j] (endpointTaylor p a)).eval s| ≤
        κ * s ^ (p + 1 - j)) → ∀ j ≤ p, ∀ x ∈ Set.Icc (0 : ℝ) s,
        |(derivative^[j] (intervalPolynomial p s a b)).eval x| ≤ B := by
  obtain ⟨T, hT, hTaylor⟩ := exists_endpointTaylor_derivative_bound p κ hκ
  obtain ⟨C, hC, hCorr⟩ := exists_unitRightCorrection_derivative_bound p p
  let M : ℝ := max 1 κ ^ (p + 1)
  refine ⟨κ * T + M * (κ * C), by dsimp [M]; positivity, ?_⟩
  intro s a b hs hsκ ha hd j hj x hx
  have hnormal := abs_normalizedDiscrepancy_le p s κ a b hs hκ hd
  have hscale : s ^ (p + 1) * (s⁻¹) ^ j = s ^ (p + 1 - j) :=
    pow_mul_inv_pow_eq_sub s (ne_of_gt hs) _ _ (by omega)
  have hpow : s ^ (p + 1 - j) ≤ M := by
    calc
      s ^ (p + 1 - j) ≤ (max 1 κ) ^ (p + 1 - j) :=
        pow_le_pow_left₀ hs.le (hsκ.trans (le_max_right _ _)) _
      _ ≤ (max 1 κ) ^ (p + 1) := pow_le_pow_right₀ (le_max_left _ _) (by omega)
  rw [intervalPolynomial, ← Module.End.pow_apply, map_add, eval_add, Module.End.pow_apply,
    Module.End.pow_apply]
  calc
    _ ≤ |(derivative^[j] (endpointTaylor p a)).eval x| +
        |(derivative^[j] (intervalRightCorrection p s (normalizedDiscrepancy p s a b))).eval x| :=
      abs_add_le _ _
    _ ≤ κ * T + M * (κ * C) := by
      apply add_le_add
      · exact hTaylor a ha j hj x ⟨hx.1, hx.2.trans hsκ⟩
      · rw [eval_iterate_derivative_intervalRightCorrection, hscale, abs_mul,
          abs_of_pos (pow_pos hs _)]
        exact mul_le_mul hpow
          (hCorr _ κ hκ hnormal j hj (x / s)
            ⟨div_nonneg hx.1 hs.le, (div_le_one hs).mpr hx.2⟩)
          (abs_nonneg _) (by dsimp [M]; positivity)

/-- Uniform two-point Hermite interpolation estimates. The constants depend only on `p`
and `κ`; they apply simultaneously to every positive spacing and every pair of derivative
jets satisfying the scaled Taylor discrepancy inequalities. -/
theorem interval_hermite_derivative_bounds (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L B : ℝ≥0, ∀ (s : ℝ) (a b : ℕ → ℝ), 0 < s →
      (∀ j ≤ p, |b j - (derivative^[j] (endpointTaylor p a)).eval s| ≤
        κ * s ^ (p + 1 - j)) →
      ∃ P : ℝ[X], P.natDegree ≤ 2 * p + 1 ∧
        (∀ j ≤ p, iteratedDeriv j (fun x => P.eval x) 0 = a j ∧
          iteratedDeriv j (fun x => P.eval x) s = b j) ∧
        LipschitzOnWith L (iteratedDeriv p (fun x => P.eval x)) (Set.Icc 0 s) ∧
        ((∀ j ≤ p, |a j| ≤ κ) → s ≤ κ → ∀ j ≤ p, ∀ x ∈ Set.Icc (0 : ℝ) s,
          |iteratedDeriv j (fun x => P.eval x) x| ≤ B) := by
  obtain ⟨C, hC, htop⟩ := exists_intervalPolynomial_top_derivative_bound p
  obtain ⟨B, hB, hlower⟩ := exists_intervalPolynomial_lower_derivative_bound p κ hκ
  refine ⟨⟨κ * C, mul_nonneg hκ hC.le⟩, ⟨B, hB⟩, ?_⟩
  intro s a b hs hd
  refine ⟨intervalPolynomial p s a b, natDegree_intervalPolynomial_le p s a b, ?_, ?_, ?_⟩
  · intro j hj
    rw [Polynomial.iteratedDeriv_eval]
    exact ⟨eval_iterate_derivative_intervalPolynomial_zero p j s a b hj,
      eval_iterate_derivative_intervalPolynomial_right p j s a b hs hj⟩
  · rw [Polynomial.iteratedDeriv_eval]
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ => (derivative^[p] (intervalPolynomial p s a b)).differentiableAt) _
      (convex_Icc 0 s)
    intro x hx
    change ‖deriv (fun y => (derivative^[p] (intervalPolynomial p s a b)).eval y) x‖ ≤ κ * C
    rw [Polynomial.deriv, Real.norm_eq_abs]
    simpa only [Function.iterate_succ_apply'] using htop s κ a b hs hκ hd x hx
  · intro ha hsκ j hj x hx
    rw [Polynomial.iteratedDeriv_eval]
    exact hlower s a b hs hsκ ha hd j hj x hx

/-- The repeated interpolation nodes on an interval. -/
def intervalNodes (p : ℕ) (s : ℝ) : Multiset ℝ :=
  Multiset.replicate (p + 1) 0 + Multiset.replicate (p + 1) s

/-- Endpoint derivative data expressed as Taylor coefficients. -/
noncomputable def intervalJet (a b : ℕ → ℝ) (x : ℝ) (j : ℕ) : ℝ :=
  if x = 0 then a j / j.factorial else b j / j.factorial

/-- The constructed polynomial is the existing unique algebraic Hermite interpolant.
Thus the uniform estimates concern the canonical interpolant, rather than a separate
choice of polynomials. -/
theorem intervalPolynomial_eq_interpolateJet (p : ℕ) (s : ℝ) (a b : ℕ → ℝ) (hs : 0 < s) :
    intervalPolynomial p s a b = interpolateJet (intervalNodes p s) (intervalJet a b) := by
  apply eq_interpolateJet
  · have h := degree_le_of_natDegree_le (natDegree_intervalPolynomial_le p s a b)
    apply h.trans_lt
    simp only [intervalNodes, Multiset.card_add, Multiset.card_replicate]
    exact_mod_cast (show 2 * p + 1 < p + 1 + (p + 1) by omega)
  · apply isJetInterpolant_iff_coeff_taylor.mpr
    intro x hx j hj
    have hx' : x = 0 ∨ x = s := by
      simp only [intervalNodes, Multiset.mem_add, Multiset.mem_replicate] at hx
      exact hx.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    rcases hx' with h0 | h1
    · subst x
      have hj' : j ≤ p := by
        simp only [intervalNodes, Multiset.count_add, Multiset.count_replicate] at hj
        simpa [ne_of_gt hs] using hj
      rw [coeff_taylor_eq_eval_iterate_derivative_div,
        eval_iterate_derivative_intervalPolynomial_zero p j s a b hj']
      simp [intervalJet]
    · subst x
      have hj' : j ≤ p := by
        simp only [intervalNodes, Multiset.count_add, Multiset.count_replicate] at hj
        simpa [(ne_of_gt hs).symm] using hj
      rw [coeff_taylor_eq_eval_iterate_derivative_div,
        eval_iterate_derivative_intervalPolynomial_right p j s a b hs hj']
      simp [intervalJet, ne_of_gt hs]

end Hermite
