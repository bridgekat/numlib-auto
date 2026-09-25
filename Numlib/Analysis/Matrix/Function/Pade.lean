import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Numlib.Analysis.Normed.Algebra.Logarithm
import Numlib.Approximation.TriangleQuadrature
import Numlib.Analysis.Calculus.HermiteInterpolation

/-!
# Padé approximants of the exponential

The `(p, q)` Padé approximant `R_pq(z) = D_pq(z)⁻¹ N_pq(z)` of `e^z` ([golub2013matrix] §9.3.1;
Moler–Van Loan, "Nineteen dubious ways to compute the exponential of a matrix", SIAM Rev. 20
(1978)), with

  `N_pq(z) = ∑_{k ≤ p} (p + q - k)! p! / ((p + q)! k! (p - k)!) z^k`,  `D_pq(z) = N_qp(-z)`,

as polynomials over any field (`Pade.expNum`, `Pade.expDen`), and its value
`Pade.expApprox 𝕂 p q a = D_pq(a)⁻¹ N_pq(a)` at an element of an algebra over `𝕂`.

## Main results

* `Pade.isUnit_aeval_expDen`: the denominator is invertible for `‖a‖ < log 2`, in particular in the
  scaling-and-squaring regime `‖a‖ ≤ 1/2`, with `‖D_pq(a)⁻¹‖ ≤ 1/(2 - e^{‖a‖})`.
* `Pade.exp_eq_expApprox_add`: the remainder formula [golub2013matrix] (9.3.1),
  `e^a = R_pq(a) + ((-1)^q/(p + q)!) a^{p+q+1} D_pq(a)⁻¹ ∫₀¹ u^p (1 - u)^q e^{(1-u)a} du`, in any
  complete normed `ℝ`-algebra, by `p + q + 1` integrations by parts.

The book's algorithm uses the `∞`-norm; every statement here holds for any submultiplicative norm
with `‖1‖ = 1`. Neither Mathlib nor Numlib had Padé approximants.
-/

open Polynomial Finset
open scoped Nat

namespace Pade

variable (K : Type*) [Field K]

/-- The **Padé numerator** `N_pq(z) = ∑_{k ≤ p} (p + q - k)! p! / ((p + q)! k! (p - k)!) z^k` of the
exponential ([golub2013matrix] §9.3.1). -/
noncomputable def expNum (p q : ℕ) : K[X] :=
  ∑ k ∈ range (p + 1),
    C (((p + q - k)! * p ! : ℕ) / ((p + q)! * k ! * (p - k)! : ℕ) : K) * X ^ k

/-- The **Padé denominator** `D_pq(z) = N_qp(-z)`. For the diagonal approximants `D_qq(z) =
N_qq(-z)`, the even/odd splitting `N = U + V`, `D = U - V` of [golub2013matrix] §9.3.1. -/
noncomputable def expDen (p q : ℕ) : K[X] :=
  (expNum K q p).comp (-X)

variable {K}

/-- The coefficients of the Padé numerator. -/
theorem coeff_expNum (p q k : ℕ) :
    (expNum K p q).coeff k = if k ≤ p then
      (((p + q - k)! * p ! : ℕ) / ((p + q)! * k ! * (p - k)! : ℕ) : K) else 0 := by
  simp only [expNum, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- Coefficients of `q(-X)`. -/
private theorem coeff_comp_neg_X (f : K[X]) (k : ℕ) :
    (f.comp (-X)).coeff k = (-1) ^ k * f.coeff k := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [add_comp, hf, hg, mul_add]
  | monomial m c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow, ← C_1, ← C_neg,
      ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h
      ring
    · simp

/-- The coefficients of the Padé denominator. -/
theorem coeff_expDen (p q k : ℕ) :
    (expDen K p q).coeff k = if k ≤ q then (-1) ^ k *
      (((p + q - k)! * q ! : ℕ) / ((p + q)! * k ! * (q - k)! : ℕ) : K) else 0 := by
  rw [expDen, coeff_comp_neg_X, coeff_expNum, add_comm q p]
  split_ifs <;> simp

private theorem natCast_factorial_ne_zero [CharZero K] (m : ℕ) : ((m ! : ℕ) : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)

/-- With `q = 0` the numerator is the Taylor polynomial of order `p`. -/
theorem expNum_zero_right [CharZero K] (p : ℕ) :
    expNum K p 0 = ∑ k ∈ range (p + 1), C ((k ! : K)⁻¹) * X ^ k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  rw [add_zero, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  have h1 := natCast_factorial_ne_zero (K := K) (p - k)
  have h2 := natCast_factorial_ne_zero (K := K) p
  have h3 := natCast_factorial_ne_zero (K := K) k
  field_simp

/-- With `q = 0` the denominator is `1`. -/
theorem expDen_zero_right [CharZero K] (p : ℕ) : expDen K p 0 = 1 := by
  ext k
  rw [coeff_expDen, coeff_one]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [le_refl, ite_true, pow_zero, one_mul, Nat.sub_zero, add_zero, Nat.factorial_zero,
      mul_one]
    exact div_self (natCast_factorial_ne_zero p)
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

section Approx

variable (𝕂 : Type*) [Field 𝕂] {𝔸 : Type*} [Ring 𝔸] [Algebra 𝕂 𝔸]

/-- **The `(p, q)` Padé approximant** `R_pq(a) = D_pq(a)⁻¹ N_pq(a)` of the exponential at an element
of a `𝕂`-algebra ([golub2013matrix] §9.3.1; the two factors commute). -/
noncomputable def expApprox (p q : ℕ) (a : 𝔸) : 𝔸 :=
  Ring.inverse (aeval a (expDen 𝕂 p q)) * aeval a (expNum 𝕂 p q)

end Approx

/-- **The Moler–Van Loan constant** `ε(p, q) = 2^{3-(p+q)} p! q! / ((p + q)! (p + q + 1)!)`
([golub2013matrix] §9.3.1). -/
noncomputable def errorBound (p q : ℕ) : ℝ :=
  2 ^ (3 - (p + q : ℤ)) * (p ! * q ! : ℕ) / ((p + q)! * (p + q + 1)! : ℕ)

/-! ### The denominator is invertible for small arguments -/

/-- The coefficients of `D_pq` are bounded by those of the exponential series:
`(p + q - k)! q! ≤ (p + q)! (q - k)!`. -/
theorem factorial_ratio_le_one (p q k : ℕ) (hk : k ≤ q) :
    (((p + q - k)! * q ! : ℕ) : ℝ) ≤ ((p + q)! * (q - k)! : ℕ) := by
  have h1 := Nat.factorial_mul_descFactorial (show k ≤ q from hk)
  have h2 := Nat.factorial_mul_descFactorial (show k ≤ p + q by omega)
  have h3 : q.descFactorial k ≤ (p + q).descFactorial k := Nat.descFactorial_le k (by omega)
  exact_mod_cast (by
    calc (p + q - k)! * q ! = (p + q - k)! * ((q - k)! * q.descFactorial k) := by rw [h1]
      _ ≤ (p + q - k)! * ((q - k)! * (p + q).descFactorial k) := by gcongr
      _ = (p + q)! * (q - k)! := by rw [← h2]; ring)

section Norm

variable {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- The coefficients of `D_pq` are bounded by those of the exponential series. -/
theorem norm_coeff_expDen_le (p q k : ℕ) : ‖(expDen 𝕂 p q).coeff k‖ ≤ 1 / (k ! : ℝ) := by
  rw [coeff_expDen]
  split_ifs with hk
  · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div, RCLike.norm_natCast,
      RCLike.norm_natCast, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h := factorial_ratio_le_one p q k hk
    have hk0 : (0 : ℝ) ≤ (k ! : ℕ) := by positivity
    push_cast at h ⊢
    calc ((p + q - k)! * q ! : ℝ) * k ! ≤ ((p + q)! * (q - k)!) * k ! :=
          mul_le_mul_of_nonneg_right h hk0
      _ = (p + q)! * k ! * (q - k)! := by ring
  · rw [norm_zero]
    positivity

omit [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- The constant coefficient of the Padé denominator is `1`. -/
theorem coeff_expDen_zero (p q : ℕ) : (expDen 𝕂 p q).coeff 0 = 1 := by
  rw [coeff_expDen, ite_eq_left (Nat.zero_le _)]
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.factorial_zero, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr (by positivity))

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- `‖D_pq(a) - 1‖ ≤ e^{‖a‖} - 1`. -/
theorem norm_aeval_expDen_sub_one_le (p q : ℕ) (a : 𝔸) :
    ‖aeval a (expDen 𝕂 p q) - 1‖ ≤ Real.exp ‖a‖ - 1 := by
  rw [aeval_eq_sum_range, Finset.sum_range_succ', coeff_expDen_zero, pow_zero, one_smul,
    add_sub_cancel_right]
  have hexp := Real.sum_le_exp_of_nonneg (norm_nonneg a) ((expDen 𝕂 p q).natDegree + 1)
  rw [Finset.sum_range_succ'] at hexp
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hexp
  have hsum : ∑ k ∈ Finset.range (expDen 𝕂 p q).natDegree, ‖a‖ ^ (k + 1) / ((k + 1)! : ℝ) ≤
      Real.exp ‖a‖ - 1 := by linarith
  refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun k _ => ?_) hsum)
  rw [norm_smul]
  calc ‖(expDen 𝕂 p q).coeff (k + 1)‖ * ‖a ^ (k + 1)‖
      ≤ 1 / ((k + 1)! : ℝ) * ‖a‖ ^ (k + 1) :=
        mul_le_mul (norm_coeff_expDen_le p q (k + 1)) (norm_pow_le' a k.succ_pos)
          (norm_nonneg _) (by positivity)
    _ = ‖a‖ ^ (k + 1) / (k + 1)! := by ring

/-- **The Padé denominator is invertible** for `‖a‖ < log 2` ([golub2013matrix] §9.3.1), with
`‖D_pq(a)⁻¹‖ ≤ 1/(2 - e^{‖a‖})`: `‖D_pq(a) - 1‖ ≤ e^{‖a‖} - 1 < 1` and the Neumann series. In
particular for `‖a‖ ≤ 1/2`. -/
theorem isUnit_aeval_expDen (p q : ℕ) {a : 𝔸} (ha : ‖a‖ < Real.log 2) :
    IsUnit (aeval a (expDen 𝕂 p q)) ∧
      ‖Ring.inverse (aeval a (expDen 𝕂 p q))‖ ≤ 1 / (2 - Real.exp ‖a‖) := by
  have hlt : Real.exp ‖a‖ < 2 := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
    exact Real.exp_lt_exp.mpr ha
  set t : 𝔸 := 1 - aeval a (expDen 𝕂 p q)
  have ht : ‖t‖ ≤ Real.exp ‖a‖ - 1 := by
    rw [norm_sub_rev]
    exact norm_aeval_expDen_sub_one_le p q a
  have ht1 : ‖t‖ < 1 := by linarith
  have hD : aeval a (expDen 𝕂 p q) = 1 - t := by rw [sub_sub_cancel]
  refine ⟨hD ▸ (Units.oneSub t ht1).isUnit, ?_⟩
  rw [hD, ← geom_series_eq_inverse t ht1]
  refine (tsum_geometric_le_of_norm_lt_one t ht1).trans ?_
  rw [norm_one, sub_self, zero_add, one_div]
  exact inv_anti₀ (by linarith) (by linarith)

end Norm

/-! ### The Padé remainder (9.3.1) -/

section Remainder

open NormedSpace intervalIntegral

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The exponential of a complete normed `ℝ`-algebra is continuous. -/
private theorem continuous_exp_real' : Continuous (exp : 𝔸 → 𝔸) :=
  continuous_iff_continuousAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt

/-- The Beta-type weight `P(u) = u^p (1 - u)^q` of the remainder. -/
private noncomputable def weight (p q : ℕ) : ℝ[X] := X ^ p * (1 - X) ^ q

/-- The value of the `j`-th derivative of `P` at `0`: `j!` times its `j`-th coefficient. -/
private theorem iterate_derivative_weight_eval_zero (p q j : ℕ) :
    (derivative^[j] (weight p q)).eval 0 =
      j ! * (if p ≤ j then (-1) ^ (j - p) * ((q.choose (j - p) : ℕ) : ℝ) else 0) := by
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul, weight, coeff_X_pow_mul']
  congr 1
  split_ifs with h
  · have : (1 - X : ℝ[X]) ^ q = C ((-1) ^ q) * (X + C (-1)) ^ q := by
      rw [C_pow, ← mul_pow, map_neg, C_1]
      congr 1
      ring
    rw [this, coeff_C_mul, coeff_X_add_C_pow]
    rcases le_or_gt (j - p) q with hk | hk
    · rw [← mul_assoc, ← pow_add, show q + (q - (j - p)) = 2 * (q - (j - p)) + (j - p) by omega,
        pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    · rw [Nat.choose_eq_zero_of_lt hk]
      simp
  · rfl

/-- The value of the `j`-th derivative of `P` at `1`. -/
private theorem iterate_derivative_weight_eval_one (p q j : ℕ) :
    (derivative^[j] (weight p q)).eval 1 =
      j ! * (if q ≤ j then (-1) ^ q * ((p.choose (j - q) : ℕ) : ℝ) else 0) := by
  have h := Hermite.coeff_taylor_eq_eval_iterate_derivative_div (weight p q) 1 j
  have hj : (j ! : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hj] at h
  rw [← h, mul_comm]
  congr 1
  have ht : taylor (1 : ℝ) (weight p q) = C ((-1) ^ q) * (X ^ q * (X + C 1) ^ p) := by
    simp only [weight, taylor_mul, taylor_pow, map_sub, taylor_one, taylor_X, C_pow, map_neg,
      C_1]
    ring
  rw [ht, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with hq
  · rw [coeff_X_add_C_pow, one_pow, one_mul]
  · rw [mul_zero]

/-- One integration by parts: `a I_j = P^{(j)}(0) e^a - P^{(j)}(1) + I_{j+1}` for
`I_j = ∫₀¹ P^{(j)}(u) e^{(1-u)a} du`. -/
private theorem mul_integral_iterate_derivative (P : ℝ[X]) (a : 𝔸) (j : ℕ) :
    a * ∫ u in (0 : ℝ)..1, (derivative^[j] P).eval u • exp ((1 - u) • a) =
      (derivative^[j] P).eval 0 • exp a - (derivative^[j] P).eval 1 • (1 : 𝔸) +
        ∫ u in (0 : ℝ)..1, (derivative^[j + 1] P).eval u • exp ((1 - u) • a) := by
  set Q := derivative^[j] P
  have hE : ∀ u : ℝ, HasDerivAt (fun u : ℝ => exp ((1 - u) • a)) (-(a * exp ((1 - u) • a))) u :=
    fun u => by
      have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) a (1 - u)).scomp u
        ((hasDerivAt_id' u).const_sub 1)
      simpa [Function.comp_def] using h1
  have hF : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Q.eval u • exp ((1 - u) • a))
      (Q.eval u • -(a * exp ((1 - u) • a)) + (derivative Q).eval u • exp ((1 - u) • a)) u :=
    fun u => (Q.hasDerivAt u).smul (hE u)
  have hcE : Continuous fun u : ℝ => exp ((1 - u) • a) :=
    continuous_exp_real'.comp ((continuous_const.sub continuous_id).smul continuous_const)
  have hint1 : IntervalIntegrable (fun u : ℝ => Q.eval u • exp ((1 - u) • a))
      MeasureTheory.volume 0 1 := (Q.continuous.smul hcE).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun u : ℝ => (derivative Q).eval u • exp ((1 - u) • a))
      MeasureTheory.volume 0 1 := ((derivative Q).continuous.smul hcE).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun u : ℝ => Q.eval u • -(a * exp ((1 - u) • a)))
      MeasureTheory.volume 0 1 :=
    (Q.continuous.smul (continuous_const.mul hcE).neg).intervalIntegrable _ _
  have hFTC := integral_eq_sub_of_hasDerivAt (fun u _ => hF u) (hint3.add hint2)
  rw [integral_add hint3 hint2] at hFTC
  have hmul : ∫ u in (0 : ℝ)..1, Q.eval u • -(a * exp ((1 - u) • a)) =
      -(a * ∫ u in (0 : ℝ)..1, Q.eval u • exp ((1 - u) • a)) := by
    have := (ContinuousLinearMap.mul ℝ 𝔸 a).intervalIntegral_comp_comm hint1
    simp only [ContinuousLinearMap.mul_apply'] at this
    rw [← this, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [smul_neg, mul_smul_comm]
  rw [hmul] at hFTC
  simp only [sub_self, zero_smul, sub_zero, one_smul, NormedSpace.exp_zero] at hFTC
  rw [Function.iterate_succ_apply']
  change a * _ = _ - _ + ∫ u in (0 : ℝ)..1, (derivative Q).eval u • exp ((1 - u) • a)
  rw [← sub_eq_zero, ← neg_eq_zero, ← sub_eq_zero.mpr hFTC]
  abel

/-- Repeated integration by parts:
`a^m I_0 = ∑_{j<m} a^{m-1-j} (P^{(j)}(0) e^a - P^{(j)}(1)) + I_m`. -/
private theorem pow_mul_integral (P : ℝ[X]) (a : 𝔸) (m : ℕ) :
    a ^ m * ∫ u in (0 : ℝ)..1, P.eval u • exp ((1 - u) • a) =
      ∑ j ∈ Finset.range m, a ^ (m - 1 - j) *
        ((derivative^[j] P).eval 0 • exp a - (derivative^[j] P).eval 1 • (1 : 𝔸)) +
      ∫ u in (0 : ℝ)..1, (derivative^[m] P).eval u • exp ((1 - u) • a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, mul_add, mul_integral_iterate_derivative, Finset.mul_sum,
      Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul, ← add_assoc]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    rw [← mul_assoc, ← pow_succ']
    congr 2
    omega

/-- The reversed Taylor sum at `0` of the weight is `(-1)^q (p + q)! D_pq`. -/
private theorem sum_weight_zero (p q : ℕ) :
    ∑ j ∈ Finset.range (p + q + 1),
      C ((derivative^[j] (weight p q)).eval 0) * X ^ (p + q + 1 - 1 - j) =
      C ((-1) ^ q * ((p + q)! : ℝ)) * expDen ℝ p q := by
  ext k
  rw [finsetSum_coeff, coeff_C_mul, coeff_expDen]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single (p + q - k) (fun j hj hjk => by
      rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega), mul_zero])
    (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk)]
  split_ifs with h1 h2 h2
  · rw [mul_one, iterate_derivative_weight_eval_zero, ite_eq_left (by omega)]
    rw [show p + q - k - p = q - k by omega, Nat.choose_symm h2]
    have hk : (-1 : ℝ) ^ (q - k) = (-1) ^ q * (-1) ^ k := by
      rw [← pow_add, show q + k = (q - k) + 2 * k by omega, pow_add, pow_mul]
      simp
    rw [hk, Nat.cast_choose ℝ h2]
    have h3 : ((p + q)! : ℝ) ≠ 0 := by positivity
    have h4 : ((k)! : ℝ) ≠ 0 := by positivity
    have h5 : ((q - k)! : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  · rw [mul_one, iterate_derivative_weight_eval_zero, ite_eq_right (by omega), mul_zero, mul_zero]
  · omega
  · simp

/-- The reversed Taylor sum at `1` of the weight is `(-1)^q (p + q)! N_pq`. -/
private theorem sum_weight_one (p q : ℕ) :
    ∑ j ∈ Finset.range (p + q + 1),
      C ((derivative^[j] (weight p q)).eval 1) * X ^ (p + q + 1 - 1 - j) =
      C ((-1) ^ q * ((p + q)! : ℝ)) * expNum ℝ p q := by
  ext k
  rw [finsetSum_coeff, coeff_C_mul, coeff_expNum]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single (p + q - k) (fun j hj hjk => by
      rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega), mul_zero])
    (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk)]
  split_ifs with h1 h2 h2
  · rw [mul_one, iterate_derivative_weight_eval_one, ite_eq_left (by omega)]
    rw [show p + q - k - q = p - k by omega, Nat.choose_symm h2, Nat.cast_choose ℝ h2]
    have h3 : ((p + q)! : ℝ) ≠ 0 := by positivity
    have h4 : ((k)! : ℝ) ≠ 0 := by positivity
    have h5 : ((p - k)! : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  · rw [mul_one, iterate_derivative_weight_eval_one, ite_eq_right (by omega), mul_zero, mul_zero]
  · omega
  · simp

omit [CompleteSpace 𝔸] in
/-- The value of a reversed Taylor sum at `a`. -/
private theorem aeval_sum_C_mul_X_pow (a : 𝔸) (m : ℕ) (c : ℕ → ℝ) :
    aeval a (∑ j ∈ Finset.range m, C (c j) * X ^ (m - 1 - j)) =
      ∑ j ∈ Finset.range m, c j • a ^ (m - 1 - j) := by
  simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]

/-- **The Padé remainder** ([golub2013matrix] (9.3.1)): when `D_pq(a)` is invertible,
`e^a = R_pq(a) + ((-1)^q/(p + q)!) a^{p+q+1} D_pq(a)⁻¹ ∫₀¹ u^p (1 - u)^q e^{(1-u)a} du`.
Proof: `p + q + 1` integrations by parts of `∫₀¹ P(u) e^{(1-u)a} du`, `P(u) = u^p (1-u)^q`, give
`a^{p+q+1} ∫₀¹ P(u) e^{(1-u)a} du = (-1)^q (p + q)! (D_pq(a) e^a - N_pq(a))`, the boundary terms
being the reversed Taylor sums of `P` at `0` and `1`. -/
theorem exp_eq_expApprox_add (p q : ℕ) (a : 𝔸) (hD : IsUnit (aeval a (expDen ℝ p q))) :
    exp a = expApprox ℝ p q a + ((-1) ^ q / (p + q)! : ℝ) •
      (a ^ (p + q + 1) * Ring.inverse (aeval a (expDen ℝ p q)) *
        ∫ u in (0 : ℝ)..1, (u ^ p * (1 - u) ^ q) • exp ((1 - u) • a)) := by
  set D := aeval a (expDen ℝ p q)
  set Nn := aeval a (expNum ℝ p q)
  set I := ∫ u in (0 : ℝ)..1, (u ^ p * (1 - u) ^ q) • exp ((1 - u) • a)
  set c : ℝ := (-1) ^ q * (p + q)!
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  have hI : I = ∫ u in (0 : ℝ)..1, (weight p q).eval u • exp ((1 - u) • a) := by
    simp [I, weight]
  have hdeg : (weight p q).natDegree < p + q + 1 := by
    have h1 : (X ^ p : ℝ[X]).natDegree ≤ p := natDegree_X_pow_le p
    have h2 : ((1 - X : ℝ[X]) ^ q).natDegree ≤ q := by
      refine (natDegree_pow_le_of_le q (?_ : (1 - X : ℝ[X]).natDegree ≤ 1)).trans (by omega)
      exact (natDegree_sub_le _ _).trans (by simp)
    exact lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add h1 h2)) (by omega)
  have hkey : a ^ (p + q + 1) * I = c • (D * exp a) - c • Nn := by
    rw [hI, pow_mul_integral, iterate_derivative_eq_zero hdeg]
    simp only [eval_zero, zero_smul, intervalIntegral.integral_zero, add_zero]
    have h0 := congrArg (aeval a) (sum_weight_zero p q)
    have h1 := congrArg (aeval a) (sum_weight_one p q)
    rw [aeval_sum_C_mul_X_pow, map_mul, aeval_C, ← Algebra.smul_def] at h0 h1
    simp only [mul_sub, Finset.sum_sub_distrib, mul_smul_comm, mul_one]
    rw [← h1, ← smul_mul_assoc, ← h0, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc]
  -- solve for `e^a`
  obtain ⟨u, hu⟩ := hD
  have hinv : Ring.inverse D * D = 1 := by rw [← hu, Ring.inverse_unit, Units.inv_mul]
  have hcomm : Commute (a ^ (p + q + 1)) (Ring.inverse D) := by
    rw [← hu, Ring.inverse_unit]
    refine Commute.units_inv_right ?_
    rw [hu]
    have : Commute (aeval a (X ^ (p + q + 1) : ℝ[X])) (aeval a (expDen ℝ p q)) := by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
    simpa using this
  have hEa : D * exp a = Nn + c⁻¹ • (a ^ (p + q + 1) * I) := by
    rw [hkey, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, one_smul]
    abel
  have hcinv : c⁻¹ = (-1) ^ q / (p + q)! := by
    simp only [c]
    rw [mul_inv, ← inv_pow, inv_neg, inv_one, div_eq_mul_inv]
  calc exp a = Ring.inverse D * (D * exp a) := by rw [← mul_assoc, hinv, one_mul]
    _ = _ := by
      rw [hEa, mul_add, mul_smul_comm, ← mul_assoc, ← hcomm.eq, expApprox, hcinv]

end Remainder

/-! ### The Moler–Van Loan backward error bound -/

section MolerVanLoan

open NormedSpace intervalIntegral

/-- The constant `K = p! q!/((p + q)! (p + q + 1)!)` of the Moler–Van Loan bound. -/
private noncomputable def mvlConst (p q : ℕ) : ℝ :=
  (p ! * q ! : ℕ) / ((p + q)! * (p + q + 1)! : ℕ)

private theorem mvlConst_nonneg (p q : ℕ) : 0 ≤ mvlConst p q := by
  unfold mvlConst; positivity

private theorem errorBound_eq (p q : ℕ) :
    errorBound p q = 8 * mvlConst p q * (1 / 2) ^ (p + q) := by
  rw [errorBound, mvlConst, show (3 : ℤ) - (p + q : ℤ) = ((3 : ℕ) : ℤ) - ((p + q : ℕ) : ℤ) by
    push_cast; ring, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, one_div, inv_pow]
  field_simp
  ring

/-- `-log (1 - y) ≤ T x` from `y ≤ M x ≤ r < 1` and `M ≤ (1 - r) T`. -/
private theorem neg_log_one_sub_le_of_le {y M x r T : ℝ} (hy0 : 0 ≤ y) (hyM : y ≤ M * x)
    (hMx : M * x ≤ r) (hr : r < 1) (hx : 0 ≤ x) (hM : M ≤ (1 - r) * T) :
    y < 1 ∧ -Real.log (1 - y) ≤ T * x := by
  have h1 : 0 < 1 - y := by linarith
  refine ⟨by linarith, ?_⟩
  have h2 : -Real.log (1 - y) ≤ (1 - y)⁻¹ - 1 := by
    rw [← Real.log_inv]
    exact Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  have h3 : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
  rw [h3] at h2
  refine h2.trans ?_
  rw [div_le_iff₀ h1]
  have h4 : y ≤ (1 - r) * T * x := hyM.trans (mul_le_mul_of_nonneg_right hM hx)
  have hTx : 0 ≤ T * x := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right (show 1 - r ≤ 1 - y by linarith) hTx]

/-- The scalar inequality behind the Moler–Van Loan bound: with `K = mvlConst p q`,
`0 ≤ x ≤ 1/2` and `0 ≤ y ≤ K x^{p+q+1} e^x β`, where `β ≤ 2` when `p + q = 1` and
`β ≤ 1/(2 - e^x)` when `p + q ≥ 2`, one has `y < 1` and `-log(1 - y) ≤ ε(p, q) x`. -/
private theorem mvl_scalar (p q : ℕ) (hpq : 1 ≤ p + q) {x y β : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) (hβ0 : 0 ≤ β)
    (hβ : (p + q = 1 → β ≤ 2) ∧ (2 ≤ p + q → β ≤ 1 / (2 - Real.exp x))) (hy0 : 0 ≤ y)
    (hy : y ≤ mvlConst p q * x ^ (p + q + 1) * Real.exp x * β) :
    y < 1 ∧ -Real.log (1 - y) ≤ errorBound p q * x := by
  have hK := mvlConst_nonneg p q
  have hexp : Real.exp x ≤ 1.6488 := by
    have h1 : Real.exp x ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hx
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (1 / 2)]
  have hexp1 : 1 ≤ Real.exp x := Real.one_le_exp hx0
  set s : ℝ := (1 / 2) ^ (p + q)
  have hs0 : 0 ≤ s := by positivity
  have hxs : x ^ (p + q + 1) ≤ x * s := by
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx _) hx0
  rw [errorBound_eq]
  rcases Nat.lt_or_ge (p + q) 2 with hn | hn
  · -- `p + q = 1`: `K = 1/2`, `s = 1/2`, `β ≤ 2`
    have hn1 : p + q = 1 := by omega
    have hKv : mvlConst p q = 1 / 2 := by
      unfold mvlConst
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp; obtain rfl : q = 1 := by omega
        norm_num
      · obtain rfl : p = 1 := by omega
        obtain rfl : q = 0 := by omega
        norm_num
    have hβ2 := hβ.1 hn1
    have hs' : x ^ (p + q + 1) ≤ x * (1 / 2) := by
      rw [hn1]
      calc x ^ (1 + 1) = x * x := by ring
        _ ≤ x * (1 / 2) := mul_le_mul_of_nonneg_left hx hx0
    rw [hKv] at hy
    rw [hKv, hn1]
    refine neg_log_one_sub_le_of_le (M := 0.8244) (r := 0.4122) hy0 ?_ ?_ (by norm_num) hx0
      (by norm_num)
    · calc y ≤ 1 / 2 * x ^ (p + q + 1) * Real.exp x * β := hy
        _ ≤ 1 / 2 * (x * (1 / 2)) * 1.6488 * 2 := by gcongr
        _ = 0.8244 * x := by ring
    · nlinarith
  · -- `p + q ≥ 2`: `K ≤ 1/6`, `s ≤ 1/4`, `β ≤ 1/(2 - e^x) ≤ 2.8475`
    have hK6 : mvlConst p q ≤ 1 / 6 := by
      unfold mvlConst
      have h1 : p ! * q ! ≤ (p + q)! :=
        Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add p q)
      have h2 : 3 ! ≤ (p + q + 1)! := Nat.factorial_le (by omega)
      rw [div_le_iff₀ (by positivity)]
      have h3 : ((p ! * q ! : ℕ) : ℝ) ≤ (p + q)! := by exact_mod_cast h1
      have h4 : (6 : ℝ) ≤ (p + q + 1)! := by
        have : ((3 ! : ℕ) : ℝ) ≤ ((p + q + 1)! : ℕ) := by exact_mod_cast h2
        simpa [Nat.factorial] using this
      push_cast at h3 ⊢
      have h5 : (0 : ℝ) ≤ (p + q)! := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
    have hs4 : s ≤ 1 / 4 := by
      calc s = (1 / 2) ^ (p + q) := rfl
        _ ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
        _ = 1 / 4 := by norm_num
    have hβ3 : β ≤ 2.8475 := by
      refine (hβ.2 hn).trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    set K := mvlConst p q
    refine neg_log_one_sub_le_of_le (M := 4.7 * K * s) (r := 0.1) hy0 ?_ ?_ (by norm_num) hx0 ?_
    · calc y ≤ K * x ^ (p + q + 1) * Real.exp x * β := hy
        _ ≤ K * (x * s) * 1.6488 * 2.8475 := by gcongr
        _ ≤ 4.7 * K * s * x := by nlinarith [mul_nonneg (mul_nonneg hK hs0) hx0]
    · calc 4.7 * K * s * x ≤ 4.7 * (1 / 6) * (1 / 4) * (1 / 2) := by gcongr
        _ ≤ 0.1 := by norm_num
    · nlinarith [mul_nonneg hK hs0]

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- `‖e^x‖ ≤ e^{‖x‖}` in a real normed algebra with `‖1‖ = 1`. -/
private theorem norm_exp_le_exp_norm' (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have hx := exp_series_hasSum_exp' (𝕂 := ℝ) x
  have hr := exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  rw [← Real.exp_eq_exp_ℝ] at hr
  refine hx.norm_le_of_bounded hr fun n => ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

/-- `‖e^x - 1‖ ≤ ‖x‖ e^{‖x‖}`. -/
private theorem norm_exp_sub_one_le' (x : 𝔸) : ‖exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have hx := (hasSum_nat_add_iff' 1).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have hr := (hasSum_nat_add_iff' 1).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_smul] at hx hr
  rw [← Real.exp_eq_exp_ℝ] at hr
  refine (hx.norm_le_of_bounded hr fun n => ?_).trans ?_
  · rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x _) (by positivity)
  · have h := Real.add_one_le_exp (-‖x‖)
    have h2 : Real.exp (-‖x‖) * Real.exp ‖x‖ = 1 := by rw [← Real.exp_add, neg_add_cancel,
      Real.exp_zero]
    nlinarith [Real.exp_pos ‖x‖, norm_nonneg x]

omit [NormOneClass 𝔸] in
private theorem exp_add_of_commute' {x y : 𝔸} (h : Commute x y) :
    exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

omit [NormOneClass 𝔸] in
private theorem exp_nsmul' (m : ℕ) (x : 𝔸) : exp (m • x) = exp x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [succ_nsmul, exp_add_of_commute' ((Commute.refl x).smul_left m), ih, pow_succ]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem commute_aeval_of_commute {x a : 𝔸} (h : Commute x a) (P : ℝ[X]) :
    Commute x (aeval a P) := by
  induction P using Polynomial.induction_on with
  | C c => simpa using Algebra.commute_algebraMap_right c x
  | add p q hp hq => simpa using hp.add_right hq
  | monomial n c _ => simpa using
      (Algebra.commute_algebraMap_right c x).mul_right (h.pow_right (n + 1))

omit [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem commute_ring_inverse {x D : 𝔸} (hD : IsUnit D) (h : Commute x D) :
    Commute x (Ring.inverse D) := by
  obtain ⟨u, rfl⟩ := hD
  rw [Ring.inverse_unit]
  exact h.units_inv_right

/-- The core of the Moler–Van Loan bound for `‖a‖ ≤ 1/2`, given a bound `β` on the inverse Padé
denominator: `R_pq(a) = e^{a + e}` with `e` commuting with `a` and `‖e‖ ≤ ε(p, q) ‖a‖`. -/
private theorem exists_expApprox_eq_exp_add_of_norm_inverse_le (p q : ℕ) (hpq : 1 ≤ p + q)
    {a : 𝔸} (ha : ‖a‖ ≤ 1 / 2) (hD : IsUnit (aeval a (expDen ℝ p q))) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : ‖Ring.inverse (aeval a (expDen ℝ p q))‖ ≤ β)
    (hβ' : (p + q = 1 → β ≤ 2) ∧ (2 ≤ p + q → β ≤ 1 / (2 - Real.exp ‖a‖))) :
    ∃ e : 𝔸, Commute a e ∧ ‖e‖ ≤ errorBound p q * ‖a‖ ∧ expApprox ℝ p q a = exp (a + e) := by
  set D := aeval a (expDen ℝ p q)
  set Dinv := Ring.inverse D
  set c : ℝ := (-1) ^ q / (p + q)!
  set I := ∫ u in (0 : ℝ)..1, (u ^ p * (1 - u) ^ q) • exp ((1 - u) • a)
  set J := ∫ u in (0 : ℝ)..1, (u ^ p * (1 - u) ^ q) • exp (-(u • a))
  set F := exp (-a)
  set P := a ^ (p + q + 1)
  have hrem : exp a = expApprox ℝ p q a + c • (P * Dinv * I) := exp_eq_expApprox_add p q a hD
  have hcF : Commute F a := ((Commute.refl a).neg_left).exp_left
  have hcFD : Commute F Dinv := commute_ring_inverse hD (commute_aeval_of_commute hcF _)
  have hcFP : Commute F P := hcF.pow_right _
  have hFE : F * exp a = 1 := by
    rw [← exp_add_of_commute' ((Commute.refl a).neg_left), neg_add_cancel, exp_zero]
  have hEF : exp a * F = 1 := by
    rw [← exp_add_of_commute' ((Commute.refl a).neg_right), add_neg_cancel, exp_zero]
  have hw : Continuous fun u : ℝ => u ^ p * (1 - u) ^ q := by fun_prop
  have hcI : Continuous fun u : ℝ => (u ^ p * (1 - u) ^ q) • exp ((1 - u) • a) :=
    hw.smul (continuous_exp_real'.comp ((continuous_const.sub continuous_id).smul
      continuous_const))
  have hcJ : Continuous fun u : ℝ => (u ^ p * (1 - u) ^ q) • exp (-(u • a)) :=
    hw.smul (continuous_exp_real'.comp (continuous_id.smul continuous_const).neg)
  have hFI : F * I = J := by
    have := (ContinuousLinearMap.mul ℝ 𝔸 F).intervalIntegral_comp_comm
      (hcI.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    simp only [ContinuousLinearMap.mul_apply'] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [mul_smul_comm, ← exp_add_of_commute' (((Commute.refl a).smul_right _).neg_left)]
    congr 2
    rw [sub_smul, one_smul]
    abel
  have hT : F * (P * Dinv * I) = P * Dinv * J := by
    rw [← mul_assoc, (hcFP.mul_right hcFD).eq, mul_assoc, hFI]
  set h := -(c • (P * Dinv * J)) with hh_def
  have hRF : F * expApprox ℝ p q a = 1 + h := by
    have h0 := congrArg (F * ·) hrem
    simp only [mul_add, mul_smul_comm, hT, hFE] at h0
    rw [h0, hh_def]
    abel
  -- the norm of `h`
  have hJ : ‖J‖ ≤ Real.exp ‖a‖ * (p ! * q ! / (p + q + 1)! : ℝ) := by
    rw [← _root_.integral_pow_mul_one_sub_pow, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) zero_le_one
      (Filter.Eventually.of_forall fun u hu => ?_)
      ((continuous_const.mul hw).intervalIntegrable _ _)
    have hu0 : 0 ≤ u := hu.1.le
    have hu1 : u ≤ 1 := hu.2
    have hwu : 0 ≤ u ^ p * (1 - u) ^ q := mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith) _)
    rw [norm_smul, Real.norm_of_nonneg hwu, mul_comm]
    refine mul_le_mul_of_nonneg_right ((norm_exp_le_exp_norm' _).trans
      (Real.exp_le_exp.mpr ?_)) hwu
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hu0]
    nlinarith [norm_nonneg a]
  have hh : ‖h‖ ≤ mvlConst p q * ‖a‖ ^ (p + q + 1) * Real.exp ‖a‖ * β := by
    have hc : ‖c‖ = 1 / (p + q)! := by
      simp only [c, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast]
    calc ‖h‖ = ‖c‖ * ‖P * Dinv * J‖ := by rw [norm_neg, norm_smul]
      _ ≤ ‖c‖ * (‖a‖ ^ (p + q + 1) * β * (Real.exp ‖a‖ * (p ! * q ! / (p + q + 1)! : ℝ))) := by
          gcongr
          exact (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
            (mul_le_mul (norm_pow_le _ _) hβ (norm_nonneg _) (by positivity))) hJ (norm_nonneg _)
            (by positivity))
      _ = mvlConst p q * ‖a‖ ^ (p + q + 1) * Real.exp ‖a‖ * β := by
          rw [hc, mvlConst]
          push_cast
          field_simp
  obtain ⟨hh1, hlog⟩ := mvl_scalar p q hpq (norm_nonneg a) ha hβ0 hβ' (norm_nonneg h) hh
  -- the logarithm of `1 + h`
  set e' := NormedSpace.log (1 + h)
  have hexp : exp e' = 1 + h := exp_log_of_norm_sub_one_lt (by rwa [add_sub_cancel_left])
  have hnorm : ‖e'‖ ≤ -Real.log (1 - ‖h‖) := by
    have := norm_log_le ℝ (x := 1 + h) (by rwa [add_sub_cancel_left])
    rwa [add_sub_cancel_left] at this
  have hcaJ : Commute a J := by
    have h1 := (ContinuousLinearMap.mul ℝ 𝔸 a).intervalIntegral_comp_comm
      (hcJ.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    have h2 := ((ContinuousLinearMap.mul ℝ 𝔸).flip a).intervalIntegral_comp_comm
      (hcJ.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at h1 h2
    change a * J = J * a
    rw [← h1, ← h2]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [mul_smul_comm, smul_mul_assoc]
    rw [((((Commute.refl a).smul_right u).neg_right).exp_right).eq]
  have hcah : Commute a h :=
    (((((Commute.refl a).pow_right _).mul_right (commute_ring_inverse hD
      (commute_aeval_of_commute (Commute.refl a) _))).mul_right hcaJ).smul_right c).neg_right
  have hce : Commute a e' := ((Commute.one_right a).add_right hcah).log_right
  refine ⟨e', hce, hnorm.trans hlog, ?_⟩
  calc expApprox ℝ p q a = exp a * (F * expApprox ℝ p q a) := by rw [← mul_assoc, hEF, one_mul]
    _ = exp a * exp e' := by rw [hRF, hexp]
    _ = exp (a + e') := (exp_add_of_commute' hce).symm

private theorem expDen_zero_one : expDen ℝ 0 1 = 1 - X := by
  ext k
  rw [coeff_expDen, coeff_sub, coeff_one, coeff_X]
  rcases k with _ | _ | k <;> norm_num

/-- The Moler–Van Loan bound for `‖a‖ ≤ 1/2` (one squaring step removed). -/
private theorem exists_expApprox_eq_exp_add (p q : ℕ) {a : 𝔸} (ha : ‖a‖ ≤ 1 / 2) :
    ∃ e : 𝔸, Commute a e ∧ ‖e‖ ≤ errorBound p q * ‖a‖ ∧ expApprox ℝ p q a = exp (a + e) := by
  have hlog2 : ‖a‖ < Real.log 2 := by linarith [Real.log_two_gt_d9]
  obtain ⟨hDu, hDinv⟩ := isUnit_aeval_expDen (𝕂 := ℝ) p q hlog2
  rcases Nat.eq_zero_or_pos (p + q) with h0 | hpos
  · -- `p = q = 0`: `R = 1`
    obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
    refine ⟨-a, (Commute.refl a).neg_right, ?_, ?_⟩
    · rw [norm_neg]
      have : errorBound 0 0 = 8 := by norm_num [errorBound]
      rw [this]
      nlinarith [norm_nonneg a]
    · rw [add_neg_cancel, exp_zero, expApprox, expDen_zero_right, expNum_zero_right]
      simp
  rcases Nat.lt_or_ge (p + q) 2 with hn | hn
  · have hn1 : p + q = 1 := by omega
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      refine exists_expApprox_eq_exp_add_of_norm_inverse_le p 0 hpos ha hDu zero_le_one ?_
        ⟨fun _ => by norm_num, fun h => by omega⟩
      rw [expDen_zero_right, map_one, Ring.inverse_one, norm_one]
    · obtain rfl : q = 1 := by omega
      obtain rfl : p = 0 := by omega
      have ha1 : ‖a‖ < 1 := by linarith
      refine exists_expApprox_eq_exp_add_of_norm_inverse_le 0 1 hpos ha hDu (β := 2)
        zero_le_two ?_ ⟨fun _ => le_rfl, fun h => by omega⟩
      rw [expDen_zero_one, map_sub, map_one, aeval_X, ← geom_series_eq_inverse a ha1]
      refine (tsum_geometric_le_of_norm_lt_one a ha1).trans ?_
      rw [norm_one, sub_self, zero_add, inv_le_comm₀ (by linarith) two_pos]
      linarith
  · have h2e : Real.exp ‖a‖ < 2 := by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
      exact Real.exp_lt_exp.mpr hlog2
    exact exists_expApprox_eq_exp_add_of_norm_inverse_le p q hpos ha hDu
      (by rw [one_div]; exact inv_nonneg.mpr (by linarith)) hDinv
      ⟨fun h => by omega, fun _ => le_rfl⟩

/-- **The Moler–Van Loan backward error bound** ([golub2013matrix] §9.3.1, quoted from Moler–Van
Loan (1978)): in a complete normed `ℝ`-algebra with `‖1‖ = 1` (complex matrices included, through
`NormedAlgebra.complexToReal`), if `‖a / 2^j‖ ≤ 1/2` then the scaled-and-squared Padé approximant
is an exact exponential of a perturbed argument: `R_pq(a / 2^j)^{2^j} = e^{a + e}` with `e`
commuting with `a` and `‖e‖ ≤ ε(p, q) ‖a‖`. Proof: (9.3.1) gives `e^{-a'} R_pq(a') = 1 + h` with
`‖h‖ ≤ K ‖a'‖^{p+q+1} e^{‖a'‖} ‖D_pq(a')⁻¹‖` (the Beta integral `p! q!/(p + q + 1)!`), and
`e' = log(1 + h)` has `‖e'‖ ≤ -log(1 - ‖h‖) ≤ ε ‖a'‖`; the constant needs the exact denominators
`D_10 = 1` and `D_01 = 1 - z` when `p + q = 1` (with `‖D_01(a')⁻¹‖ ≤ 1/(1 - ‖a'‖)`, the general
`1/(2 - e^{‖a'‖})` is too weak there), and at `p = q = 0`, `e = -a`. -/
theorem exists_exp_add_eq_expApprox_pow (p q j : ℕ) {a : 𝔸} (ha : ‖a‖ ≤ 2 ^ j / 2) :
    ∃ e : 𝔸, Commute a e ∧ ‖e‖ ≤ errorBound p q * ‖a‖ ∧
      expApprox ℝ p q ((2⁻¹ : ℝ) ^ j • a) ^ (2 ^ j) = exp (a + e) := by
  set a' : 𝔸 := (2⁻¹ : ℝ) ^ j • a
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hx : ‖a'‖ = ‖a‖ / 2 ^ j := by
    rw [norm_smul, norm_pow, norm_inv, Real.norm_two, inv_pow, div_eq_inv_mul]
  have hx2 : ‖a'‖ ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ h2j]
    linarith
  have hback : ((2 ^ j : ℕ) : ℝ) • a' = a := by
    simp only [a', smul_smul, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow,
      mul_inv_cancel₀ (two_ne_zero' ℝ), one_pow, one_smul]
  obtain ⟨e', hc, hn, he⟩ := exists_expApprox_eq_exp_add p q hx2
  refine ⟨((2 ^ j : ℕ) : ℝ) • e', ?_, ?_, ?_⟩
  · rw [← hback]
    exact (hc.smul_left _).smul_right _
  · rw [norm_smul, Real.norm_natCast, Nat.cast_pow, Nat.cast_ofNat]
    calc 2 ^ j * ‖e'‖ ≤ 2 ^ j * (errorBound p q * ‖a'‖) :=
          mul_le_mul_of_nonneg_left hn h2j.le
      _ = errorBound p q * ‖a‖ := by rw [hx]; field_simp
  · rw [he, ← exp_nsmul', ← hback, ← smul_add, Nat.cast_smul_eq_nsmul]

/-- **The relative error of scaling and squaring** ([golub2013matrix] §9.3.1): under the hypotheses
of `Pade.exists_exp_add_eq_expApprox_pow`, with `F = R_pq(a/2^j)^{2^j}` and `ε = ε(p, q)`,
`‖e^a - F‖ ≤ ε ‖a‖ e^{ε ‖a‖} ‖e^a‖`: `F - e^a = e^a (e^e - 1)`. -/
theorem norm_exp_sub_expApprox_pow_le (p q j : ℕ) {a : 𝔸} (ha : ‖a‖ ≤ 2 ^ j / 2) :
    ‖exp a - expApprox ℝ p q ((2⁻¹ : ℝ) ^ j • a) ^ (2 ^ j)‖ ≤
      errorBound p q * ‖a‖ * Real.exp (errorBound p q * ‖a‖) * ‖exp a‖ := by
  obtain ⟨e, hc, hn, he⟩ := exists_exp_add_eq_expApprox_pow p q j ha
  have hd : exp a - exp a * exp e = -(exp a * (exp e - 1)) := by noncomm_ring
  rw [he, exp_add_of_commute' hc, hd, norm_neg]
  calc ‖exp a * (exp e - 1)‖ ≤ ‖exp a‖ * (‖e‖ * Real.exp ‖e‖) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_exp_sub_one_le' e)
          (norm_nonneg _))
    _ ≤ ‖exp a‖ * (errorBound p q * ‖a‖ * Real.exp (errorBound p q * ‖a‖)) := by
        have h0 : 0 ≤ errorBound p q * ‖a‖ :=
          mul_nonneg (by rw [errorBound]; positivity) (norm_nonneg a)
        exact mul_le_mul_of_nonneg_left (mul_le_mul hn (Real.exp_le_exp.mpr hn)
          (Real.exp_pos _).le h0) (norm_nonneg _)
    _ = _ := by ring

end MolerVanLoan

end Pade
