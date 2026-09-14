/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.RingTheory.Polynomial.Chebyshev`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact

/-!
# Chebyshev min–max on an interval

The classical Chebyshev min–max theorem on an interval,
`min {max_{t ∈ [a,b]} |p t| : deg p ≤ m, p γ = 1} = 1 / |T_m(1 + 2(a - γ)/(b - a))|` for
`γ ∉ [a, b]`, its special case `γ = 0`, and the growth estimates for `T_m` that turn it into the
geometric rates used in Krylov-method error bounds.
Mathlib supplies `Polynomial.Chebyshev.T` and the extremal inequality
`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`.

The last theorem of the file leaves the single interval: for a spectrum split into two intervals
on either side of the origin, composing the shifted Chebyshev polynomial with a quadratic that
fixes the origin and maps both intervals onto one gives the corresponding geometric bound.

## Main definitions

* `Polynomial.Chebyshev.shifted m a b γ`: the Chebyshev polynomial of degree `m` transplanted to
  `[a, b]` by an affine change of variable and normalized to `1` at `γ`.

## Main results

* `Polynomial.Chebyshev.one_div_eval_T_le_sSup_abs_eval` and
  `Polynomial.Chebyshev.sSup_abs_eval_shifted`: the min–max value, as a lower bound over the
  admissible polynomials and as the value `Polynomial.Chebyshev.shifted` attains;
  `Polynomial.Chebyshev.one_div_eval_T_le_sSup_abs_eval_of_eval_zero` is the case `γ = 0`.
* `Polynomial.Chebyshev.one_div_eval_T_le_two_mul_pow`: the growth estimate
  `1 / T_m((κ + 1)/(κ - 1)) ≤ 2 ((√κ - 1)/(√κ + 1))^m`, which is where the `√κ` rate of a Krylov
  method on a system of condition number `κ` comes from.
* `Polynomial.Chebyshev.exists_eval_zero_eq_one_abs_le_of_union_Icc`: the two-interval bound.
-/

open Polynomial Polynomial.Chebyshev

namespace Polynomial.Chebyshev

/-- Closed form `T_m x = ½ ((x + √(x²-1))^m + (x - √(x²-1))^m)` for `x ≥ 1`. -/
theorem eval_T_eq_half_add_pow {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    (T ℝ m).eval x =
      ((x + Real.sqrt (x ^ 2 - 1)) ^ m + (x - Real.sqrt (x ^ 2 - 1)) ^ m) / 2 := by
  have hexp : Real.exp (Real.arcosh x) = x + Real.sqrt (x ^ 2 - 1) := Real.exp_arcosh hx
  have hexpn : Real.exp (-Real.arcosh x) = x - Real.sqrt (x ^ 2 - 1) := by
    rw [Real.exp_neg, hexp, Real.add_sqrt_self_sq_sub_one_inv hx]
  have hkey := T_real_cosh (Real.arcosh x) (m : ℤ)
  rw [Real.cosh_arcosh hx] at hkey
  have hcast : ((m : ℤ) : ℝ) = (m : ℝ) := by push_cast; ring
  rw [hkey, Real.cosh_eq, hcast, Real.exp_nat_mul, hexp,
    show -((m : ℝ) * Real.arcosh x) = (m : ℝ) * -Real.arcosh x by ring,
    Real.exp_nat_mul, hexpn]

/-- `½ (x + √(x²-1))^m ≤ T_m x` for `x ≥ 1`. -/
theorem half_pow_le_eval_T {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    (x + Real.sqrt (x ^ 2 - 1)) ^ m / 2 ≤ (T ℝ m).eval x := by
  rw [eval_T_eq_half_add_pow hx]
  have hle : Real.sqrt (x ^ 2 - 1) ≤ x := by
    have h1 : Real.sqrt (x ^ 2 - 1) ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq (by linarith)] at h1
  have := pow_nonneg (by linarith : (0:ℝ) ≤ x - Real.sqrt (x ^ 2 - 1)) m
  linarith

/-- To the right of the oscillation interval `T_m` is at least `1`, so the min–max value
`1 / T_m(·)` is a genuine contraction factor and no absolute value is needed around it. -/
theorem one_le_eval_T {x : ℝ} (hx : 1 ≤ x) (m : ℕ) : 1 ≤ (T ℝ m).eval x :=
  one_le_eval_T_real _ hx

/-- The shifted Chebyshev polynomial `t ↦ T_m((b + a - 2t)/(b - a)) / T_m((b + a - 2γ)/(b - a))`,
normalized to `1` at `γ`. -/
noncomputable def shifted (m : ℕ) (a b γ : ℝ) : ℝ[X] :=
  Polynomial.C (1 / (T ℝ m).eval ((b + a - 2 * γ) / (b - a))) *
    (T ℝ m).comp (Polynomial.C ((b + a) / (b - a)) - Polynomial.C (2 / (b - a)) * X)

/-- `shifted m a b γ` has degree at most `m`: the affine change of variable does not raise the
degree. Half of what makes it an admissible competitor in the min–max problem. -/
theorem shifted_degree_le (m : ℕ) (a b γ : ℝ) : (shifted m a b γ).degree ≤ m := by
  have hlin : (Polynomial.C ((b + a) / (b - a)) -
      Polynomial.C (2 / (b - a)) * X : ℝ[X]).natDegree ≤ 1 := by
    compute_degree
  have hT : (T ℝ (m : ℤ)).natDegree = m := by rw [natDegree_T, Int.natAbs_natCast]
  refine Polynomial.degree_le_of_natDegree_le ?_
  rw [shifted]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine Polynomial.natDegree_comp_le.trans ?_
  rw [hT]
  simpa using Nat.mul_le_mul_left m hlin

/-- The evaluation of `shifted` as a ratio of Chebyshev values. -/
private theorem eval_shifted (m : ℕ) {a b : ℝ} (hab : a < b) (γ t : ℝ) :
    (shifted m a b γ).eval t
      = (T ℝ (m : ℤ)).eval ((b + a - 2 * t) / (b - a)) /
        (T ℝ (m : ℤ)).eval ((b + a - 2 * γ) / (b - a)) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  rw [shifted, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  rw [show (b + a) / (b - a) - 2 / (b - a) * t = (b + a - 2 * t) / (b - a) by field_simp]
  ring

/-- The affine change of variable `t ↦ (b + a - 2t)/(b - a)` maps `[a, b]` into `[-1, 1]`. -/
private theorem abs_shift_le_one {a b t : ℝ} (hab : a < b) (ht : t ∈ Set.Icc a b) :
    |(b + a - 2 * t) / (b - a)| ≤ 1 := by
  have hd : 0 < b - a := by linarith
  rw [abs_div, abs_of_pos hd, div_le_one hd]
  exact abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- A point outside `[a, b]` is mapped outside `[-1, 1]`. -/
private theorem one_lt_abs_shift {a b γ : ℝ} (hab : a < b) (hγ : γ ∉ Set.Icc a b) :
    1 < |(b + a - 2 * γ) / (b - a)| := by
  have hd : 0 < b - a := by linarith
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hγ
  rcases hγ with h | h
  · exact lt_of_lt_of_le (by rw [lt_div_iff₀ hd]; linarith) (le_abs_self _)
  · exact lt_of_lt_of_le (by
      have : (b + a - 2 * γ) / (b - a) < -1 := by rw [div_lt_iff₀ hd]; linarith
      linarith) (neg_le_abs _)

/-- `|T_m|` is unchanged by a sign change of its argument, `T_m` being even or odd with `m`. -/
private theorem abs_eval_T_neg (m : ℕ) (z : ℝ) :
    |(T ℝ (m : ℤ)).eval (-z)| = |(T ℝ (m : ℤ)).eval z| := by
  simp [T_eval_neg, abs_mul]

/-- `shifted m a b γ` takes the value `1` at the normalization point `γ`, the other half of what
makes it admissible. The hypothesis `γ ∉ [a, b]` is what keeps the normalizing denominator
`T_m((b + a - 2γ)/(b - a))` away from zero. -/
theorem shifted_eval_self (m : ℕ) {a b γ : ℝ} (hab : a < b) (hγ : γ ∉ Set.Icc a b) :
    (shifted m a b γ).eval γ = 1 := by
  have hTne : (T ℝ (m : ℤ)).eval ((b + a - 2 * γ) / (b - a)) ≠ 0 := by
    have h := one_le_abs_eval_T_real (m : ℤ) (one_lt_abs_shift hab hγ).le
    intro hz
    rw [hz, abs_zero] at h
    linarith
  rw [eval_shifted m hab, div_self hTne]

/-- The extremal property of `T_m` outside `[-1, 1]`: a real polynomial of degree at most `m`
bounded by `1` on `[-1, 1]` is bounded by `|T_m|` at any point of absolute value at least `1`. -/
private theorem eval_le_abs_eval_T {m : ℕ} {P : ℝ[X]} (hdeg : P.degree ≤ m)
    (hbnd : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |P.eval y| ≤ 1) {z : ℝ} (hz : 1 ≤ |z|) :
    P.eval z ≤ |(T ℝ (m : ℤ)).eval z| := by
  rcases le_or_gt 1 z with hz1 | hz1
  · have h := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0) hz1 hdeg hbnd
    simp only [Function.iterate_zero, id_eq] at h
    exact h.trans (le_abs_self _)
  · have hzn : 1 ≤ -z := by
      rcases abs_cases z with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hQdeg : (P.comp (-X : ℝ[X])).degree ≤ m := by
      refine Polynomial.degree_le_of_natDegree_le (Polynomial.natDegree_comp_le.trans ?_)
      rw [show (-X : ℝ[X]).natDegree = 1 by simp, mul_one]
      exact Polynomial.natDegree_le_of_degree_le hdeg
    have hQbnd : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(P.comp (-X : ℝ[X])).eval y| ≤ 1 := by
      intro y hy
      rw [Polynomial.eval_comp]
      simp only [Polynomial.eval_neg, Polynomial.eval_X]
      exact hbnd (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have h := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0) hzn hQdeg hQbnd
    simp only [Function.iterate_zero, id_eq, Polynomial.eval_comp, Polynomial.eval_neg,
      Polynomial.eval_X, neg_neg] at h
    calc P.eval z ≤ (T ℝ (m : ℤ)).eval (-z) := h
      _ ≤ |(T ℝ (m : ℤ)).eval (-z)| := le_abs_self _
      _ = |(T ℝ (m : ℤ)).eval z| := abs_eval_T_neg m z

/-- The modulus of a polynomial attains a maximum on a nonempty compact interval. -/
private theorem exists_isGreatest_abs_eval (p : ℝ[X]) {a b : ℝ} (hab : a ≤ b) :
    ∃ M, IsGreatest ((fun t => |p.eval t|) '' Set.Icc a b) M :=
  (isCompact_Icc.image p.continuous.abs).exists_isGreatest
    ((Set.nonempty_Icc.mpr hab).image _)

/-- Lower bound (general normalization point `γ ∉ [a, b]`): every polynomial of degree `≤ m`
with `p γ = 1` has sup over `[a, b]` at least `1 / |T_m((b + a - 2γ)/(b - a))|`. -/
theorem one_div_eval_T_le_sSup_abs_eval (m : ℕ) {a b γ : ℝ} (hab : a < b)
    (hγ : γ ∉ Set.Icc a b) (p : ℝ[X]) (hp : p.degree ≤ m) (hpγ : p.eval γ = 1) :
    1 / |(T ℝ m).eval ((b + a - 2 * γ) / (b - a))| ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc a b) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  obtain ⟨M, hMmem, hMub⟩ := exists_isGreatest_abs_eval p hab.le
  rw [IsGreatest.csSup_eq ⟨hMmem, hMub⟩]
  have hMle : ∀ t ∈ Set.Icc a b, |p.eval t| ≤ M := fun t ht => hMub ⟨t, ht, rfl⟩
  have hMnonneg : 0 ≤ M := by
    obtain ⟨t, _, ht⟩ := hMmem
    rw [← ht]
    positivity
  have hM0 : 0 < M := by
    rcases hMnonneg.lt_or_eq with h | h
    · exact h
    exfalso
    have hsub : Set.Icc a b ⊆ {x | p.IsRoot x} := by
      intro t ht
      have hle := hMle t ht
      rw [← h] at hle
      exact abs_nonpos_iff.mp hle
    have : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
      (Set.Infinite.mono hsub (Set.Icc_infinite hab))
    rw [this] at hpγ
    simp at hpγ
  set u : ℝ := (b + a - 2 * γ) / (b - a) with hu
  have hu1 : 1 < |u| := one_lt_abs_shift hab hγ
  have hTpos : (0 : ℝ) < |(T ℝ (m : ℤ)).eval u| :=
    lt_of_lt_of_le zero_lt_one (one_le_abs_eval_T_real _ hu1.le)
  set φ : ℝ[X] := Polynomial.C ((b + a) / 2) + Polynomial.C ((b - a) / 2) * X with hφ
  have hφeval : ∀ y : ℝ, φ.eval y = (b + a) / 2 + (b - a) / 2 * y := by
    intro y; rw [hφ]; simp
  have hφmem : ∀ y ∈ Set.Icc (-1 : ℝ) 1, φ.eval y ∈ Set.Icc a b := by
    intro y hy
    rw [hφeval]
    constructor <;> nlinarith [hy.1, hy.2]
  set P : ℝ[X] := Polynomial.C M⁻¹ * p.comp φ with hP
  have hPdeg : P.degree ≤ (m : ℕ) := by
    refine Polynomial.degree_le_of_natDegree_le ?_
    rw [hP]
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_C, zero_add]
    refine Polynomial.natDegree_comp_le.trans ?_
    have hφd : φ.natDegree ≤ 1 := by rw [hφ]; compute_degree
    simpa using Nat.mul_le_mul (Polynomial.natDegree_le_of_degree_le hp) hφd
  have hPbnd : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |P.eval y| ≤ 1 := by
    intro y hy
    have hval : |P.eval y| = M⁻¹ * |p.eval (φ.eval y)| := by
      rw [hP]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, abs_mul]
      rw [abs_of_nonneg (inv_nonneg.mpr hMnonneg)]
    rw [hval]
    calc M⁻¹ * |p.eval (φ.eval y)| ≤ M⁻¹ * M := by
          gcongr
          exact hMle _ (hφmem y hy)
      _ = 1 := inv_mul_cancel₀ hM0.ne'
  have hφu : φ.eval (-u) = γ := by
    rw [hφeval, hu]
    field_simp
    ring
  have hPu : P.eval (-u) = M⁻¹ := by
    rw [hP]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, hφu, hpγ, mul_one]
  have hkey : M⁻¹ ≤ |(T ℝ (m : ℤ)).eval u| := by
    rw [← hPu, ← abs_eval_T_neg m u]
    exact eval_le_abs_eval_T hPdeg hPbnd (by rw [abs_neg]; exact hu1.le)
  rw [div_le_iff₀ hTpos]
  calc (1 : ℝ) = M * M⁻¹ := by field_simp
    _ ≤ M * |(T ℝ (m : ℤ)).eval u| := by gcongr

/-- The bound is attained by `shifted m a b γ`. -/
theorem sSup_abs_eval_shifted (m : ℕ) {a b γ : ℝ} (hab : a < b) (hγ : γ ∉ Set.Icc a b) :
    sSup ((fun t => |(shifted m a b γ).eval t|) '' Set.Icc a b) =
      1 / |(T ℝ m).eval ((b + a - 2 * γ) / (b - a))| := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hTpos : (0 : ℝ) < |(T ℝ (m : ℤ)).eval ((b + a - 2 * γ) / (b - a))| :=
    lt_of_lt_of_le zero_lt_one (one_le_abs_eval_T_real _ (one_lt_abs_shift hab hγ).le)
  refine IsGreatest.csSup_eq ⟨⟨a, Set.left_mem_Icc.mpr hab.le, ?_⟩, ?_⟩
  · dsimp only
    rw [eval_shifted m hab, show (b + a - 2 * a) / (b - a) = 1 by field_simp; ring, T_eval_one,
      abs_div, abs_one]
  · rintro _ ⟨t, ht, rfl⟩
    dsimp only
    rw [eval_shifted m hab, abs_div]
    calc |(T ℝ (m : ℤ)).eval ((b + a - 2 * t) / (b - a))| /
          |(T ℝ (m : ℤ)).eval ((b + a - 2 * γ) / (b - a))|
        = |(T ℝ (m : ℤ)).eval ((b + a - 2 * t) / (b - a))| *
            (1 / |(T ℝ (m : ℤ)).eval ((b + a - 2 * γ) / (b - a))|) := by ring
      _ ≤ 1 * (1 / |(T ℝ (m : ℤ)).eval ((b + a - 2 * γ) / (b - a))|) :=
          mul_le_mul_of_nonneg_right
            (abs_eval_T_real_le_one _ (abs_shift_le_one hab ht))
            (div_nonneg zero_le_one (abs_nonneg _))
      _ = 1 / |(T ℝ (m : ℤ)).eval ((b + a - 2 * γ) / (b - a))| := one_mul _

/-- Special case `γ = 0`, `0 < a < b`, the form used for the error bound of a Krylov method on a
positive definite operator with spectrum in `[a, b]`:
`min_{deg p ≤ m, p 0 = 1} max_{[a,b]} |p| = 1 / T_m((b + a)/(b - a))`. -/
theorem one_div_eval_T_le_sSup_abs_eval_of_eval_zero (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (p : ℝ[X]) (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    1 / (T ℝ m).eval ((b + a) / (b - a)) ≤ sSup ((fun t => |p.eval t|) '' Set.Icc a b) := by
  have hγ : (0 : ℝ) ∉ Set.Icc a b := fun h => absurd (Set.mem_Icc.mp h).1 (by linarith)
  have h := one_div_eval_T_le_sSup_abs_eval m hab hγ p hp hp0
  rw [show (b + a - 2 * (0 : ℝ)) / (b - a) = (b + a) / (b - a) by ring_nf] at h
  have hu : 1 ≤ (b + a) / (b - a) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < b - a)]
    linarith
  rwa [abs_of_nonneg (le_trans zero_le_one (one_le_eval_T hu m))] at h

/-- `1 / T_m((κ + 1)/(κ - 1)) ≤ 2 ((√κ - 1)/(√κ + 1))^m` for `κ > 1`: the growth estimate that
turns the min–max value into the classical `√κ` convergence rate for a system of condition
number `κ`. -/
theorem one_div_eval_T_le_two_mul_pow {κ : ℝ} (hκ : 1 < κ) (m : ℕ) :
    1 / (T ℝ m).eval ((κ + 1) / (κ - 1)) ≤
      2 * ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ m := by
  have hk1 : (0 : ℝ) < κ - 1 := by linarith
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt (by linarith)
  have hs1 : 1 < Real.sqrt κ := by nlinarith [Real.sqrt_nonneg κ]
  have hsm1 : Real.sqrt κ - 1 ≠ 0 := by linarith
  have hsp1 : Real.sqrt κ + 1 ≠ 0 := by linarith
  have hx1 : (1 : ℝ) ≤ (κ + 1) / (κ - 1) := by
    rw [le_div_iff₀ hk1]; linarith
  have hsq : Real.sqrt (((κ + 1) / (κ - 1)) ^ 2 - 1) = 2 * Real.sqrt κ / (κ - 1) := by
    rw [show ((κ + 1) / (κ - 1)) ^ 2 - 1 = (2 * Real.sqrt κ / (κ - 1)) ^ 2 by
      rw [div_pow, div_pow, mul_pow, hs]
      field_simp
      ring]
    exact Real.sqrt_sq (by positivity)
  have hw : (κ + 1) / (κ - 1) + Real.sqrt (((κ + 1) / (κ - 1)) ^ 2 - 1)
      = (Real.sqrt κ + 1) / (Real.sqrt κ - 1) := by
    rw [hsq, ← add_div, div_eq_div_iff hk1.ne' hsm1]
    linear_combination 2 * hs
  have hwpos : (0 : ℝ) < ((Real.sqrt κ + 1) / (Real.sqrt κ - 1)) ^ m := by
    have : (0 : ℝ) < (Real.sqrt κ + 1) / (Real.sqrt κ - 1) := by
      apply div_pos <;> linarith
    positivity
  have hT : ((Real.sqrt κ + 1) / (Real.sqrt κ - 1)) ^ m / 2 ≤ (T ℝ (m : ℤ)).eval
      ((κ + 1) / (κ - 1)) := by
    have h := half_pow_le_eval_T hx1 m
    rwa [hw] at h
  calc 1 / (T ℝ (m : ℤ)).eval ((κ + 1) / (κ - 1))
      ≤ 1 / (((Real.sqrt κ + 1) / (Real.sqrt κ - 1)) ^ m / 2) :=
        one_div_le_one_div_of_le (by positivity) hT
    _ = 2 * ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ m := by
        rw [one_div_div, div_pow, div_pow]
        field_simp

/-- The closed form of the Chebyshev min–max value on `[λmin, λmax]` with `κ = λmax / λmin > 1`
([quarteroni2000numerical] (4.47) and the display closing the proof of Theorem 4.12): with
`c = (√κ - 1)/(√κ + 1)`, `1 / T_m((κ + 1)/(κ - 1)) = 2 c^m / (1 + c^{2m})`. At
`x = (κ + 1)/(κ - 1)` one has `x + √(x² - 1) = 1/c` and `x - √(x² - 1) = c`, so
`T_m x = ½ (c^{-m} + c^m)` by `eval_T_eq_half_add_pow`. This sharpens
`one_div_eval_T_le_two_mul_pow` to an equality. -/
theorem one_div_eval_T_eq_two_mul_pow_div {κ : ℝ} (hκ : 1 < κ) (m : ℕ) :
    1 / (T ℝ m).eval ((κ + 1) / (κ - 1)) =
      2 * ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ m /
        (1 + ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ (2 * m)) := by
  have hk1 : (0 : ℝ) < κ - 1 := by linarith
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt (by linarith)
  have hs1 : 1 < Real.sqrt κ := by nlinarith [Real.sqrt_nonneg κ]
  have hsm1 : Real.sqrt κ - 1 ≠ 0 := by linarith
  have hsp1 : Real.sqrt κ + 1 ≠ 0 := by linarith
  have hx1 : (1 : ℝ) ≤ (κ + 1) / (κ - 1) := by
    rw [le_div_iff₀ hk1]; linarith
  have hsq : Real.sqrt (((κ + 1) / (κ - 1)) ^ 2 - 1) = 2 * Real.sqrt κ / (κ - 1) := by
    rw [show ((κ + 1) / (κ - 1)) ^ 2 - 1 = (2 * Real.sqrt κ / (κ - 1)) ^ 2 by
      rw [div_pow, div_pow, mul_pow, hs]
      field_simp
      ring]
    exact Real.sqrt_sq (by positivity)
  set c : ℝ := (Real.sqrt κ - 1) / (Real.sqrt κ + 1) with hc
  have hcpos : 0 < c := div_pos (by linarith) (by linarith)
  have hw : (κ + 1) / (κ - 1) + Real.sqrt (((κ + 1) / (κ - 1)) ^ 2 - 1) = c⁻¹ := by
    rw [hsq, ← add_div, hc, inv_div, div_eq_div_iff hk1.ne' hsm1]
    linear_combination 2 * hs
  have hw' : (κ + 1) / (κ - 1) - Real.sqrt (((κ + 1) / (κ - 1)) ^ 2 - 1) = c := by
    rw [hsq, ← sub_div, hc, div_eq_div_iff hk1.ne' hsp1]
    linear_combination (-2) * hs
  rw [eval_T_eq_half_add_pow hx1, hw, hw', inv_pow, pow_mul, ← pow_mul, mul_comm 2 m, pow_mul]
  have hcm : 0 < c ^ m := pow_pos hcpos m
  field_simp

/-! ### Uniqueness of the constrained Chebyshev minimizer -/

section Uniqueness

variable {m : ℕ} {a b : ℝ}

/-- The Chebyshev extremal nodes of `[a, b]`: the images `t_k = (b + a)/2 - cos(kπ/m) (b - a)/2`,
`k = 0, …, m`, of the extrema `cos(kπ/m)` of `T_m` under the affine map of `[-1, 1]` onto
`[a, b]`; `t_0 = a` and `t_m = b`. -/
noncomputable def extremalNode (m : ℕ) (a b : ℝ) (k : Fin (m + 1)) : ℝ :=
  (b + a) / 2 - Real.cos ((k : ℝ) * Real.pi / m) * ((b - a) / 2)

/-- The affine change of variable sends the `k`-th extremal node back to `cos(kπ/m)`. -/
theorem shift_extremalNode (hab : a < b) (k : Fin (m + 1)) :
    (b + a - 2 * extremalNode m a b k) / (b - a) = Real.cos ((k : ℝ) * Real.pi / m) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  rw [extremalNode]
  field_simp
  ring

/-- The extremal nodes lie in `[a, b]`. -/
theorem extremalNode_mem_Icc (hab : a < b) (k : Fin (m + 1)) :
    extremalNode m a b k ∈ Set.Icc a b := by
  have hc := Real.abs_cos_le_one ((k : ℝ) * Real.pi / m)
  rw [abs_le] at hc
  constructor <;> (simp only [extremalNode]; nlinarith [hc.1, hc.2])

/-- The angle `kπ/m` of the `k`-th node lies in `[0, π]`. -/
private theorem angle_mem_Icc (hm : 1 ≤ m) (k : Fin (m + 1)) :
    (k : ℝ) * Real.pi / m ∈ Set.Icc 0 Real.pi := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hk : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 k.2
  constructor
  · positivity
  · rw [div_le_iff₀ hmpos]
    nlinarith [Real.pi_pos]

/-- The extremal nodes are strictly increasing in `k`. -/
theorem extremalNode_strictMono (hm : 1 ≤ m) (hab : a < b) :
    StrictMono (extremalNode m a b) := by
  intro j k hjk
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hjk' : (j : ℝ) * Real.pi / m < (k : ℝ) * Real.pi / m := by
    have : (j : ℝ) < k := by exact_mod_cast hjk
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right this Real.pi_pos) hmpos
  have hcos := Real.strictAntiOn_cos (angle_mem_Icc hm j) (angle_mem_Icc hm k) hjk'
  simp only [extremalNode]
  nlinarith

/-- The extremal nodes are distinct. -/
theorem extremalNode_injective (hm : 1 ≤ m) (hab : a < b) :
    Function.Injective (extremalNode m a b) :=
  (extremalNode_strictMono hm hab).injective

/-- At the `k`-th extremal node the normalized Chebyshev polynomial takes the value
`(-1)^k / T_m((b + a)/(b - a))`, the alternating extremal values. -/
theorem eval_shifted_extremalNode (hm : 1 ≤ m) (hab : a < b) (k : Fin (m + 1)) :
    (shifted m a b 0).eval (extremalNode m a b k)
      = (-1) ^ (k : ℕ) / (T ℝ m).eval ((b + a) / (b - a)) := by
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hm)
  rw [eval_shifted m hab, shift_extremalNode hab, T_real_cos,
    show ((m : ℤ) : ℝ) * ((k : ℝ) * Real.pi / m) = (k : ℕ) * Real.pi by
      push_cast; field_simp,
    Real.cos_nat_mul_pi, mul_zero, sub_zero]

/-- The weights `ℓ_k(0)` of Lagrange interpolation at the extremal nodes, evaluated at `0`, have
the sign `(-1)^k`: `0 < (-1)^k ℓ_k(0)`. Each factor `(0 - t_j)/(t_k - t_j)` of `ℓ_k(0)` is
negative exactly for the `k` indices `j < k`. -/
theorem pos_neg_one_pow_mul_eval_zero_basis_extremalNode (hm : 1 ≤ m) (ha : 0 < a) (hab : a < b)
    (k : Fin (m + 1)) :
    0 < (-1) ^ (k : ℕ) * (Lagrange.basis Finset.univ (extremalNode m a b) k).eval 0 := by
  have hpos : ∀ j, 0 < extremalNode m a b j := fun j =>
    lt_of_lt_of_le ha (extremalNode_mem_Icc hab j).1
  have hmono := extremalNode_strictMono hm hab
  have hcard : (-1 : ℝ) ^ (k : ℕ) = ∏ j ∈ Finset.univ.erase k, if j < k then (-1 : ℝ) else 1 := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp), Finset.filter_gt_eq_Iio,
      Fin.card_Iio]
  rw [hcard, Lagrange.basis, Polynomial.eval_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_pos fun j hj => ?_
  have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
  rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  rcases lt_or_gt_of_ne hjk with h | h
  · simp only [h, ↓reduceIte]
    have h1 : 0 < extremalNode m a b k - extremalNode m a b j := sub_pos.2 (hmono h)
    have := hpos j
    have : 0 < (extremalNode m a b k - extremalNode m a b j)⁻¹ := inv_pos.2 h1
    nlinarith
  · simp only [not_lt.2 h.le, ↓reduceIte]
    have h1 : extremalNode m a b k - extremalNode m a b j < 0 := sub_neg.2 (hmono h)
    have := hpos j
    have : (extremalNode m a b k - extremalNode m a b j)⁻¹ < 0 := inv_lt_zero.2 h1
    nlinarith

/-- Lagrange interpolation at the extremal nodes, evaluated at `0`: for `deg r ≤ m`,
`r(0) = ∑_k r(t_k) ℓ_k(0)`. -/
theorem eval_zero_eq_sum_extremalNode (hm : 1 ≤ m) (hab : a < b) {r : ℝ[X]}
    (hr : r.natDegree ≤ m) :
    r.eval 0 = ∑ k : Fin (m + 1), r.eval (extremalNode m a b k) *
      (Lagrange.basis Finset.univ (extremalNode m a b) k).eval 0 := by
  have hinj : Set.InjOn (extremalNode m a b) (Finset.univ : Finset (Fin (m + 1))) :=
    (extremalNode_injective hm hab).injOn
  have hdeg : r.degree < (Finset.univ : Finset (Fin (m + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hr)
      (by exact_mod_cast m.lt_succ_self)
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- Uniqueness in the Chebyshev min–max problem (the "admits a unique solution" of
[quarteroni2000numerical] Property 4.6, which the book states without proof): for `0 < a < b` and
`m ≥ 1`, a polynomial `p` of degree at most `m` with `p(0) = 1` whose maximum modulus on `[a, b]`
is the minimal value `1 / T_m((b + a)/(b - a))` (`one_div_eval_T_le_sSup_abs_eval_of_eval_zero`)
is the normalized Chebyshev polynomial `shifted m a b 0`. Instead of counting zeros with
multiplicity, the proof interpolates at the `m + 1` extremal nodes `t_k`: the weights
`λ_k = ℓ_k(0)` have the signs `(-1)^k` of the extremal values of `q = shifted m a b 0`, so
`1 = p(0) = ∑ λ_k p(t_k) ≤ ∑ |λ_k| M = ∑ λ_k q(t_k) = q(0) = 1` forces `p(t_k) = q(t_k)` at every
node, and two polynomials of degree at most `m` agreeing at `m + 1` points are equal. -/
theorem eq_shifted_of_sSup_abs_eval_eq (hm : 1 ≤ m) (ha : 0 < a) (hab : a < b) {p : ℝ[X]}
    (hp : p.natDegree ≤ m) (hp0 : p.eval 0 = 1)
    (hsup : sSup ((fun t => |p.eval t|) '' Set.Icc a b) = 1 / (T ℝ m).eval ((b + a) / (b - a))) :
    p = shifted m a b 0 := by
  set M : ℝ := 1 / (T ℝ m).eval ((b + a) / (b - a)) with hM
  have hx1 : (1 : ℝ) ≤ (b + a) / (b - a) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hT1 : 1 ≤ (T ℝ m).eval ((b + a) / (b - a)) := one_le_eval_T hx1 m
  have hMpos : 0 < M := by rw [hM]; positivity
  have hγ : (0 : ℝ) ∉ Set.Icc a b := fun h => absurd h.1 (not_le.2 ha)
  set q : ℝ[X] := shifted m a b 0 with hq
  have hq0 : q.eval 0 = 1 := shifted_eval_self m hab hγ
  have hqdeg : q.natDegree ≤ m :=
    Polynomial.natDegree_le_iff_degree_le.2 (shifted_degree_le m a b 0)
  -- `|p| ≤ M` on `[a, b]`
  have hbdd : BddAbove ((fun t => |p.eval t|) '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn
      (p.continuous.abs.continuousOn)).bddAbove
  have hpM : ∀ t ∈ Set.Icc a b, |p.eval t| ≤ M := fun t ht =>
    hsup ▸ le_csSup hbdd ⟨t, ht, rfl⟩
  -- the interpolation weights and their signs
  set lam : Fin (m + 1) → ℝ := fun k => (Lagrange.basis Finset.univ (extremalNode m a b) k).eval 0
    with hlam
  have hsign : ∀ k : Fin (m + 1), 0 < (-1) ^ (k : ℕ) * lam k := fun k =>
    pos_neg_one_pow_mul_eval_zero_basis_extremalNode hm ha hab k
  have habs : ∀ k, |lam k| = (-1) ^ (k : ℕ) * lam k := fun k => by
    have hk := hsign k
    rcases neg_one_pow_eq_or ℝ (k : ℕ) with h | h
    · rw [h, one_mul] at hk ⊢; exact abs_of_pos hk
    · rw [h, neg_one_mul] at hk ⊢; exact abs_of_neg (by linarith)
  have hqk : ∀ k, q.eval (extremalNode m a b k) = (-1) ^ (k : ℕ) * M := fun k => by
    rw [hq, eval_shifted_extremalNode hm hab k, hM, div_eq_mul_one_div]
  have hp_sum := eval_zero_eq_sum_extremalNode hm hab hp
  have hq_sum := eval_zero_eq_sum_extremalNode hm hab hqdeg
  rw [hp0] at hp_sum
  rw [hq0] at hq_sum
  -- termwise `λ_k p(t_k) ≤ |λ_k| M = λ_k q(t_k)`, with equality of the sums
  have hterm : ∀ k,
      p.eval (extremalNode m a b k) * lam k ≤ q.eval (extremalNode m a b k) * lam k := by
    intro k
    have h1 : p.eval (extremalNode m a b k) * lam k ≤ |lam k| * M := by
      calc p.eval (extremalNode m a b k) * lam k ≤ |p.eval (extremalNode m a b k) * lam k| :=
            le_abs_self _
        _ = |p.eval (extremalNode m a b k)| * |lam k| := abs_mul _ _
        _ ≤ M * |lam k| :=
            mul_le_mul_of_nonneg_right (hpM _ (extremalNode_mem_Icc hab k)) (abs_nonneg _)
        _ = |lam k| * M := mul_comm _ _
    rw [habs k] at h1
    rw [hqk k]
    linarith
  have hsum_eq : ∑ k, p.eval (extremalNode m a b k) * lam k
      = ∑ k, q.eval (extremalNode m a b k) * lam k := by
    rw [← hp_sum, ← hq_sum]
  have heq : ∀ k, p.eval (extremalNode m a b k) * lam k = q.eval (extremalNode m a b k) * lam k :=
    fun k => (Finset.sum_eq_sum_iff_of_le fun k _ => hterm k).1 hsum_eq k (Finset.mem_univ k)
  have hval : ∀ k, p.eval (extremalNode m a b k) = q.eval (extremalNode m a b k) := by
    intro k
    have hne : lam k ≠ 0 := by
      intro h0
      have := hsign k
      rw [h0, mul_zero] at this
      exact lt_irrefl 0 this
    exact mul_right_cancel₀ hne (heq k)
  -- two polynomials of degree `≤ m` agreeing at `m + 1` points
  have hinj : Set.InjOn (extremalNode m a b) (Finset.univ : Finset (Fin (m + 1))) :=
    (extremalNode_injective hm hab).injOn
  have hcard : ((Finset.univ : Finset (Fin (m + 1))).card : WithBot ℕ) = (m + 1 : ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hinj ?_ ?_ fun k _ => hval k
  · rw [hcard]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp)
      (by exact_mod_cast m.lt_succ_self)
  · rw [hcard]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hqdeg)
      (by exact_mod_cast m.lt_succ_self)

end Uniqueness

/-- The pointwise form of the min–max bound: on `[a, b]` the normalized Chebyshev polynomial
`shifted m a b γ` is bounded by `1 / |T_m((b + a - 2γ)/(b - a))|`. -/
theorem abs_eval_shifted_le (m : ℕ) {a b γ t : ℝ} (hab : a < b) (ht : t ∈ Set.Icc a b) :
    |(shifted m a b γ).eval t| ≤ 1 / |(T ℝ m).eval ((b + a - 2 * γ) / (b - a))| := by
  rw [eval_shifted m hab, abs_div, div_eq_mul_inv, one_div]
  exact mul_le_of_le_one_left (inv_nonneg.mpr (abs_nonneg _))
    (abs_eval_T_real_le_one _ (abs_shift_le_one hab ht))

/-- The two-interval Chebyshev polynomial. For `a < b < 0 < c < d` with equal interval lengths
`b - a = d - c` there is, for every `k`, a real polynomial of degree at most `2k` taking the
value `1` at the origin whose modulus on `[a, b] ∪ [c, d]` is at most
`2 ((√|ad| - √|bc|)/(√|ad| + √|bc|))^k`.

It is `shifted k |b c| |a d| 0` composed with the quadratic `t ↦ t² - (a + d) t`, which fixes the
origin and maps each of the two intervals onto `[|b c|, |a d|]`: the equal lengths make
`a + d = b + c`, so the quadratic is `t² - (b + c) t` as well and the two images coincide.
This is the polynomial behind the convergence bound of a minimal-residual Krylov method for a
symmetric operator whose spectrum is split into two intervals on either side of the origin. -/
theorem exists_eval_zero_eq_one_abs_le_of_union_Icc {a b c d : ℝ} (hab : a < b) (hb : b < 0)
    (hc : 0 < c) (hcd : c < d) (hlen : b - a = d - c) (k : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ (2 * k : ℕ) ∧ p.eval 0 = 1 ∧
      ∀ t ∈ Set.Icc a b ∪ Set.Icc c d,
        |p.eval t| ≤ 2 * ((Real.sqrt |a * d| - Real.sqrt |b * c|) /
          (Real.sqrt |a * d| + Real.sqrt |b * c|)) ^ k := by
  have ha : a < 0 := hab.trans hb
  have hd : 0 < d := hc.trans hcd
  have hbc : b * c < 0 := mul_neg_of_neg_of_pos hb hc
  have had : a * d < 0 := mul_neg_of_neg_of_pos ha hd
  have hαv : |b * c| = -(b * c) := abs_of_neg hbc
  have hβv : |a * d| = -(a * d) := abs_of_neg had
  have hα0 : 0 < |b * c| := by rw [hαv]; linarith
  have hβ0 : 0 < |a * d| := by rw [hβv]; linarith
  have hαβ : |b * c| < |a * d| := by
    rw [hαv, hβv]
    nlinarith
  have hsum : a + d = b + c := by linarith
  have h0 : (0 : ℝ) ∉ Set.Icc |b * c| |a * d| := fun h => absurd h.1 (not_le.mpr hα0)
  refine ⟨(shifted k |b * c| |a * d| 0).comp (X ^ 2 - Polynomial.C (a + d) * X), ?_, ?_, ?_⟩
  · refine Polynomial.degree_le_of_natDegree_le (Polynomial.natDegree_comp_le.trans ?_)
    have h1 : (shifted k |b * c| |a * d| 0).natDegree ≤ k :=
      Polynomial.natDegree_le_of_degree_le (shifted_degree_le k _ _ _)
    have h2 : ((X : ℝ[X]) ^ 2 - Polynomial.C (a + d) * X).natDegree ≤ 2 := by compute_degree
    calc (shifted k |b * c| |a * d| 0).natDegree *
          ((X : ℝ[X]) ^ 2 - Polynomial.C (a + d) * X).natDegree ≤ k * 2 := Nat.mul_le_mul h1 h2
      _ = 2 * k := by ring
  · rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C]
    rw [show (0 : ℝ) ^ 2 - (a + d) * 0 = 0 by ring]
    exact shifted_eval_self k hαβ h0
  · intro t ht
    have hq : ∀ s : ℝ,
        ((X : ℝ[X]) ^ 2 - Polynomial.C (a + d) * X).eval s = s ^ 2 - (a + d) * s := by
      intro s
      simp
    have hmem : (((X : ℝ[X]) ^ 2 - Polynomial.C (a + d) * X).eval t) ∈
        Set.Icc |b * c| |a * d| := by
      rw [hq]
      have hfac1 : t ^ 2 - (a + d) * t = |b * c| + (t - b) * (t - c) := by
        rw [hαv]; linear_combination (-t) * hsum
      have hfac2 : t ^ 2 - (a + d) * t = |a * d| + (t - a) * (t - d) := by
        rw [hβv]; ring
      constructor
      · rw [hfac1]
        rcases ht with ht | ht
        · nlinarith [ht.1, ht.2]
        · nlinarith [ht.1, ht.2]
      · rw [hfac2]
        rcases ht with ht | ht
        · nlinarith [ht.1, ht.2]
        · nlinarith [ht.1, ht.2]
    set κ : ℝ := |a * d| / |b * c| with hκ
    have hκ1 : 1 < κ := (one_lt_div hα0).mpr hαβ
    have harg : (|a * d| + |b * c| - 2 * 0) / (|a * d| - |b * c|) = (κ + 1) / (κ - 1) := by
      have hden : |a * d| - |b * c| ≠ 0 := sub_ne_zero.mpr hαβ.ne'
      have hκ' : κ - 1 ≠ 0 := sub_ne_zero.mpr hκ1.ne'
      rw [mul_zero, sub_zero, div_eq_div_iff hden hκ', hκ]
      field_simp
    have hTge : 1 ≤ (T ℝ k).eval ((κ + 1) / (κ - 1)) := by
      refine one_le_eval_T ?_ k
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < κ - 1)]
      linarith
    have hsqrtα : 0 < Real.sqrt |b * c| := Real.sqrt_pos.mpr hα0
    have hsqrtκ : Real.sqrt κ = Real.sqrt |a * d| / Real.sqrt |b * c| := by
      rw [hκ, Real.sqrt_div hβ0.le]
    have hratio : (Real.sqrt κ - 1) / (Real.sqrt κ + 1)
        = (Real.sqrt |a * d| - Real.sqrt |b * c|) /
          (Real.sqrt |a * d| + Real.sqrt |b * c|) := by
      have h1 : Real.sqrt κ + 1 ≠ 0 := by positivity
      have h2 : Real.sqrt |a * d| + Real.sqrt |b * c| ≠ 0 := by positivity
      rw [div_eq_div_iff h1 h2, hsqrtκ]
      field_simp
    rw [Polynomial.eval_comp]
    calc |(shifted k |b * c| |a * d| 0).eval
            (((X : ℝ[X]) ^ 2 - Polynomial.C (a + d) * X).eval t)|
        ≤ 1 / |(T ℝ k).eval ((|a * d| + |b * c| - 2 * 0) / (|a * d| - |b * c|))| :=
          abs_eval_shifted_le k hαβ hmem
      _ = 1 / (T ℝ k).eval ((κ + 1) / (κ - 1)) := by
          rw [harg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (T ℝ k).eval ((κ + 1) / (κ - 1)))]
      _ ≤ 2 * ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ k :=
          one_div_eval_T_le_two_mul_pow hκ1 k
      _ = 2 * ((Real.sqrt |a * d| - Real.sqrt |b * c|) /
            (Real.sqrt |a * d| + Real.sqrt |b * c|)) ^ k := by rw [hratio]

end Polynomial.Chebyshev
