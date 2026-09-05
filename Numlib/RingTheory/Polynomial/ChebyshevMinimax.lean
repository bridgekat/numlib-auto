/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.RingTheory.Polynomial.Chebyshev`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact

/-!
# Chebyshev min–max on an interval

`min {max_{t ∈ [a,b]} |p t| : deg p ≤ m, p γ = 1} = 1 / |T_m(1 + 2(a - γ)/(b - a))|` for
`γ ∉ [a, b]` (Saad Thm 6.25 / Saad-eig Thm 4.8; Rivlin Thm 1.10), its special case `γ = 0`,
and the growth estimates that turn it into geometric rates (Saad (6.128)).
Mathlib supplies `Polynomial.Chebyshev.T` and the extremal inequality
`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`.
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

theorem one_le_eval_T {x : ℝ} (hx : 1 ≤ x) (m : ℕ) : 1 ≤ (T ℝ m).eval x :=
  one_le_eval_T_real _ hx

/-- The shifted Chebyshev polynomial `t ↦ T_m((b + a - 2t)/(b - a)) / T_m((b + a - 2γ)/(b - a))`,
normalized to `1` at `γ`. -/
noncomputable def shifted (m : ℕ) (a b γ : ℝ) : ℝ[X] :=
  Polynomial.C (1 / (T ℝ m).eval ((b + a - 2 * γ) / (b - a))) *
    (T ℝ m).comp (Polynomial.C ((b + a) / (b - a)) - Polynomial.C (2 / (b - a)) * X)

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

private theorem abs_eval_T_neg (m : ℕ) (z : ℝ) :
    |(T ℝ (m : ℤ)).eval (-z)| = |(T ℝ (m : ℤ)).eval z| := by
  simp [T_eval_neg, abs_mul]

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

/-- Special case `γ = 0`, `0 < a < b` (Saad Thm 6.29's ingredient):
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

/-- `1 / T_m((κ + 1)/(κ - 1)) ≤ 2 ((√κ - 1)/(√κ + 1))^m` for `κ > 1` (Saad (6.128)). -/
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

end Polynomial.Chebyshev
