/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A logarithmic bound for Lebesgue-type sums of reciprocal sines

For a positive integer `M`, an offset `δ ∈ [0, 1)` and an integer `k`, put

`SineSum.term M δ k = |sin (π (k + δ))| / (M |sin (π (k + δ) / M)|)`,

with the convention `0/0 = 0` at the finitely many `k` where the denominator vanishes. This file
proves that a sum of `M` consecutive such terms is at most `2 + (2/π) log M` for `M ≥ 3`,
uniformly in `δ` and in where the run of indices starts (`SineSum.sum_term_le`).

## The argument

The numerator is the same for every `k` in the run, and `|sin (M x)| ≤ M |sin x|`
(`SineSum.abs_sin_natCast_mul_le`) bounds every term by `1` (`SineSum.term_le_one`). The two terms
whose index is nearest the evaluation point are taken at that bound; for the rest, `sin` is
bounded below by `x - x³/6` near `0` and by the tangent comparison `x < tan x` further out, which
turns `1 / (M sin (π(k + δ)/M))` into a difference of logarithms that telescopes
(`SineSum.sum_le_of_telescope`).

## Where it is used

It is the one estimate behind every Lebesgue constant of interpolation at equally spaced angles:
`Numlib/Approximation/TrigonometricInterpolation`'s `norm_trigInterpCLM_le` is the odd case
`M = 2 n + 1`, and `Numlib/Approximation/Interpolation`'s
`Lagrange.norm_interpolateCLM_chebyshev_le`, the logarithmic growth of the Lebesgue constant of
the Chebyshev nodes, is the even case `M = 2 n + 2` after the substitution `t = cos θ`.
-/

open Real Set
open scoped Real

namespace SineSum

/-- `|sin (n x)| ≤ n |sin x|` for a natural number `n`. -/
theorem abs_sin_natCast_mul_le (n : ℕ) (x : ℝ) : |Real.sin ((n : ℝ) * x)| ≤ n * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h : ((k : ℕ) + 1 : ℝ) * x = (k : ℝ) * x + x := by ring
    push_cast
    rw [h, Real.sin_add]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |Real.sin ((k : ℝ) * x)| * |Real.cos x| ≤ (k : ℝ) * |Real.sin x| :=
      le_trans (by nlinarith [abs_nonneg (Real.sin ((k : ℝ) * x)), Real.abs_cos_le_one x]) ih
    have h2 : |Real.cos ((k : ℝ) * x)| * |Real.sin x| ≤ 1 * |Real.sin x| := by
      gcongr
      exact Real.abs_cos_le_one _
    linarith

/-- `|sin (y + n π)| = |sin y|`. -/
theorem abs_sin_add_natCast_mul_pi (n : ℕ) (y : ℝ) :
    |Real.sin (y + (n : ℝ) * π)| = |Real.sin y| := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [show y + ((k : ℝ) + 1) * π = (y + (k : ℝ) * π) + π by ring, Real.sin_add_pi, abs_neg, ih]

/-- `|sin (y + m π)| = |sin y|` for an integer `m`. -/
theorem abs_sin_add_intCast_mul_pi (m : ℤ) (y : ℝ) :
    |Real.sin (y + (m : ℝ) * π)| = |Real.sin y| := by
  rw [Real.sin_add, Real.sin_int_mul_pi, Real.cos_int_mul_pi, mul_zero, add_zero, abs_mul,
    abs_zpow, abs_neg, abs_one, one_zpow, mul_one]

/-- One term of the Lebesgue-type sum: `|sin (π (k + δ))| / (M |sin (π (k + δ) / M)|)`. -/
noncomputable def term (M : ℕ) (δ : ℝ) (k : ℤ) : ℝ :=
  |Real.sin (π * ((k : ℝ) + δ))| / ((M : ℝ) * |Real.sin (π * ((k : ℝ) + δ) / M)|)

/-- The terms are periodic in the index with period `M`. -/
theorem term_periodic (M : ℕ) (δ : ℝ) (k : ℤ) : term M δ (k + M) = term M δ k := by
  have hnum : Real.sin (π * (((k + (M : ℤ) : ℤ) : ℝ) + δ))
      = Real.sin (π * ((k : ℝ) + δ) + (M : ℝ) * π) := by
    congr 1
    push_cast
    ring
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [term]
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hden : π * (((k + (M : ℤ) : ℤ) : ℝ) + δ) / M = π * ((k : ℝ) + δ) / M + π := by
    field_simp
    push_cast
    ring
  rw [term, term, hnum, hden, abs_sin_add_natCast_mul_pi, Real.sin_add_pi, abs_neg]

/-- Every term is nonnegative. -/
theorem term_nonneg (M : ℕ) (δ : ℝ) (k : ℤ) : 0 ≤ term M δ k :=
  div_nonneg (abs_nonneg _) (by positivity)

/-- Every term is at most `1`, because `|sin (M u)| ≤ M |sin u|`. -/
theorem term_le_one {M : ℕ} (hM : 0 < M) (δ : ℝ) (k : ℤ) : term M δ k ≤ 1 := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  rcases eq_or_lt_of_le (abs_nonneg (Real.sin (π * ((k : ℝ) + δ) / M))) with h | h
  · rw [term, ← h, mul_zero, div_zero]; norm_num
  · rw [term, div_le_one (by positivity)]
    have hx : π * ((k : ℝ) + δ) = (M : ℝ) * (π * ((k : ℝ) + δ) / M) := by field_simp
    nth_rewrite 1 [hx]
    exact abs_sin_natCast_mul_le M _

/-- The sum of `M` consecutive terms does not depend on where it starts. -/
theorem sum_range_shift (M : ℕ) (δ : ℝ) (c : ℤ) :
    ∑ i ∈ Finset.range M, term M δ (c + i) = ∑ i ∈ Finset.range M, term M δ i := by
  have key : ∀ d : ℤ, ∑ i ∈ Finset.range M, term M δ (d + 1 + i)
      = ∑ i ∈ Finset.range M, term M δ (d + i) := by
    intro d
    have h1 : ∑ i ∈ Finset.range M, term M δ (d + 1 + i)
        = ∑ i ∈ Finset.range M, (fun j : ℕ => term M δ (d + j)) (i + 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      push_cast
      ring
    have h2 := Finset.sum_range_succ' (fun j : ℕ => term M δ (d + j)) M
    have h3 := Finset.sum_range_succ (fun j : ℕ => term M δ (d + j)) M
    have h4 : term M δ (d + (M : ℕ)) = term M δ (d + (0 : ℕ)) := by
      rw [Nat.cast_zero, add_zero]
      exact term_periodic M δ d
    rw [h1]
    linarith
  induction c using Int.induction_on with
  | zero => simp
  | succ i ih => rw [key (i : ℤ)]; exact ih
  | pred i ih =>
    rw [← key (-(i : ℤ) - 1), show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]
    exact ih

/-- The power series of `log ((1 + w) / (1 - w))` has nonnegative terms for `0 ≤ w < 1`, so it
dominates the sum of its first two: `2 w + (2/3) w³ ≤ log (1 + w) - log (1 - w)`. -/
private theorem add_le_log_sub_log {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    2 * w + 2 / 3 * w ^ 3 ≤ Real.log (1 + w) - Real.log (1 - w) := by
  have habs : |w| < 1 := by rwa [abs_of_nonneg hw0]
  have hsum := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * w ^ (2 * k + 1) := by
    intro k
    have hk : (0 : ℝ) ≤ 1 / (2 * (k : ℝ) + 1) := by positivity
    have : (0 : ℝ) ≤ w ^ (2 * k + 1) := pow_nonneg hw0 _
    positivity
  have h := sum_le_hasSum (Finset.range 2) (fun i _ => hnn i) hsum
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

/-- For `0 < h ≤ π/6`, `h ≤ sin h + (sin h)³ / 3`. -/
private theorem le_sin_add_sin_cube_div {h : ℝ} (hh0 : 0 < h) (hh : h ≤ π / 6) :
    h ≤ Real.sin h + Real.sin h ^ 3 / 3 := by
  have hb : h ≤ 2 / 3 := by
    have := Real.pi_le_four
    linarith
  have hs : h - h ^ 3 / 6 ≤ Real.sin h := Real.sin_ge_sub_cube hh0.le
  have hsq : h ^ 2 ≤ 0.45 := by nlinarith
  have hcube : h ^ 3 ≤ 0.45 * h := by nlinarith
  have h1 : 0.925 * h ≤ Real.sin h := by linarith
  have h2 : (0.925 * h) ^ 3 ≤ Real.sin h ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 : (0.925 * h) ^ 3 = 0.791453125 * h ^ 3 := by ring
  nlinarith [pow_pos hh0 3]

/-- **The midpoint bound for the cosecant.** For `0 < h ≤ π/6` and `h < φ < π - h`,
`2 h / sin φ ≤ log (tan ((φ + h)/2)) - log (tan ((φ - h)/2))`: the comparison
`2h / sin φ ≤ ∫_{φ - h}^{φ + h} dy / sin y` in algebraic form. -/
private theorem two_mul_div_sin_le {h φ : ℝ} (hh0 : 0 < h) (hh : h ≤ π / 6)
    (hφ1 : h < φ) (hφ2 : φ < π - h) :
    2 * h / Real.sin φ
      ≤ Real.log (Real.tan ((φ + h) / 2)) - Real.log (Real.tan ((φ - h) / 2)) := by
  have hpi := Real.pi_pos
  set A := (φ + h) / 2 with hA
  set B := (φ - h) / 2 with hB
  have hB0 : 0 < B := by rw [hB]; linarith
  have hA2 : A < π / 2 := by rw [hA]; linarith
  have hsinA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsinB : 0 < Real.sin B := Real.sin_pos_of_pos_of_lt_pi hB0 (by linarith)
  have hcosA : 0 < Real.cos A := Real.cos_pos_of_mem_Ioo ⟨by linarith, hA2⟩
  have hcosB : 0 < Real.cos B := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : Real.sin φ = Real.sin A * Real.cos B + Real.cos A * Real.sin B := by
    rw [show φ = A + B by rw [hA, hB]; ring, Real.sin_add]
  have he : Real.sin h = Real.sin A * Real.cos B - Real.cos A * Real.sin B := by
    rw [show h = A - B by rw [hA, hB]; ring, Real.sin_sub]
  have hs0 : 0 < Real.sin φ := by rw [hs]; positivity
  have he0 : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi hh0 (by linarith)
  have hes : Real.sin h < Real.sin φ := by
    rw [hs, he]; nlinarith [mul_pos hcosA hsinB]
  set w := Real.sin h / Real.sin φ with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hw1 : w < 1 := by rw [hw, div_lt_one hs0]; exact hes
  have htanA : 0 < Real.tan A := by rw [Real.tan_eq_sin_div_cos]; positivity
  have htanB : 0 < Real.tan B := by rw [Real.tan_eq_sin_div_cos]; positivity
  have hratio : Real.tan A / Real.tan B = (1 + w) / (1 - w) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, hw, hs, he]
    field_simp
    ring
  have hlog : Real.log (Real.tan A) - Real.log (Real.tan B) = Real.log (1 + w) - Real.log (1 - w) :=
    by rw [← Real.log_div htanA.ne' htanB.ne', hratio,
      Real.log_div (by linarith) (by linarith)]
  rw [hlog]
  refine le_trans ?_ (add_le_log_sub_log hw0 hw1)
  have hle : h ≤ Real.sin h + Real.sin h ^ 3 / 3 := le_sin_add_sin_cube_div hh0 hh
  have hs2 : Real.sin φ ^ 2 ≤ 1 := by nlinarith [Real.sin_le_one φ, Real.neg_one_le_sin φ]
  have hnum : 0 ≤ 2 * Real.sin h * Real.sin φ ^ 2 + 2 / 3 * Real.sin h ^ 3
      - 2 * h * Real.sin φ ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (Real.sin φ)) (sub_nonneg.2 hle),
      mul_nonneg (sub_nonneg.2 hs2) (pow_pos he0 3).le]
  rw [← sub_nonneg, hw]
  have hid : 2 * (Real.sin h / Real.sin φ) + 2 / 3 * (Real.sin h / Real.sin φ) ^ 3
      - 2 * h / Real.sin φ
      = (2 * Real.sin h * Real.sin φ ^ 2 + 2 / 3 * Real.sin h ^ 3 - 2 * h * Real.sin φ ^ 2)
        / Real.sin φ ^ 3 := by
    field_simp
  rw [hid]
  exact div_nonneg hnum (by positivity)

/-- A sum whose first and last terms are at most `1` and whose interior terms are dominated by a
telescoping difference is at most `2` plus the total difference. -/
private theorem sum_le_of_telescope {M : ℕ} (G Ψ : ℕ → ℝ) (C : ℝ)
    (hend : ∀ c, G c ≤ 1) (hmid : ∀ i, i < M → G (i + 1) ≤ C * (Ψ (i + 1) - Ψ i)) :
    ∑ c ∈ Finset.range (M + 2), G c ≤ 2 + C * (Ψ M - Ψ 0) := by
  have h1 : ∑ c ∈ Finset.range (M + 2), G c
      = (∑ i ∈ Finset.range M, G (i + 1)) + G (M + 1) + G 0 := by
    rw [Finset.sum_range_succ' G (M + 1), Finset.sum_range_succ (fun i => G (i + 1)) M]
  have h2 : ∑ i ∈ Finset.range M, G (i + 1) ≤ ∑ i ∈ Finset.range M, C * (Ψ (i + 1) - Ψ i) :=
    Finset.sum_le_sum fun i hi => hmid i (Finset.mem_range.1 hi)
  have h3 : ∑ i ∈ Finset.range M, C * (Ψ (i + 1) - Ψ i) = C * (Ψ M - Ψ 0) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub Ψ M]
  rw [h1]
  have e1 := hend (M + 1)
  have e2 := hend 0
  linarith [h2.trans_eq h3]

/-- If the `M`-scaled sine is positive, the term is at most `1 / (M sin …)`. -/
private theorem term_le_inv {M : ℕ} {δ : ℝ} (k : ℤ)
    (hpos : 0 < Real.sin (π * ((k : ℝ) + δ) / M)) :
    term M δ k ≤ 1 / ((M : ℝ) * Real.sin (π * ((k : ℝ) + δ) / M)) := by
  rw [term, abs_of_pos hpos]
  gcongr
  · exact Real.abs_sin_le_one _

/-- **A logarithmic bound for a Lebesgue-type sum of reciprocal sines.** For `M ≥ 3`, `δ ∈ [0, 1)`
and any starting index `c`,

`∑_{i < M} |sin (π (c + i + δ))| / (M |sin (π (c + i + δ) / M)|) ≤ 2 + (2/π) log M`.

The two terms nearest the evaluation point are bounded by `1` each (`|sin (M u)| ≤ M |sin u|`) and
the remaining ones by the midpoint comparison `2q / sin φ ≤ ∫_{φ-q}^{φ+q} dy / sin y` with
`q = π / (2 M)` the half-spacing, whose right-hand sides telescope to at most `2 log M`. -/
theorem sum_term_le {M : ℕ} (hM : 3 ≤ M) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (c : ℤ) :
    ∑ i ∈ Finset.range M, term M δ (c + i) ≤ 2 + 2 / π * Real.log M := by
  rw [sum_range_shift]
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < π := by
    have h := Real.sin_lt (show (0 : ℝ) < π / 6 by positivity)
    rw [Real.sin_pi_div_six] at h
    linarith
  have hMr3 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  set q : ℝ := π / (2 * (M : ℝ)) with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hqM : 2 * (M : ℝ) * q = π := by rw [hq]; field_simp
  have hq6 : q ≤ π / 6 := by
    rw [hq, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hphi : ∀ y : ℝ, π * y / (M : ℝ) = 2 * q * y := by
    intro y
    rw [hq]
    field_simp
  have hend : ∀ i : ℕ, term M δ (i : ℤ) ≤ 1 := fun i => term_le_one (by omega) δ _
  have hmid : ∀ i : ℕ, i < M - 2 → term M δ (((i + 1 : ℕ) : ℤ))
      ≤ 1 / π * (Real.log (Real.tan ((2 * q * (((i + 1 : ℕ) : ℝ) + 1 + δ) - q) / 2))
        - Real.log (Real.tan ((2 * q * ((i : ℝ) + 1 + δ) - q) / 2))) := by
    intro i hi
    have hiR : (i : ℝ) + 1 ≤ (M : ℝ) - 2 := by
      have h1 : i + 3 ≤ M := by omega
      have h2 : ((i : ℝ) + 3) ≤ (M : ℝ) := by exact_mod_cast h1
      linarith
    have harg : π * ((((i + 1 : ℕ) : ℤ) : ℝ) + δ) / (M : ℝ) = 2 * q * ((i : ℝ) + 1 + δ) := by
      rw [← hphi]
      congr 2
      push_cast
      ring
    have hφ1 : q < 2 * q * ((i : ℝ) + 1 + δ) := by nlinarith
    have hφ2 : 2 * q * ((i : ℝ) + 1 + δ) < π - q := by rw [← hqM]; nlinarith
    have hsin : 0 < Real.sin (2 * q * ((i : ℝ) + 1 + δ)) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hle := term_le_inv (M := M) (δ := δ) ((i + 1 : ℕ) : ℤ) (by rw [harg]; exact hsin)
    rw [harg] at hle
    refine hle.trans ?_
    have hrw : 1 / ((M : ℝ) * Real.sin (2 * q * ((i : ℝ) + 1 + δ)))
        = 1 / π * (2 * q / Real.sin (2 * q * ((i : ℝ) + 1 + δ))) := by
      rw [← hqM]
      field_simp
    have hΨ1 : 2 * q * (((i + 1 : ℕ) : ℝ) + 1 + δ) - q
        = 2 * q * ((i : ℝ) + 1 + δ) + q := by push_cast; ring
    rw [hrw, hΨ1]
    exact mul_le_mul_of_nonneg_left (two_mul_div_sin_le hq0 hq6 hφ1 hφ2) (by positivity)
  have hsum := sum_le_of_telescope (M := M - 2) (fun i : ℕ => term M δ (i : ℤ))
    (fun i : ℕ => Real.log (Real.tan ((2 * q * ((i : ℝ) + 1 + δ) - q) / 2))) (1 / π) hend hmid
  rw [show M - 2 + 2 = M by omega] at hsum
  refine hsum.trans ?_
  have hb0 : 0 < (3 - 2 * δ) * q / 2 := by nlinarith
  have hbpi : (3 - 2 * δ) * q / 2 < π / 2 := by nlinarith
  have ha0 : 0 < (1 + 2 * δ) * q / 2 := by nlinarith
  have hapi : (1 + 2 * δ) * q / 2 < π / 2 := by nlinarith
  have hMc : (((M - 2 : ℕ) : ℝ)) = (M : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ M)]
    norm_num
  have hΨtop : Real.log (Real.tan ((2 * q * ((((M - 2 : ℕ)) : ℝ) + 1 + δ) - q) / 2))
      = -Real.log (Real.tan ((3 - 2 * δ) * q / 2)) := by
    rw [hMc, show (2 * q * ((M : ℝ) - 2 + 1 + δ) - q) / 2 = π / 2 - (3 - 2 * δ) * q / 2 by
      rw [← hqM]; ring, Real.tan_pi_div_two_sub, Real.log_inv]
  have hΨbot : Real.log (Real.tan ((2 * q * (((0 : ℕ) : ℝ) + 1 + δ) - q) / 2))
      = Real.log (Real.tan ((1 + 2 * δ) * q / 2)) := by
    norm_num
    ring_nf
  have hla : Real.log ((1 + 2 * δ) * q / 2) ≤ Real.log (Real.tan ((1 + 2 * δ) * q / 2)) :=
    Real.log_le_log ha0 (Real.lt_tan ha0 hapi).le
  have hlb : Real.log ((3 - 2 * δ) * q / 2) ≤ Real.log (Real.tan ((3 - 2 * δ) * q / 2)) :=
    Real.log_le_log hb0 (Real.lt_tan hb0 hbpi).le
  have hprod : Real.log ((3 - 2 * δ) * q / 2) + Real.log ((1 + 2 * δ) * q / 2)
      = Real.log (((3 - 2 * δ) * q / 2) * ((1 + 2 * δ) * q / 2)) :=
    (Real.log_mul hb0.ne' ha0.ne').symm
  have hge : 1 / (M : ℝ) ^ 2 ≤ ((3 - 2 * δ) * q / 2) * ((1 + 2 * δ) * q / 2) := by
    have h16 : (16 : ℝ) ≤ 3 * π ^ 2 := by nlinarith
    rw [hq, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg δ, mul_nonneg hδ0 (sub_nonneg.2 hδ1.le)]
  have hlog2 : -(2 * Real.log (M : ℝ))
      ≤ Real.log (((3 - 2 * δ) * q / 2) * ((1 + 2 * δ) * q / 2)) := by
    have h := Real.log_le_log (by positivity) hge
    rw [one_div, Real.log_inv, Real.log_pow] at h
    push_cast at h
    linarith
  rw [hΨtop, hΨbot]
  have hfin : -Real.log (Real.tan ((3 - 2 * δ) * q / 2))
      - Real.log (Real.tan ((1 + 2 * δ) * q / 2)) ≤ 2 * Real.log (M : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hfin (le_of_lt (by positivity : (0 : ℝ) < 1 / π))
  have heq : 1 / π * (2 * Real.log (M : ℝ)) = 2 / π * Real.log (M : ℝ) := by ring
  linarith

end SineSum
