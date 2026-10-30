import Numlib.Optimization.Complexity.SlowExample.ZigZag
import NumlibSurface.CartisGouldToint.Chapter02.Section02

/-!
# Cartis–Gould–Toint, Appendix B: Appendix to Chapter 2

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Appendix B, "Appendix to
Chapter 2": the two-dimensional example on which steepest descent with exact linesearches (SDEX)
needs `ε⁻²` iterations (proof of Theorem 2.2.5, `Chapter02.theorem_2_2_5`), Lemmas B.2.1–B.2.6.

The construction is the backbone `Optimization.zigZagFunction ε k_ε`
(`Numlib.Optimization.Complexity.SlowExample.ZigZag`), `f_SDEX(x, y) = (f₁(x) + f₂(x, y))/√2`,
with iterates `Optimization.zigZagIterate ε k_ε k`; throughout, `ε > 0` and `k_ε ε² = 1`, i.e.
`ε⁻²` is an integer (`Optimization.ZigZag.IsAdmissible`).

## Main results

* `lemma_B_2_1`, `lemma_B_2_1_bound` — Lemma B.2.1: the quintic Hermite interpolant
  `hermiteQuintic` with coefficients (B.2.1)–(B.2.2), and the bound on it and its first two
  derivatives.
* `lemma_B_2_2` — Lemma B.2.2: the gradients at the iterates (B.2.25) and the iteration count of
  steepest descent with the prescribed stepsize `√2`.
* `lemma_B_2_3` — Lemma B.2.3: bounds on the corridor function `f₂` and its derivatives.
* `lemma_B_2_4`, `lemma_B_2_5` — f.Bb and f.gL with constants independent of `ε`.
* `lemma_B_2_6` — the linesearches are exact: each iterate is the first global minimizer along
  the steepest-descent ray from the previous one.

## Differences with the book

* Lemma B.2.1: the bound on `p` and its derivatives also needs `|f₀|, |g₀|, |H₀| ≤ κ_f`
  (implicit in the book's appeal to Theorem A.9.1); the bound `|r_i| ≤ κ_f` alone does not
  control the constant and linear terms.
* The corridor function: the book's `f₂` (B.2.19) equals `(y - y_mid(x))²` in the corridor and is
  continued by Hermite transitions to the constant `8δ(x)²`; the backbone uses
  `f₂(x, y) = ψ(y - y_mid(x))` with a twice continuously differentiable capped square `ψ`, which
  agrees with the book's on the corridor (where all evaluations of the proof take place).
  Accordingly Lemma B.2.3 is stated on the bands `|y - y_mid(x)| ≤ 2`, which contain the book's
  `[y_low(x) - 1, y_low(x)] ∪ [y_up(x), y_up(x) + 1]`; the bounds on the first and second
  derivatives hold on all of `ℝ²`.
* Lemma B.2.6: the book's proof shows only that `(x_{k+1}, y_{k+1})` is the first *local*
  minimizer along the ray (with the book's bounded `f₂`, `f₁` keeps decreasing along the ray after
  the corridor is left). With the capped square the line minimizer is global, so the exact
  linesearch (2.2.26) itself is realized.
* The data (B.2.5)–(B.2.6) are printed for all `k ≥ 0`, but `ε + ω_k` vanishes at `k = 2k_ε`;
  the construction freezes `y_mid` after `x_{k_ε}`.
-/

open Set Finset Optimization
open scoped RealInnerProductSpace

namespace CartisGouldToint.AppendixB

/-! ### Lemma B.2.1 -/

/-- The polynomial `∑_{i=0}^5 c_i t^i` with coefficient vector `c`. -/
def quintic (c : Fin 6 → ℝ) (t : ℝ) : ℝ := ∑ i : Fin 6, c i * t ^ (i : ℕ)

/-- The coefficients of the derivative of `quintic c`: `(c₁, 2c₂, 3c₃, 4c₄, 5c₅, 0)`. -/
def derivCoeff (c : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![c 1, 2 * c 2, 3 * c 3, 4 * c 4, 5 * c 5, 0]

theorem hasDerivAt_quintic (c : Fin 6 → ℝ) (t : ℝ) :
    HasDerivAt (quintic c) (quintic (derivCoeff c) t) t := by
  have h : HasDerivAt (fun t => ∑ i : Fin 6, c i * t ^ (i : ℕ))
      (∑ i : Fin 6, c i * ((i : ℕ) * t ^ ((i : ℕ) - 1))) t :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_pow _ t).const_mul (c i)
  refine h.congr_deriv ?_
  simp only [quintic, derivCoeff, Fin.sum_univ_six]
  simp
  ring

theorem deriv_quintic (c : Fin 6 → ℝ) : deriv (quintic c) = quintic (derivCoeff c) :=
  funext fun t => (hasDerivAt_quintic c t).deriv

theorem iteratedDeriv_two_quintic (c : Fin 6 → ℝ) :
    iteratedDeriv 2 (quintic c) = quintic (derivCoeff (derivCoeff c)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_quintic, deriv_quintic]

/-- On `[0, 1]`, `|∑ c_i t^i| ≤ ∑ |c_i|`. -/
theorem abs_quintic_le (c : Fin 6 → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |quintic c t| ≤ ∑ i : Fin 6, |c i| := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (by rw [abs_pow, abs_of_nonneg ht.1]; exact pow_le_one₀ ht.1 ht.2)

/-- The residuals (B.2.2): `r₀ = f₁ - f₀ - g₀ - H₀/2`, `r₁ = g₁ - g₀ - H₀`, `r₂ = H₁ - H₀`. -/
noncomputable def hermiteResidual (f₀ g₀ H₀ f₁ g₁ H₁ : ℝ) : Fin 3 → ℝ :=
  ![f₁ - f₀ - g₀ - H₀ / 2, g₁ - g₀ - H₀, H₁ - H₀]

/-- The coefficients (B.2.1) of the quintic Hermite interpolant:
`c₀ = f₀`, `c₁ = g₀`, `c₂ = H₀/2`, `c₃ = 10r₀ - 4r₁ + r₂/2`, `c₄ = -15r₀ + 7r₁ - r₂`,
`c₅ = 6r₀ - 3r₁ + r₂/2`. -/
noncomputable def hermiteCoeff (f₀ g₀ H₀ f₁ g₁ H₁ : ℝ) : Fin 6 → ℝ :=
  let r := hermiteResidual f₀ g₀ H₀ f₁ g₁ H₁
  ![f₀, g₀, H₀ / 2, 10 * r 0 - 4 * r 1 + r 2 / 2, -15 * r 0 + 7 * r 1 - r 2,
    6 * r 0 - 3 * r 1 + r 2 / 2]

/-- The quintic Hermite interpolant of Lemma B.2.1. -/
noncomputable def hermiteQuintic (f₀ g₀ H₀ f₁ g₁ H₁ : ℝ) : ℝ → ℝ :=
  quintic (hermiteCoeff f₀ g₀ H₀ f₁ g₁ H₁)

/-- **Lemma B.2.1** of [cartis2022evaluation], interpolation part. The quintic `p` with the
coefficients (B.2.1)–(B.2.2) satisfies `p(0) = f₀`, `p'(0) = g₀`, `p''(0) = H₀`, `p(1) = f₁`,
`p'(1) = g₁`, `p''(1) = H₁`. -/
theorem lemma_B_2_1 (f₀ g₀ H₀ f₁ g₁ H₁ : ℝ) :
    hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁ 0 = f₀ ∧
      deriv (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) 0 = g₀ ∧
      iteratedDeriv 2 (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) 0 = H₀ ∧
      hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁ 1 = f₁ ∧
      deriv (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) 1 = g₁ ∧
      iteratedDeriv 2 (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) 1 = H₁ := by
  simp only [hermiteQuintic, deriv_quintic, iteratedDeriv_two_quintic, quintic,
    Fin.sum_univ_six]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [derivCoeff, hermiteCoeff, hermiteResidual] <;> ring

/-- **Lemma B.2.1** of [cartis2022evaluation], bound part. For every `κ_f ≥ 1` there is
`κ_h > 0` (namely `κ_h = 1000 κ_f`) such that, whenever the residuals (B.2.2) satisfy
`|r_i| ≤ κ_f` (B.2.3) and the data at `0` satisfy `|f₀|, |g₀|, |H₀| ≤ κ_f`, the interpolant and
its first two derivatives are bounded by `κ_h` on `[0, 1]`. (The bounds on the data at `0` are
needed and implicit in the book; they are the analogue of the hypothesis (A.31) of the general
Hermite interpolation bound of Appendix A.) -/
theorem lemma_B_2_1_bound {κf : ℝ} (hκ : 1 ≤ κf) :
    ∃ κh : ℝ, 0 < κh ∧ ∀ f₀ g₀ H₀ f₁ g₁ H₁ : ℝ,
      (∀ i, |hermiteResidual f₀ g₀ H₀ f₁ g₁ H₁ i| ≤ κf) → |f₀| ≤ κf → |g₀| ≤ κf → |H₀| ≤ κf →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ i ≤ 2,
        |iteratedDeriv i (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) t| ≤ κh := by
  refine ⟨1000 * κf, by positivity, fun f₀ g₀ H₀ f₁ g₁ H₁ hr hf hg hH t ht i hi => ?_⟩
  have hr0 := abs_le.1 (hr 0); have hr1 := abs_le.1 (hr 1); have hr2 := abs_le.1 (hr 2)
  simp only [hermiteResidual, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hr0 hr1 hr2
  set c := hermiteCoeff f₀ g₀ H₀ f₁ g₁ H₁
  have hf' := abs_le.1 hf; have hg' := abs_le.1 hg; have hH' := abs_le.1 hH
  set r₀ := f₁ - f₀ - g₀ - H₀ / 2
  set r₁ := g₁ - g₀ - H₀
  set r₂ := H₁ - H₀
  have b0 : |f₀| ≤ 23 * κf := by linarith
  have b1 : |g₀| ≤ 23 * κf := by linarith
  have b2 : |H₀ / 2| ≤ 23 * κf := abs_le.2 ⟨by linarith, by linarith⟩
  have b3 : |10 * r₀ - 4 * r₁ + r₂ / 2| ≤ 23 * κf := abs_le.2 ⟨by linarith, by linarith⟩
  have b4 : |-15 * r₀ + 7 * r₁ - r₂| ≤ 23 * κf := abs_le.2 ⟨by linarith, by linarith⟩
  have b5 : |6 * r₀ - 3 * r₁ + r₂ / 2| ≤ 23 * κf := abs_le.2 ⟨by linarith, by linarith⟩
  have hc : ∀ j, |c j| ≤ 23 * κf := by
    intro j
    fin_cases j
    · simpa [c, hermiteCoeff] using b0
    · simpa [c, hermiteCoeff] using b1
    · simpa [c, hermiteCoeff] using b2
    · simpa [c, hermiteCoeff, hermiteResidual] using b3
    · simpa [c, hermiteCoeff, hermiteResidual] using b4
    · simpa [c, hermiteCoeff, hermiteResidual] using b5
  interval_cases i
  · rw [iteratedDeriv_zero]
    refine (abs_quintic_le c ht).trans ?_
    simp only [Fin.sum_univ_six]
    linarith [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5]
  · rw [iteratedDeriv_one, hermiteQuintic, deriv_quintic]
    refine (abs_quintic_le _ ht).trans ?_
    simp only [Fin.sum_univ_six]
    simp [derivCoeff, abs_mul]
    linarith [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5]
  · rw [hermiteQuintic, iteratedDeriv_two_quintic]
    refine (abs_quintic_le _ ht).trans ?_
    simp only [Fin.sum_univ_six]
    simp [derivCoeff, abs_mul]
    linarith [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5]

/-! ### Lemmas B.2.2–B.2.6 -/

variable {ε : ℝ} {kε : ℕ}

/-- **Lemma B.2.2** of [cartis2022evaluation]. Let `ε > 0` with `k_ε = ε⁻²` an integer
(`k_ε ε² = 1`, so `ε ≤ 1`). For `f = f_SDEX` (`Optimization.zigZagFunction ε k_ε`) the gradient at
the iterates is `∇f(x_k, y_k) = -((ε + ω_k)/√2) (1, (-1)^k)`, so `‖∇f(x_k, y_k)‖ = ε + ω_k`, for
`k ≤ k_ε` ((B.2.25), `ω_k = ε (k_ε - k)/k_ε`), and
steepest descent with the prescribed stepsize `√2` started at `(x₀, y₀) = 0` (any sequence with
`z_{k+1} = z_k - √2 ∇f(z_k)` before termination) needs exactly `k_ε` iterations to produce an
iterate with `‖∇f‖ ≤ ε`; its iterates are the zig-zag iterates `(x_k, y_k)`. -/
theorem lemma_B_2_2 (hε : 0 < ε) (hkε : (kε : ℝ) * ε ^ 2 = 1) :
    (∀ k ≤ kε, gradient (zigZagFunction ε kε) (zigZagIterate ε kε k) =
        -((ε + ZigZag.omega ε kε k) / √2) • !₂[1, (-1) ^ k] ∧
      ‖gradient (zigZagFunction ε kε) (zigZagIterate ε kε k)‖ = ε + ZigZag.omega ε kε k) ∧
    ∀ z : ℕ → EuclideanSpace ℝ (Fin 2), z 0 = 0 →
      (∀ k, (∀ j ≤ k, ¬ ‖gradient (zigZagFunction ε kε) (z j)‖ ≤ ε) →
        z (k + 1) = z k - √2 • gradient (zigZagFunction ε kε) (z k)) →
      (∀ k ≤ kε, z k = zigZagIterate ε kε k) ∧
        IsFirstHit (fun k => ‖gradient (zigZagFunction ε kε) (z k)‖ ≤ ε) kε := by
  have hadm : ZigZag.IsAdmissible ε kε := ⟨hε, hkε⟩
  set f := zigZagFunction ε kε
  have hnorm : ∀ k ≤ kε, ‖gradient f (zigZagIterate ε kε k)‖ = ε + ZigZag.omega ε kε k :=
    fun k hk => (zigZag_gradient hadm hk).2.1
  have hgt : ∀ j < kε, ¬ ‖gradient f (zigZagIterate ε kε j)‖ ≤ ε := fun j hj => by
    rw [hnorm j hj.le, not_le]; linarith [hadm.omega_pos hj]
  refine ⟨fun k hk => ⟨(zigZag_gradient hadm hk).1, hnorm k hk⟩, fun z hz0 hz => ?_⟩
  have heq : ∀ k ≤ kε, ∀ j ≤ k, z j = zigZagIterate ε kε j := by
    intro k
    induction k with
    | zero => exact fun _ j hj => by rw [Nat.le_zero.1 hj, hz0, ZigZag.zigZagIterate_zero]
    | succ k ih =>
      intro hk j hj
      have hx := ih (Nat.le_of_succ_le hk)
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact hx j (Nat.lt_succ_iff.1 hj)
      · have hstop : ∀ j ≤ k, ¬ ‖gradient f (z j)‖ ≤ ε := fun j hj => by
          rw [hx j hj]; exact hgt j (by omega)
        rw [hz k hstop, hx k le_rfl]
        exact ((zigZag_gradient hadm (k := k) (by omega)).2.2).symm
  have hx := heq kε le_rfl
  refine ⟨hx, ⟨?_, fun j hj => ?_⟩⟩
  · simp only
    rw [hx kε le_rfl, hnorm kε le_rfl, ZigZag.omega_self, add_zero]
  · simp only
    rw [hx j hj.le]; exact hgt j hj

/-- **Lemma B.2.3** of [cartis2022evaluation], for the corridor function
`f₂(x, y) = ψ(y - y_mid(x))` of the construction (`Optimization.ZigZag.f₂`). There is a constant
`C`, independent of `ε`, such that for every `ε > 0` with `k_ε ε² = 1`: `f₂` is twice continuously
differentiable, `|f₂(x, y)| ≤ C` on the bands `|y - y_mid(x)| ≤ 2` (which contain the book's
`[y_low(x) - 1, y_low(x)] ∪ [y_up(x), y_up(x) + 1]`), and its first and second derivatives (hence
all its first and second partial derivatives) are bounded by `C` on all of `ℝ²`. -/
theorem lemma_B_2_3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → (kε : ℝ) * ε ^ 2 = 1 →
      ContDiff ℝ 2 (ZigZag.f₂ ε kε) ∧ ∀ z : EuclideanSpace ℝ (Fin 2),
        (|z 1 - ZigZag.mid ε kε (z 0)| ≤ 2 → |ZigZag.f₂ ε kε z| ≤ C) ∧
        ‖fderiv ℝ (ZigZag.f₂ ε kε) z‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 (ZigZag.f₂ ε kε) z‖ ≤ C := by
  obtain ⟨C, hC, H⟩ := zigZag_hessian_bounds
  refine ⟨C, hC, fun ε kε hε hkε => ?_⟩
  obtain ⟨-, h2, hz⟩ := H ε kε ⟨hε, hkε⟩
  exact ⟨h2, fun z => ⟨(hz z).2.2.2, (hz z).2.2.1, (hz z).2.1⟩⟩

/-- **Lemma B.2.4** of [cartis2022evaluation]: `f_SDEX` is bounded below on `ℝ²` by a constant
independent of `ε`, so f.Bb holds. -/
theorem lemma_B_2_4 :
    ∃ flow : ℝ, ∀ (ε : ℝ) (kε : ℕ), 0 < ε → (kε : ℝ) * ε ^ 2 = 1 →
      Chapter02.AssumptionBb (zigZagFunction ε kε) flow := by
  obtain ⟨M, L, -, -, H⟩ := zigZag_bounds
  exact ⟨-M, fun ε kε hε hkε => (H ε kε ⟨hε, hkε⟩).2.1⟩

/-- **Lemma B.2.5** of [cartis2022evaluation]: `∇f_SDEX` is Lipschitz continuous on `ℝ²` with a
constant independent of `ε`, so f.gL holds; moreover `f_SDEX` is twice continuously
differentiable with second derivative bounded independently of `ε`. -/
theorem lemma_B_2_5 :
    ∃ L C : ℝ, ∀ (ε : ℝ) (kε : ℕ), 0 < ε → (kε : ℝ) * ε ^ 2 = 1 →
      Chapter02.AssumptionGL (zigZagFunction ε kε) L ∧ ContDiff ℝ 2 (zigZagFunction ε kε) ∧
        ∀ z, ‖iteratedFDeriv ℝ 2 (zigZagFunction ε kε) z‖ ≤ C := by
  obtain ⟨M, L, -, hL, H⟩ := zigZag_bounds
  obtain ⟨C, -, H'⟩ := zigZag_hessian_bounds
  refine ⟨L, C, fun ε kε hε hkε => ?_⟩
  obtain ⟨hC, -, hlip⟩ := H ε kε ⟨hε, hkε⟩
  obtain ⟨h2, -, hz⟩ := H' ε kε ⟨hε, hkε⟩
  exact ⟨.of_lipschitz hC hL hlip, h2, fun z => (hz z).1⟩

/-- **Lemma B.2.6** of [cartis2022evaluation] ("linesearches are exact"). For `ε > 0` with
`k_ε ε² = 1` and every `k < k_ε`, the step `√2` from `(x_k, y_k)` is the first global minimizer of
`f_SDEX` along the steepest-descent ray (`LineSearch.IsExactLineMin`, the exact linesearch
(2.2.26)); in particular `(x_{k+1}, y_{k+1})` is the first minimizer along `-∇f(x_k, y_k)`. -/
theorem lemma_B_2_6 (hε : 0 < ε) (hkε : (kε : ℝ) * ε ^ 2 = 1) {k : ℕ} (hk : k < kε) :
    LineSearch.IsExactLineMin (zigZagFunction ε kε) (zigZagIterate ε kε k) √2 ∧
      zigZagIterate ε kε (k + 1) = zigZagIterate ε kε k -
        √2 • gradient (zigZagFunction ε kε) (zigZagIterate ε kε k) :=
  ⟨zigZag_isExactLineMin ⟨hε, hkε⟩ hk, (zigZag_gradient ⟨hε, hkε⟩ hk.le).2.2⟩

end CartisGouldToint.AppendixB
