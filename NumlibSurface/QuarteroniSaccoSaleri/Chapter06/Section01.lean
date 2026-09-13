import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Complex.Norm
import Numlib.Analysis.Calculus.RootMultiplicity
import NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section01

/-!
# Quarteroni–Sacco–Saleri §6.1: conditioning of a nonlinear equation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §6.1. The equation is `f(x) = φ(x) - d = 0` with datum `d`; the
conditioning of its root is chapter 2's conditioning of the resolvent `G = φ⁻¹`, so (6.3) and the
multiple-root case (6.4) restate `example_2_4`, `example_2_4_rel` and `example_2_4_multiple_root`
of `Chapter02.Section01`, as the book itself does ("using the notation of Chapter 2"). Roots of
multiplicity `m` are `IsRootOfMultiplicity` (`Numlib/Analysis/Calculus/RootMultiplicity`), whose
Taylor factorization gives the error-versus-residual asymptotics the book writes as (6.4)–(6.7).

## Readings

* (6.4) writes `K_abs(d) ≃ |m! δd / f^{(m)}(α)|^{1/m} / |δd|`, a quantity depending on `δd`, not a
  condition number in the sense of Definition 2.1 — whose value at a multiple root is `+∞`
  (`equation_6_4_absCondNumber_eq_top`). Its content is the asymptotic
  `|δα| ~ (m! / |f^{(m)}(α)|)^{1/m} |δd|^{1/m}`, stated as the limit `equation_6_4`.
* The book's `≲` in (6.5)–(6.7) ("`a ≤ b` and `a ≃ c`") is read as: for every constant above the
  asymptotic one, the inequality holds for all perturbed roots close enough to `α`.
* (6.7) is stated for real roots of real polynomials; the complex form would need
  `IsRootOfMultiplicity` over `ℂ`, which is not in the backbone.
-/

open Conditioning Filter Polynomial Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

section Equation63

variable {φ G : ℝ → ℝ} {d : ℝ}

/-- **(6.3), absolute.** For the equation `f(x) = φ(x) - d = 0` with `φ` continuously
differentiable, invertible near `d` with continuous local inverse `G` (the resolvent `φ⁻¹`,
`φ (G y) = y` near `d`), and a simple root `α = G d` (`f'(α) ≠ 0`),
`K_abs(d) ≃ 1 / |f'(α)|`, as an equality for the first-order absolute condition number. This is
`example_2_4` of chapter 2 with `f' = φ'`. -/
theorem equation_6_3_abs (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hf' : deriv (fun x => φ x - d) (G d) ≠ 0) :
    absCondNumber G univ d = ENNReal.ofReal |deriv (fun x => φ x - d) (G d)|⁻¹ := by
  rw [deriv_sub_const] at hf' ⊢
  exact Chapter02.example_2_4 hφ hG hinv hf'

/-- **(6.3), relative.** Under the hypotheses of `equation_6_3_abs`, for `d ≠ 0` and `α ≠ 0`,
`K(d) ≃ |d| / (|α| |f'(α)|)`. This is `example_2_4_rel` of chapter 2. -/
theorem equation_6_3_rel (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hf' : deriv (fun x => φ x - d) (G d) ≠ 0) (hd : d ≠ 0)
    (hα : G d ≠ 0) :
    relCondNumber G univ d = ENNReal.ofReal (|d| / (|G d| * |deriv (fun x => φ x - d) (G d)|)) := by
  rw [deriv_sub_const] at hf' ⊢
  rw [Chapter02.example_2_4_rel hφ hG hinv hf' hd hα]
  congr 1
  have := abs_pos.2 hα
  have := abs_pos.2 hf'
  field_simp

/-- **(6.4), the multiple-root case, as a condition number**: if `α = G d` is a root of
`f = φ - d` of multiplicity `m ≥ 2` (so `f'(α) = 0`), the root problem has infinite first-order
absolute condition number, `K_abs(d) = +∞` — the book's "`K_abs(d)` could nevertheless be a large
number". This is `example_2_4_multiple_root` of chapter 2. -/
theorem equation_6_4_absCondNumber_eq_top (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) {m : ℕ} (hm : 2 ≤ m)
    (hα : IsRootOfMultiplicity (fun x => φ x - d) (G d) m) : absCondNumber G univ d = ⊤ := by
  refine Chapter02.example_2_4_multiple_root hφ hG hinv ?_
  have := hα.1 1 (by omega)
  rwa [iteratedDeriv_one, deriv_sub_const] at this

end Equation63

section MultipleRoot

variable {f : ℝ → ℝ} {α : ℝ} {m : ℕ}

/-- **(6.4), the multiple-root asymptotics.** If `α` is a root of `f ∈ C^m` of multiplicity `m`,
then `|x - α| / |f x|^{1/m} → (m! / |f^{(m)}(α)|)^{1/m}` as `x → α`, `x ≠ α`: a perturbation
`δd = f(α + δα)` of the datum moves the root by `|δα| ≃ (m! / |f^{(m)}(α)|)^{1/m} |δd|^{1/m}`,
which is what (6.4) says about `K_abs(d) ≃ |m! δd / f^{(m)}(α)|^{1/m} / |δd|`.
`IsRootOfMultiplicity.tendsto_abs_sub_div_abs_rpow`. -/
theorem equation_6_4 (hm : 1 ≤ m) (hf : ContDiffAt ℝ m f α) (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => |x - α| / |f x| ^ (1 / (m : ℝ))) (𝓝[≠] α)
      (𝓝 ((m.factorial / |iteratedDeriv m f α|) ^ (1 / (m : ℝ)))) :=
  hα.tendsto_abs_sub_div_abs_rpow hm hf

/-- **(6.5), error versus residual at a simple root.** If `f ∈ C¹` near a simple root `α ≠ 0`
(`f α = 0`, `f'(α) ≠ 0`), then for every `c > 1 / |f'(α)|` and every `α̂` close enough to `α`,
`|α̂ - α| / |α| ≤ c |r̂| / |α|` with the residual `r̂ = f(α̂)`: the book's
`|α̂ - α| / |α| ≲ |r̂| / (|f'(α)| |α|)`. The `m = 1` case of
`IsRootOfMultiplicity.eventually_abs_sub_le_mul_abs_rpow`. -/
theorem equation_6_5 (hf : ContDiffAt ℝ 1 f α) (hα : f α = 0) (hf' : deriv f α ≠ 0)
    (hα0 : α ≠ 0) {c : ℝ} (hc : 1 / |deriv f α| < c) :
    ∀ᶠ x in 𝓝 α, |x - α| / |α| ≤ c * |f x| / |α| := by
  have hroot : IsRootOfMultiplicity f α 1 := isRootOfMultiplicity_one_iff.2 ⟨hα, hf'⟩
  have hc' : ((1 : ℕ).factorial / |iteratedDeriv 1 f α|) ^ (1 / ((1 : ℕ) : ℝ)) < c := by
    simpa using hc
  filter_upwards [hroot.eventually_abs_sub_le_mul_abs_rpow le_rfl (by simpa using hf) hc'] with x hx
  have hα' : 0 < |α| := abs_pos.2 hα0
  rw [div_le_div_iff_of_pos_right hα']
  simpa using hx

/-- `(m! / |f^{(m)}(α)|)^{1/m} / |α| = (m! / (|f^{(m)}(α)| |α|^m))^{1/m}`: the constants of (6.4)
and (6.6). -/
theorem rpow_div_abs_eq {a b : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) :
    a ^ (1 / (m : ℝ)) / |b| = (a / |b| ^ m) ^ (1 / (m : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  rw [Real.div_rpow ha (pow_nonneg (abs_nonneg b) m), one_div,
    Real.pow_rpow_inv_natCast (abs_nonneg b) hm0]

/-- **(6.6), error versus residual at a root of multiplicity `m`.** If `α ≠ 0` is a root of
`f ∈ C^m` of multiplicity `m ≥ 1`, then for every `c > (m! / (|f^{(m)}(α)| |α|^m))^{1/m}` and
every `α̂` close enough to `α`, `|α̂ - α| / |α| ≤ c |r̂|^{1/m}` with `r̂ = f(α̂)`.
`IsRootOfMultiplicity.eventually_abs_sub_le_mul_abs_rpow` with the constant `c |α|`. -/
theorem equation_6_6 (hm : 1 ≤ m) (hf : ContDiffAt ℝ m f α) (hα : IsRootOfMultiplicity f α m)
    (hα0 : α ≠ 0) {c : ℝ}
    (hc : (m.factorial / (|iteratedDeriv m f α| * |α| ^ m)) ^ (1 / (m : ℝ)) < c) :
    ∀ᶠ x in 𝓝 α, |x - α| / |α| ≤ c * |f x| ^ (1 / (m : ℝ)) := by
  have hα' : 0 < |α| := abs_pos.2 hα0
  have hc' : (m.factorial / |iteratedDeriv m f α|) ^ (1 / (m : ℝ)) < c * |α| := by
    rw [← div_lt_iff₀ hα', rpow_div_abs_eq (by positivity) hm, div_div]
    exact hc
  filter_upwards [hα.eventually_abs_sub_le_mul_abs_rpow hm hf hc'] with x hx
  rw [div_le_iff₀ hα']
  linarith

/-- **(6.7), sensitivity of a polynomial root to a perturbation of the coefficients.** Let
`α ≠ 0` be a real root of `p : ℝ[X]` of multiplicity `m ≥ 1` and `q` a perturbation polynomial.
For every `c > (m! / (|p^{(m)}(α)| |α|^m))^{1/m}` there is `δ > 0` such that every real root `α̂`
of `p + q` with `|α̂ - α| < δ` satisfies `|α̂ - α| / |α| ≤ c |q(α̂)|^{1/m}` — (6.6) for `f = p`,
whose residual at `α̂` is `p(α̂) = -q(α̂)`. Stated for real roots; the book's complex roots would
need `IsRootOfMultiplicity` over `ℂ`. -/
theorem equation_6_7 {p q : ℝ[X]} {α : ℝ} (hα0 : α ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (hmult : p.rootMultiplicity α = m) {c : ℝ}
    (hc : (m.factorial / (|(derivative^[m] p).eval α| * |α| ^ m)) ^ (1 / (m : ℝ)) < c) :
    ∃ δ > 0, ∀ x, |x - α| < δ → (p + q).IsRoot x →
      |x - α| / |α| ≤ c * |q.eval x| ^ (1 / (m : ℝ)) := by
  have hp : p ≠ 0 := by
    rintro rfl
    rw [rootMultiplicity_zero] at hmult
    omega
  have hroot : IsRootOfMultiplicity (fun x => p.eval x) α m :=
    (isRootOfMultiplicity_eval_iff hp).2 hmult
  have hf : ContDiffAt ℝ m (fun x => p.eval x) α := by
    have := Polynomial.contDiff_aeval (𝕜 := ℝ) p m
    simpa [Polynomial.coe_aeval_eq_eval] using this.contDiffAt
  have hc' : (m.factorial / (|iteratedDeriv m (fun x => p.eval x) α| * |α| ^ m)) ^ (1 / (m : ℝ))
      < c := by
    rwa [iteratedDeriv_eval]
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (equation_6_6 hm hf hroot hα0 hc')
  refine ⟨δ, hδ, fun x hx hroot' => ?_⟩
  have := h (by rwa [Real.dist_eq])
  have hq : |p.eval x| = |q.eval x| := by
    rw [IsRoot.def, eval_add, add_eq_zero_iff_eq_neg] at hroot'
    rw [hroot', abs_neg]
  simpa [hq] using this

end MultipleRoot

section Example61

open Complex

/-- **Example 6.1, the roots.** For `0 < ε`, the roots of the perturbed polynomial
`p̂₄(x) = (x - 1)⁴ - ε` are exactly the four complex numbers `1 + ε^{1/4} iᵏ`, `k = 0, 1, 2, 3`:
they lie at angular spacing `π/2` on the circle of radius `ε^{1/4}` about `1`, the fourfold root
of `p₄ = (x - 1)⁴`. -/
theorem example_6_1 {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ((X - 1) ^ 4 - C (ε : ℂ)).IsRoot z ↔
      ∃ k : Fin 4, z = 1 + ((ε ^ (1 / 4 : ℝ) : ℝ) : ℂ) * I ^ (k : ℕ) := by
  set r : ℝ := ε ^ (1 / 4 : ℝ) with hr
  have hr4 : r ^ 4 = ε := by
    rw [hr, one_div, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_inv_natCast_pow hε.le (by norm_num)]
  have hr0 : 0 < r := Real.rpow_pos_of_pos hε _
  have key : ∀ w : ℂ, w ^ 4 - (r : ℂ) ^ 4 =
      (w - r) * (w + r) * (w - r * I) * (w + r * I) := by
    intro w
    ring_nf
    simp only [I_sq]
    ring
  have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq, neg_one_mul]
  have hε' : (ε : ℂ) = (r : ℂ) ^ 4 := by rw [← hr4]; push_cast; rfl
  rw [IsRoot.def, eval_sub, eval_pow, eval_sub, eval_X, eval_one, eval_C, hε', key,
    mul_eq_zero, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg,
    add_eq_zero_iff_eq_neg]
  constructor
  · rintro (((h | h) | h) | h)
    · exact ⟨0, by simp only [Fin.val_zero, pow_zero]; linear_combination h⟩
    · exact ⟨2, by simp only [Fin.val_two, I_sq]; linear_combination h⟩
    · exact ⟨1, by simp only [Fin.val_one, pow_one]; linear_combination h⟩
    · exact ⟨3, by rw [show ((3 : Fin 4) : ℕ) = 3 from rfl, hI3]; linear_combination h⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl (Or.inl (Or.inl (by simp)))
    · exact Or.inl (Or.inr (by simp))
    · exact Or.inl (Or.inl (Or.inr (by simp [I_sq])))
    · exact Or.inr (by simp [hI3])

/-- **Example 6.1, the relative error.** Every root `α̂` of `(x - 1)⁴ - ε` has
`|α̂ - α| / |α| = ε^{1/4}` from the fourfold root `α = 1`: the problem is stable
(`α̂ → 1` as `ε → 0`) but ill-conditioned, and the right-hand side of (6.7) is exactly `ε^{1/4}`
(`m = 4`, `p₄^{(4)} = 4!`, `|q(α̂)| = ε`), so (6.7) is an equality here. -/
theorem example_6_1_norm {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : ((X - 1) ^ 4 - C (ε : ℂ)).IsRoot z) :
    ‖z - 1‖ / ‖(1 : ℂ)‖ = ε ^ (1 / 4 : ℝ) := by
  obtain ⟨k, rfl⟩ := (example_6_1 hε z).1 hz
  have hr0 : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.le _
  rw [norm_one, div_one, add_sub_cancel_left, norm_mul, norm_pow, norm_I, one_pow, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hr0]

end Example61

end QuarteroniSaccoSaleri.Chapter06
