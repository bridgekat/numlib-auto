import Numlib.Backbone

/-!
# Saad, §6.11.1–6.11.2: Chebyshev polynomials and the min–max property

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.11.1–6.11.2.

`C k` is the book's `C_k`, the degree-`k` Chebyshev polynomial of the first kind of (6.109), which
is Mathlib's `Polynomial.Chebyshev.T ℝ k`; `Chat k α β γ` is the shifted and normalized
polynomial `Ĉ_k` of (6.113). The backbone's normalized polynomial `Polynomial.Chebyshev.shifted`
(`Numlib/RingTheory/Polynomial/ChebyshevMinimax.lean`) uses the affine map
`t ↦ (β + α - 2t)/(β - α)` where the book uses `t ↦ 1 + 2(t - β)/(β - α)`; the two differ by a
sign, which cancels in the quotient (`Chat_eq_shifted`), and every result of this file is read
off from the backbone through that identity: (6.109)–(6.112) from the closed forms, Theorem 6.25
from the backbone min–max pair `one_div_eval_T_le_sSup_abs_eval` / `sSup_abs_eval_shifted`.

The remaining quantities of §6.11 — `η`, `κ`, the `A`-norm and `ε^{(m)}` — belong to §6.11.3
and §6.11.4 and live in `Ch06/Convergence.lean`.

Deferred to the later phase (`tracker/saadsparse-ch6.md` §4, the complex-ellipse results):
Lemma 6.26 (Zarantonello) and Theorem 6.27 with the ellipse bound, that is (6.115)–(6.121) apart
from the definition (6.114). They need the complex Chebyshev and ellipse theory that the backbone
does not yet have; only `Ccomplex` is provided here for them.
-/

open Polynomial.Chebyshev (T shifted T_add_two T_eval_neg T_real_cos T_real_cosh
  eval_T_eq_half_add_pow half_pow_le_eval_T shifted_degree_le shifted_eval_self
  sSup_abs_eval_shifted one_div_eval_T_le_sSup_abs_eval)

open scoped Polynomial

namespace SaadSparse.Ch06

variable {t α β γ : ℝ}

/-! ### (6.109)–(6.112): the real Chebyshev polynomials -/

/-- **(6.109)**: the Chebyshev polynomial `C_k` of the first kind of degree `k`, Mathlib's
`Polynomial.Chebyshev.T ℝ k`. -/
noncomputable abbrev C (k : ℕ) : ℝ[X] := T ℝ (k : ℤ)

/-- **(6.114)**: the Chebyshev polynomials of the first kind over `ℂ`. They are used only by the
complex-ellipse results of §6.11.2 — Lemma 6.26, Theorem 6.27 and (6.117), (6.119)–(6.120) —
which are deferred to the later phase (`tracker/saadsparse-ch6.md` §4). -/
noncomputable abbrev Ccomplex (k : ℕ) : ℂ[X] := T ℂ (k : ℤ)

/-- **(6.109)**: `C_k(t) = cos(k cos⁻¹ t)` on `[-1, 1]`. -/
theorem equation_6_109 (k : ℕ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (C k).eval t = Real.cos (k * Real.arccos t) := by
  have h : Real.cos (Real.arccos t) = t := Real.cos_arccos ht.1 ht.2
  have hT := T_real_cos (Real.arccos t) (k : ℤ)
  rw [h] at hT
  exact hT.trans (by norm_cast)

/-- The three-term recurrence of §6.11.1: `C_{k+2} = 2 t C_{k+1} - C_k`. -/
theorem C_rec (k : ℕ) : C (k + 2) = 2 * Polynomial.X * C (k + 1) - C k := by
  have h := T_add_two (R := ℝ) (n := (k : ℤ))
  have h1 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
  have h2 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [show C (k + 2) = T ℝ (((k + 2 : ℕ) : ℤ)) from rfl, h1, h,
    show C (k + 1) = T ℝ (((k + 1 : ℕ) : ℤ)) from rfl, h2]

/-- `C_0 = 1`. -/
theorem C_zero : C 0 = 1 := Polynomial.Chebyshev.T_zero ℝ

/-- `C_1 = t`. -/
theorem C_one : C 1 = Polynomial.X := Polynomial.Chebyshev.T_one ℝ

/-- **(6.110)**: `C_k(t) = cosh(k cosh⁻¹ t)` for `t ≥ 1`. -/
theorem equation_6_110 (k : ℕ) (ht : 1 ≤ t) : (C k).eval t = Real.cosh (k * Real.arcosh t) := by
  have h : Real.cosh (Real.arcosh t) = t := Real.cosh_arcosh ht
  have hT := T_real_cosh (Real.arcosh t) (k : ℤ)
  rw [h] at hT
  exact hT.trans (by norm_cast)

/-- **(6.111)**: `C_k(t) = ½[(t + √(t²-1))^k + (t + √(t²-1))^{-k}]` for `t ≥ 1`. -/
theorem equation_6_111 (k : ℕ) (ht : 1 ≤ t) :
    (C k).eval t =
      ((t + Real.sqrt (t ^ 2 - 1)) ^ k + ((t + Real.sqrt (t ^ 2 - 1))⁻¹) ^ k) / 2 := by
  rw [Real.add_sqrt_self_sq_sub_one_inv ht]
  exact eval_T_eq_half_add_pow ht k

/-- **(6.112)**: `½ (t + √(t²-1))^k ≤ C_k(t)` for `t ≥ 1`; the book writes this growth estimate
as the approximation `C_k(t) ≳ ½ (t + √(t²-1))^k`. -/
theorem equation_6_112 (k : ℕ) (ht : 1 ≤ t) :
    (t + Real.sqrt (t ^ 2 - 1)) ^ k / 2 ≤ (C k).eval t :=
  half_pow_le_eval_T ht k

/-! ### (6.113): the shifted and normalized Chebyshev polynomial -/

/-- **(6.113)**: `Ĉ_k(t) = C_k(1 + 2(t - β)/(β - α)) / C_k(1 + 2(γ - β)/(β - α))`, the Chebyshev
polynomial of `[α, β]` normalized to `1` at `γ`. -/
noncomputable def Chat (k : ℕ) (α β γ : ℝ) : ℝ[X] :=
  Polynomial.C (1 / (C k).eval (1 + 2 * (γ - β) / (β - α))) *
    (C k).comp (Polynomial.C (1 - 2 * β / (β - α)) + Polynomial.C (2 / (β - α)) * Polynomial.X)

/-- The book's affine map is the negative of the backbone's: `1 + 2(x - β)/(β - α)` is
`-((β + α - 2x)/(β - α))`. -/
private theorem shift_neg (hαβ : α < β) (x : ℝ) :
    1 + 2 * (x - β) / (β - α) = -((β + α - 2 * x) / (β - α)) := by
  have h : β - α ≠ 0 := sub_ne_zero.mpr hαβ.ne'
  field_simp
  ring

private theorem eval_Chat (k : ℕ) (hαβ : α < β) (γ t : ℝ) :
    (Chat k α β γ).eval t =
      (T ℝ (k : ℤ)).eval (1 + 2 * (t - β) / (β - α)) /
        (T ℝ (k : ℤ)).eval (1 + 2 * (γ - β) / (β - α)) := by
  have h : β - α ≠ 0 := sub_ne_zero.mpr hαβ.ne'
  rw [Chat, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  rw [show 1 - 2 * β / (β - α) + 2 / (β - α) * t = 1 + 2 * (t - β) / (β - α) by
    field_simp; ring]
  ring

private theorem eval_shifted (k : ℕ) (hαβ : α < β) (γ t : ℝ) :
    (shifted k α β γ).eval t =
      (T ℝ (k : ℤ)).eval ((β + α - 2 * t) / (β - α)) /
        (T ℝ (k : ℤ)).eval ((β + α - 2 * γ) / (β - α)) := by
  have h : β - α ≠ 0 := sub_ne_zero.mpr hαβ.ne'
  rw [shifted, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  rw [show (β + α) / (β - α) - 2 / (β - α) * t = (β + α - 2 * t) / (β - α) by field_simp]
  ring

private theorem cast_negOnePow_ne_zero (m : ℤ) : ((m.negOnePow : ℤ) : ℝ) ≠ 0 := by
  rcases Int.isUnit_iff.1 (Units.isUnit m.negOnePow) with h | h <;> rw [h] <;> norm_num

private theorem abs_eval_T_neg (k : ℕ) (z : ℝ) :
    |(T ℝ (k : ℤ)).eval (-z)| = |(T ℝ (k : ℤ)).eval z| := by
  simp [T_eval_neg, abs_mul]

/-- **The bridge to the backbone**: the book's `Ĉ_k` of (6.113) is the backbone's
`Polynomial.Chebyshev.shifted`. The two affine maps differ by a sign and `T_k(-x)` is
`(-1)^k T_k(x)`, so the sign cancels in the quotient. -/
theorem Chat_eq_shifted (k : ℕ) (hαβ : α < β) (γ : ℝ) : Chat k α β γ = shifted k α β γ := by
  refine Polynomial.funext fun t => ?_
  rw [eval_Chat k hαβ γ t, eval_shifted k hαβ γ t, shift_neg hαβ t, shift_neg hαβ γ,
    T_eval_neg, T_eval_neg]
  exact mul_div_mul_left _ _ (cast_negOnePow_ne_zero _)

/-- **(6.113)**: `Ĉ_k(t) = C_k(1 + 2(t - β)/(β - α)) / C_k(1 + 2(γ - β)/(β - α))`. -/
theorem Chat_eval (k : ℕ) (hαβ : α < β) (γ t : ℝ) :
    (Chat k α β γ).eval t =
      (C k).eval (1 + 2 * (t - β) / (β - α)) / (C k).eval (1 + 2 * (γ - β) / (β - α)) :=
  eval_Chat k hαβ γ t

/-- `Ĉ_k` has degree at most `k`, so it is a competitor in the min–max problem of Theorem
6.25. -/
theorem Chat_degree_le (k : ℕ) (hαβ : α < β) (γ : ℝ) : (Chat k α β γ).degree ≤ k := by
  rw [Chat_eq_shifted k hαβ γ]
  exact shifted_degree_le k α β γ

/-- `Ĉ_k(γ) = 1`: the normalization of (6.113). -/
theorem Chat_eval_gamma (k : ℕ) (hαβ : α < β) (hγ : γ ∉ Set.Icc α β) :
    (Chat k α β γ).eval γ = 1 := by
  rw [Chat_eq_shifted k hαβ γ]
  exact shifted_eval_self k hαβ hγ

/-! ### Theorem 6.25: the Chebyshev min–max property -/

/-- **Theorem 6.25**: for a nondegenerate interval `[α, β]` and `γ ∉ [α, β]`, the minimum of
`max_{t ∈ [α, β]} |p(t)|` over the polynomials `p` of degree at most `k` with `p(γ) = 1` is
attained by `Ĉ_k` of (6.113).

The book says "non-empty interval `[α, β]`", read here as nondegenerate (`α < β`), since (6.113)
divides by `β - α`. -/
theorem theorem_6_25 (k : ℕ) (hαβ : α < β) (hγ : γ ∉ Set.Icc α β) :
    IsLeast {M : ℝ | ∃ p : ℝ[X], p.degree ≤ k ∧ p.eval γ = 1 ∧
        M = sSup ((fun t => |p.eval t|) '' Set.Icc α β)}
      (sSup ((fun t => |(Chat k α β γ).eval t|) '' Set.Icc α β)) := by
  refine ⟨⟨Chat k α β γ, Chat_degree_le k hαβ γ, Chat_eval_gamma k hαβ hγ, rfl⟩, ?_⟩
  rintro M ⟨p, hp, hpγ, rfl⟩
  rw [Chat_eq_shifted k hαβ γ, sSup_abs_eval_shifted k hαβ hγ]
  exact one_div_eval_T_le_sSup_abs_eval k hαβ hγ p hp hpγ

/-- **Theorem 6.25**, the value of the minimum: `1 / |C_k(1 + 2(γ - β)/(β - α))|`. -/
theorem theorem_6_25_value (k : ℕ) (hαβ : α < β) (hγ : γ ∉ Set.Icc α β) :
    sSup ((fun t => |(Chat k α β γ).eval t|) '' Set.Icc α β) =
      1 / |(C k).eval (1 + 2 * (γ - β) / (β - α))| := by
  rw [Chat_eq_shifted k hαβ γ, sSup_abs_eval_shifted k hαβ hγ,
    show (1 : ℝ) + 2 * (γ - β) / (β - α) = -((β + α - 2 * γ) / (β - α)) from shift_neg hαβ γ,
    abs_eval_T_neg]

/-- **Theorem 6.25**, the corollary formula: with `μ = (α + β)/2` the midpoint of the interval,
the minimum is `1 / |C_k(2(γ - μ)/(β - α))|`. -/
theorem theorem_6_25_value_mid (k : ℕ) (hαβ : α < β) (hγ : γ ∉ Set.Icc α β) :
    sSup ((fun t => |(Chat k α β γ).eval t|) '' Set.Icc α β) =
      1 / |(C k).eval (2 * (γ - (α + β) / 2) / (β - α))| := by
  have h : β - α ≠ 0 := sub_ne_zero.mpr hαβ.ne'
  rw [theorem_6_25_value k hαβ hγ,
    show (1 : ℝ) + 2 * (γ - β) / (β - α) = 2 * (γ - (α + β) / 2) / (β - α) by field_simp; ring]

end SaadSparse.Ch06
