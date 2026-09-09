import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Atkinson–Han §6.1: difference approximations of derivatives

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §6.1.

The section opens with the forward, backward and centred difference quotients (6.1.1)–(6.1.3) and
the centred second difference (6.1.4), and then uses them to write down the forward-time
centred-space, backward-time centred-space and Crank–Nicolson schemes for the heat equation
`u_t = ν u_xx`.

Those four difference formulas are the section's whole mathematical content, and they are the whole
of this module.

The book writes the error of each formula as `O(h)` or `O(h²)`.  What that abbreviates, and what
the rest of the chapter uses, is a bound with an explicit constant against a bound on the relevant
derivative, so that is the form the four statements take here.  The centred formulas need one
derivative more than a naive count suggests, because the two Taylor expansions cancel to an extra
order; that cancellation is what makes them second order, and is why the hypotheses are not
weakened to the next lower derivative.

## Main results

* `equation_6_1_1`, `equation_6_1_2` — the forward and backward difference quotients approximate
  `f'(x)` to within `(h/2) M`, where `M` bounds `|f''|` on the interval used.
* `equation_6_1_3` — the centred difference quotient approximates `f'(x)` to within `(h²/6) M`,
  with `M` a bound for `|f'''|`.
* `equation_6_1_4` — the centred second difference approximates `f''(x)` to within `(h²/12) M`,
  with `M` a bound for `|f''''|`.
* `example_6_1_1` — the three schemes of Example 6.1.1 for the heat equation, each in the two forms
  the book writes it in: the difference equation (6.1.8), (6.1.12), (6.1.16) and the explicit or
  tridiagonal row (6.1.11), (6.1.15), (6.1.19) it "can be written as", with `r = ν h_t / h_x²`.
* `example_6_1_1_exact` — the sample problem of Figures 6.1 and 6.2: `u (x, t) = e^{-t} sin x`
  solves (6.1.5)–(6.1.7) for `ν = 1`, `f = 0` and `u₀ (x) = sin x`.

## Not formalized here

The rest of Example 6.1.1: the grid `x_j = j h_x`, `t_m = m h_t` and the boundary and initial
conditions (6.1.9)–(6.1.10), (6.1.13)–(6.1.14), (6.1.17)–(6.1.18) are data rather than claims, and
Figures 6.1–6.2 are plots of computed errors, whose numbers a rigorous statement would have to
recompute. The section numbers no theorem at all, and nothing downstream needs the four difference
estimates either: §6.2 and §6.3 take consistency as a hypothesis rather than deriving it from these
formulas.
-/

open Set

namespace AtkinsonHan.Chapter06

section Differences

variable {f f' f'' f''' f'''' : ℝ → ℝ} {x h M : ℝ}

/-- The single estimate behind all four formulas below, applied once for each order of the Taylor
expansion that has to be undone: a function vanishing at `0` whose derivative on `[0, b]` is
bounded by `C tⁿ` is itself bounded there by `D t^{n+1}`, where `D (n + 1) = C`. -/
private theorem abs_le_of_abs_deriv_le_mul_pow {g g' : ℝ → ℝ} {b C D : ℝ} (n : ℕ)
    (hD : D * (n + 1) = C) (hg0 : g 0 = 0)
    (hg : ∀ t ∈ Icc (0 : ℝ) b, HasDerivAt g (g' t) t)
    (hC : ∀ t ∈ Icc (0 : ℝ) b, |g' t| ≤ C * t ^ n) :
    ∀ t ∈ Icc (0 : ℝ) b, |g t| ≤ D * t ^ (n + 1) := by
  intro t ht
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => D * s ^ (n + 1)) (C * s ^ n) s := by
    intro s
    have hp := (hasDerivAt_pow (n + 1) s).const_mul D
    simp only [Nat.add_sub_cancel] at hp
    refine hp.congr_deriv ?_
    push_cast
    rw [← hD]
    ring
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (f' := g') (B := fun s : ℝ => D * s ^ (n + 1)) (B' := fun s : ℝ => C * s ^ n)
    (fun s hs => (hg s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hg s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (by simp [hg0]) hB
    (fun s hs => by simpa using hC s (Ico_subset_Icc_self hs)) ht
  simpa using hmain

/-- **(6.1.1)**: the *forward* difference quotient approximates `f'(x)` to first order.  If `f` has
a second derivative bounded by `M` on `[x, x + h]`, then
`|f'(x) − (f(x + h) − f(x))/h| ≤ (h/2) M`. -/
theorem equation_6_1_1 (hh : 0 < h) (hf : ∀ y ∈ Icc x (x + h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc x (x + h), HasDerivAt f' (f'' y) y)
    (hM : ∀ y ∈ Icc x (x + h), |f'' y| ≤ M) :
    |f' x - (f (x + h) - f x) / h| ≤ h / 2 * M := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) h, x + t ∈ Icc x (x + h) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h1 : ∀ t ∈ Icc (0 : ℝ) h, |f' (x + t) - f' x| ≤ M * t := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow (g := fun t => f' (x + t) - f' x)
      (g' := fun t => f'' (x + t)) (C := M) (D := M) 0 (by push_cast; ring) (by simp)
      (fun t ht => ((hf' _ (hmem t ht)).comp_const_add x t).sub_const (f' x))
      (fun t ht => by simpa using hM _ (hmem t ht))
    intro t ht
    simpa using hstep t ht
  have h2 : ∀ t ∈ Icc (0 : ℝ) h, |f (x + t) - f x - t * f' x| ≤ M / 2 * t ^ 2 := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow (g := fun t => f (x + t) - f x - t * f' x)
      (g' := fun t => f' (x + t) - f' x) (C := M) (D := M / 2) 1 (by push_cast; ring) (by simp)
      (fun t ht => (((hf _ (hmem t ht)).comp_const_add x t).sub_const (f x)).sub
        (hasDerivAt_mul_const (f' x)))
      (fun t ht => by simpa using h1 t ht)
    intro t ht
    simpa using hstep t ht
  have hkey := h2 h ⟨hh.le, le_refl h⟩
  have heq : f' x - (f (x + h) - f x) / h = -((f (x + h) - f x - h * f' x) / h) := by
    field_simp
    ring
  rw [heq, abs_neg, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  calc |f (x + h) - f x - h * f' x| ≤ M / 2 * h ^ 2 := hkey
    _ = h / 2 * M * h := by ring

/-- **(6.1.2)**: the *backward* difference quotient approximates `f'(x)` to first order.  If `f` has
a second derivative bounded by `M` on `[x − h, x]`, then
`|f'(x) − (f(x) − f(x − h))/h| ≤ (h/2) M`. -/
theorem equation_6_1_2 (hh : 0 < h) (hf : ∀ y ∈ Icc (x - h) x, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (x - h) x, HasDerivAt f' (f'' y) y)
    (hM : ∀ y ∈ Icc (x - h) x, |f'' y| ≤ M) :
    |f' x - (f x - f (x - h)) / h| ≤ h / 2 * M := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) h, x - t ∈ Icc (x - h) x := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h1 : ∀ t ∈ Icc (0 : ℝ) h, |f' (x - t) - f' x| ≤ M * t := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow (g := fun t => f' (x - t) - f' x)
      (g' := fun t => -f'' (x - t)) (C := M) (D := M) 0 (by push_cast; ring) (by simp)
      (fun t ht => ((hf' _ (hmem t ht)).comp_const_sub x t).sub_const (f' x))
      (fun t ht => by simpa using hM _ (hmem t ht))
    intro t ht
    simpa using hstep t ht
  have h2 : ∀ t ∈ Icc (0 : ℝ) h, |f (x - t) - f x + t * f' x| ≤ M / 2 * t ^ 2 := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow (g := fun t => f (x - t) - f x + t * f' x)
      (g' := fun t => -(f' (x - t) - f' x)) (C := M) (D := M / 2) 1 (by push_cast; ring) (by simp)
      (fun t ht => ((((hf _ (hmem t ht)).comp_const_sub x t).sub_const (f x)).add
        (hasDerivAt_mul_const (f' x))).congr_deriv (by ring))
      (fun t ht => by simpa [abs_sub_comm] using h1 t ht)
    intro t ht
    simpa using hstep t ht
  have hkey := h2 h ⟨hh.le, le_refl h⟩
  have heq : f' x - (f x - f (x - h)) / h = (f (x - h) - f x + h * f' x) / h := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  calc |f (x - h) - f x + h * f' x| ≤ M / 2 * h ^ 2 := hkey
    _ = h / 2 * M * h := by ring

section Centred

/-- The two reflected points `x ± t` lie in the symmetric interval `[x − h, x + h]`. -/
private theorem mem_symm (hh : 0 < h) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) h) :
    x + t ∈ Icc (x - h) (x + h) ∧ x - t ∈ Icc (x - h) (x + h) :=
  ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩

/-- **(6.1.3)**: the *centred* difference quotient approximates `f'(x)` to second order.  If `f` has
a third derivative bounded by `M` on `[x − h, x + h]`, then
`|f'(x) − (f(x + h) − f(x − h))/(2h)| ≤ (h²/6) M`.

The third derivative is genuinely needed: the expansions of `f(x + h)` and `f(x − h)` agree in
their second-order terms, which therefore cancel in the difference, and the leading error is the
third-order one. -/
theorem equation_6_1_3 (hh : 0 < h) (hf : ∀ y ∈ Icc (x - h) (x + h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (x - h) (x + h), HasDerivAt f' (f'' y) y)
    (hf'' : ∀ y ∈ Icc (x - h) (x + h), HasDerivAt f'' (f''' y) y)
    (hM : ∀ y ∈ Icc (x - h) (x + h), |f''' y| ≤ M) :
    |f' x - (f (x + h) - f (x - h)) / (2 * h)| ≤ h ^ 2 / 6 * M := by
  have h1 : ∀ t ∈ Icc (0 : ℝ) h, |f'' (x + t) - f'' (x - t)| ≤ 2 * M * t := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow (g := fun t => f'' (x + t) - f'' (x - t))
      (g' := fun t => f''' (x + t) + f''' (x - t)) (C := 2 * M) (D := 2 * M) 0
      (by push_cast; ring) (by simp)
      (fun t ht => (((hf'' _ (mem_symm hh ht).1).comp_const_add x t).sub
        ((hf'' _ (mem_symm hh ht).2).comp_const_sub x t)).congr_deriv (by ring))
      (fun t ht => by
        have hb : |f''' (x + t) + f''' (x - t)| ≤ 2 * M :=
          calc |f''' (x + t) + f''' (x - t)| ≤ |f''' (x + t)| + |f''' (x - t)| := abs_add_le _ _
            _ ≤ M + M := add_le_add (hM _ (mem_symm hh ht).1) (hM _ (mem_symm hh ht).2)
            _ = 2 * M := by ring
        simpa using hb)
    intro t ht
    simpa using hstep t ht
  have h2 : ∀ t ∈ Icc (0 : ℝ) h, |f' (x + t) + f' (x - t) - 2 * f' x| ≤ M * t ^ 2 := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow
      (g := fun t => f' (x + t) + f' (x - t) - 2 * f' x)
      (g' := fun t => f'' (x + t) - f'' (x - t)) (C := 2 * M) (D := M) 1 (by push_cast; ring)
      (by simp only [add_zero, sub_zero]; ring)
      (fun t ht => ((((hf' _ (mem_symm hh ht).1).comp_const_add x t).add
        ((hf' _ (mem_symm hh ht).2).comp_const_sub x t)).sub_const
        (2 * f' x)).congr_deriv (by ring))
      (fun t ht => by simpa using h1 t ht)
    intro t ht
    simpa using hstep t ht
  have h3 : ∀ t ∈ Icc (0 : ℝ) h, |f (x + t) - f (x - t) - 2 * t * f' x| ≤ M / 3 * t ^ 3 := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow
      (g := fun t => f (x + t) - f (x - t) - 2 * t * f' x)
      (g' := fun t => f' (x + t) + f' (x - t) - 2 * f' x) (C := M) (D := M / 3) 2
      (by push_cast; ring) (by simp)
      (fun t ht => by
        have hlin : HasDerivAt (fun s : ℝ => 2 * s * f' x) (2 * f' x) t := by
          simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).mul_const (f' x)
        exact ((((hf _ (mem_symm hh ht).1).comp_const_add x t).sub
          ((hf _ (mem_symm hh ht).2).comp_const_sub x t)).sub hlin).congr_deriv (by ring))
      (fun t ht => h2 t ht)
    intro t ht
    simpa using hstep t ht
  have hkey := h3 h ⟨hh.le, le_refl h⟩
  have h2h : (0 : ℝ) < 2 * h := by linarith
  have heq : f' x - (f (x + h) - f (x - h)) / (2 * h)
      = -((f (x + h) - f (x - h) - 2 * h * f' x) / (2 * h)) := by
    field_simp
    ring
  rw [heq, abs_neg, abs_div, abs_of_pos h2h, div_le_iff₀ h2h]
  calc |f (x + h) - f (x - h) - 2 * h * f' x| ≤ M / 3 * h ^ 3 := hkey
    _ = h ^ 2 / 6 * M * (2 * h) := by ring

/-- **(6.1.4)**: the *centred second difference* approximates `f''(x)` to second order.  If `f` has
a fourth derivative bounded by `M` on `[x − h, x + h]`, then
`|f''(x) − (f(x + h) − 2 f(x) + f(x − h))/h²| ≤ (h²/12) M`.

Here it is the odd-order terms of the two expansions that cancel, which is what turns the order `h`
a naive count would predict into `h²`. -/
theorem equation_6_1_4 (hh : 0 < h) (hf : ∀ y ∈ Icc (x - h) (x + h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (x - h) (x + h), HasDerivAt f' (f'' y) y)
    (hf'' : ∀ y ∈ Icc (x - h) (x + h), HasDerivAt f'' (f''' y) y)
    (hf''' : ∀ y ∈ Icc (x - h) (x + h), HasDerivAt f''' (f'''' y) y)
    (hM : ∀ y ∈ Icc (x - h) (x + h), |f'''' y| ≤ M) :
    |f'' x - (f (x + h) - 2 * f x + f (x - h)) / h ^ 2| ≤ h ^ 2 / 12 * M := by
  have h1 : ∀ t ∈ Icc (0 : ℝ) h, |f''' (x + t) - f''' (x - t)| ≤ 2 * M * t := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow (g := fun t => f''' (x + t) - f''' (x - t))
      (g' := fun t => f'''' (x + t) + f'''' (x - t)) (C := 2 * M) (D := 2 * M) 0
      (by push_cast; ring) (by simp)
      (fun t ht => (((hf''' _ (mem_symm hh ht).1).comp_const_add x t).sub
        ((hf''' _ (mem_symm hh ht).2).comp_const_sub x t)).congr_deriv (by ring))
      (fun t ht => by
        have hb : |f'''' (x + t) + f'''' (x - t)| ≤ 2 * M :=
          calc |f'''' (x + t) + f'''' (x - t)| ≤ |f'''' (x + t)| + |f'''' (x - t)| := abs_add_le _ _
            _ ≤ M + M := add_le_add (hM _ (mem_symm hh ht).1) (hM _ (mem_symm hh ht).2)
            _ = 2 * M := by ring
        simpa using hb)
    intro t ht
    simpa using hstep t ht
  have h2 : ∀ t ∈ Icc (0 : ℝ) h, |f'' (x + t) + f'' (x - t) - 2 * f'' x| ≤ M * t ^ 2 := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow
      (g := fun t => f'' (x + t) + f'' (x - t) - 2 * f'' x)
      (g' := fun t => f''' (x + t) - f''' (x - t)) (C := 2 * M) (D := M) 1 (by push_cast; ring)
      (by simp only [add_zero, sub_zero]; ring)
      (fun t ht => ((((hf'' _ (mem_symm hh ht).1).comp_const_add x t).add
        ((hf'' _ (mem_symm hh ht).2).comp_const_sub x t)).sub_const
        (2 * f'' x)).congr_deriv (by ring))
      (fun t ht => by simpa using h1 t ht)
    intro t ht
    simpa using hstep t ht
  have h3 : ∀ t ∈ Icc (0 : ℝ) h, |f' (x + t) - f' (x - t) - 2 * t * f'' x| ≤ M / 3 * t ^ 3 := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow
      (g := fun t => f' (x + t) - f' (x - t) - 2 * t * f'' x)
      (g' := fun t => f'' (x + t) + f'' (x - t) - 2 * f'' x) (C := M) (D := M / 3) 2
      (by push_cast; ring) (by simp)
      (fun t ht => by
        have hlin : HasDerivAt (fun s : ℝ => 2 * s * f'' x) (2 * f'' x) t := by
          simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).mul_const (f'' x)
        exact ((((hf' _ (mem_symm hh ht).1).comp_const_add x t).sub
          ((hf' _ (mem_symm hh ht).2).comp_const_sub x t)).sub hlin).congr_deriv (by ring))
      (fun t ht => h2 t ht)
    intro t ht
    simpa using hstep t ht
  have h4 : ∀ t ∈ Icc (0 : ℝ) h,
      |f (x + t) + f (x - t) - 2 * f x - t ^ 2 * f'' x| ≤ M / 12 * t ^ 4 := by
    have hstep := abs_le_of_abs_deriv_le_mul_pow
      (g := fun t => f (x + t) + f (x - t) - 2 * f x - t ^ 2 * f'' x)
      (g' := fun t => f' (x + t) - f' (x - t) - 2 * t * f'' x) (C := M / 3) (D := M / 12) 3
      (by push_cast; ring) (by simp only [add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul]; ring)
      (fun t ht => by
        have hsq : HasDerivAt (fun s : ℝ => s ^ 2 * f'' x) (2 * t * f'' x) t := by
          simpa using (hasDerivAt_pow 2 t).mul_const (f'' x)
        exact (((((hf _ (mem_symm hh ht).1).comp_const_add x t).add
          ((hf _ (mem_symm hh ht).2).comp_const_sub x t)).sub_const (2 * f x)).sub
          hsq).congr_deriv (by ring))
      (fun t ht => h3 t ht)
    intro t ht
    simpa using hstep t ht
  have hkey := h4 h ⟨hh.le, le_refl h⟩
  have hsq : (0 : ℝ) < h ^ 2 := by positivity
  have heq : f'' x - (f (x + h) - 2 * f x + f (x - h)) / h ^ 2
      = -((f (x + h) + f (x - h) - 2 * f x - h ^ 2 * f'' x) / h ^ 2) := by
    field_simp
    ring
  rw [heq, abs_neg, abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
  calc |f (x + h) + f (x - h) - 2 * f x - h ^ 2 * f'' x| ≤ M / 12 * h ^ 4 := hkey
    _ = h ^ 2 / 12 * M * h ^ 2 := by ring

end Centred

end Differences

/-! ### Example 6.1.1: the three schemes for the heat equation -/

section HeatSchemes

open Real

open scoped Real

/-- **Example 6.1.1**, the three difference equations and the forms the book solves them in. With
`r = ν h_t / h_x²`, the forward-time centred-space equation (6.1.8) is the explicit update (6.1.11),
the backward-time centred-space equation (6.1.12) is the tridiagonal row (6.1.15), and the
Crank–Nicolson equation (6.1.16) is the tridiagonal row (6.1.19). Each clause is an equivalence,
which is what "can be written as" means in the book, and each is the whole mathematical content of
the corresponding scheme: the boundary and initial conditions (6.1.9)–(6.1.10), (6.1.13)–(6.1.14)
and (6.1.17)–(6.1.18) are data rather than claims.

`w` is `v_j^{m+1}` in the first clause, `v` and `vprev` are `v_j^m` and `v_j^{m-1}`; `vp`, `vm` are
the space neighbours `v_{j±1}` at the same time level and `vpprev`, `vmprev` those at the previous
one. (6.1.19) is printed in the book with `u_{j±1}^{m-1}` where it means `v_{j±1}^{m-1}`. -/
theorem example_6_1_1 {ν hx ht r : ℝ} (hx0 : hx ≠ 0) (ht0 : ht ≠ 0) (hr : r = ν * ht / hx ^ 2)
    (w v vp vm vprev vpprev vmprev f : ℝ) :
    ((w - v) / ht = ν * ((vp - 2 * v + vm) / hx ^ 2) + f ↔
        w = (1 - 2 * r) * v + r * (vp + vm) + ht * f) ∧
      ((v - vprev) / ht = ν * ((vp - 2 * v + vm) / hx ^ 2) + f ↔
        (1 + 2 * r) * v - r * (vp + vm) = vprev + ht * f) ∧
      ((v - vprev) / ht
            = ν * (((vp - 2 * v + vm) + (vpprev - 2 * vprev + vmprev)) / (2 * hx ^ 2)) + f ↔
        (1 + r) * v - r / 2 * (vp + vm)
          = (1 - r) * vprev + r / 2 * (vpprev + vmprev) + ht * f) := by
  have hx2 : hx ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  subst hr
  refine ⟨?_, ?_, ?_⟩ <;>
    · constructor <;> intro h <;> field_simp at h ⊢ <;> linarith

/-- **Example 6.1.1**, the sample problem of Figures 6.1 and 6.2: for `ν = 1`, `f = 0` and
`u₀ (x) = sin x`, the solution of (6.1.5)–(6.1.7) is `u (x, t) = e^{-t} sin x`, as the book says can
be verified. Its time derivative and its second space derivative are both `-e^{-t} sin x`, so it
solves the heat equation; it vanishes at `x = 0` and `x = π`, and reduces to `sin x` at `t = 0`.

Figures 6.1 and 6.2 plot the errors of the forward and backward schemes against this solution; the
plotted numbers are not stated. -/
theorem example_6_1_1_exact :
    (∀ x t : ℝ, HasDerivAt (fun s : ℝ => exp (-s) * sin x) (-(exp (-t) * sin x)) t) ∧
      (∀ x t : ℝ, HasDerivAt (fun y : ℝ => exp (-t) * sin y) (exp (-t) * cos x) x) ∧
      (∀ x t : ℝ, HasDerivAt (fun y : ℝ => exp (-t) * cos y) (-(exp (-t) * sin x)) x) ∧
      (∀ t : ℝ, exp (-t) * sin 0 = 0) ∧
      (∀ t : ℝ, exp (-t) * sin π = 0) ∧
      ∀ x : ℝ, exp (-(0 : ℝ)) * sin x = sin x := by
  refine ⟨fun x t => ?_, fun x t => ?_, fun x t => ?_, by simp, by simp, by simp⟩
  · simpa using ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).mul_const (sin x)
  · simpa using (Real.hasDerivAt_sin x).const_mul (exp (-t))
  · simpa using (Real.hasDerivAt_cos x).const_mul (exp (-t))

end HeatSchemes

end AtkinsonHan.Chapter06
