/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Atkinson and Han, Section 6.1: Difference Approximations of Derivatives

This module formalizes Section 6.1 of [han2009theoretical]. The section introduces the forward,
backward and centred difference quotients (6.1.1)–(6.1.3) for $f'(x)$ and the centred second
difference (6.1.4) for $f''(x)$,
$$\frac{f(x + h) - f(x)}{h}, \quad \frac{f(x) - f(x - h)}{h}, \quad \frac{f(x + h) - f(x - h)}{2h},
  \quad \frac{f(x + h) - 2 f(x) + f(x - h)}{h^2},$$
with the errors $O(h)$, $O(h)$, $O(h^2)$ and $O(h^2)$. It then uses them in Example 6.1.1 to write
down the forward-time centred-space, the backward-time centred-space and the Crank–Nicolson schemes
for the heat equation $u_t = \nu u_{xx}$. The module states the four error estimates, the equivalent
forms of the three schemes, and the exact solution of the sample problem of the example. The proofs
use only Mathlib's calculus.

## Main results

* Equation (6.1.1), `AtkinsonHan.Chapter06.equation_6_1_1`: the forward difference quotient
  approximates $f'(x)$ to within $(h/2) M$, where $M$ bounds $|f''|$.
* Equation (6.1.2), `AtkinsonHan.Chapter06.equation_6_1_2`: the backward difference quotient
  approximates $f'(x)$ to within $(h/2) M$, where $M$ bounds $|f''|$.
* Equation (6.1.3), `AtkinsonHan.Chapter06.equation_6_1_3`: the centred difference quotient
  approximates $f'(x)$ to within $(h^2/6) M$, where $M$ bounds $|f'''|$.
* Equation (6.1.4), `AtkinsonHan.Chapter06.equation_6_1_4`: the centred second difference
  approximates $f''(x)$ to within $(h^2/12) M$, where $M$ bounds $|f''''|$.
* Example 6.1.1, `AtkinsonHan.Chapter06.example_6_1_1`: the difference equations (6.1.8), (6.1.12)
  and (6.1.16) of the three schemes are equivalent to the explicit or tridiagonal forms (6.1.11),
  (6.1.15) and (6.1.19).
* Example 6.1.1, `AtkinsonHan.Chapter06.example_6_1_1_exact`: $u(x, t) = e^{-t} \sin x$ solves the
  sample problem (6.1.5)–(6.1.7) with $\nu = 1$, $f = 0$ and $u_0(x) = \sin x$.

## Conventions

* The book writes the errors as $O(h)$ and $O(h^2)$. The statements give a bound with an explicit
  constant times a bound on the relevant derivative, which is what the rest of the chapter uses. The
  centred formulas need one more derivative than a naive count suggests, because terms of the two
  Taylor expansions cancel; this cancellation is what makes them second order, so the hypotheses are
  not weakened to the next lower derivative.

## Deviations from the source

* **Example 6.1.1, (6.1.19)** (typo). The book prints $u_{j \pm 1}^{m-1}$ where it means
  $v_{j \pm 1}^{m-1}$. See `AtkinsonHan.Chapter06.example_6_1_1`.

## Not formalized

* **Example 6.1.1, the grid and the side conditions.** The grid $x_j = j h_x$, $t_m = m h_t$ and the
  boundary and initial conditions (6.1.9)–(6.1.10), (6.1.13)–(6.1.14) and (6.1.17)–(6.1.18) are
  data, not claims.
* **Figures 6.1 and 6.2.** They plot computed errors, whose values a rigorous statement would have
  to compute again.

The section has no numbered theorem, and no later section uses the four estimates: Sections 6.2 and
6.3 take consistency as a hypothesis.
-/

open Set

namespace AtkinsonHan.Chapter06

section Differences

variable {f f' f'' f''' f'''' : ℝ → ℝ} {x h M : ℝ}

/-- The estimate behind the four difference formulas: if $g(0) = 0$ and $|g'(t)| \le C t^n$ on
$[0, b]$ with $D(n + 1) = C$, then $|g(t)| \le D t^{n+1}$ on $[0, b]$. -/
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

/-- **Equation (6.1.1)** of [han2009theoretical], the forward difference quotient. Let $h > 0$, and
let $f$ have the derivatives $f'$ and $f''$ on $[x, x + h]$ with $|f''(y)| \le M$ there. Then
$$\left| f'(x) - \frac{f(x + h) - f(x)}{h} \right| \le \frac{h}{2} M.$$
-/
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

/-- **Equation (6.1.2)** of [han2009theoretical], the backward difference quotient. Let $h > 0$, and
let $f$ have the derivatives $f'$ and $f''$ on $[x - h, x]$ with $|f''(y)| \le M$ there. Then
$$\left| f'(x) - \frac{f(x) - f(x - h)}{h} \right| \le \frac{h}{2} M.$$
-/
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

/-- For $0 \le t \le h$, the two points $x + t$ and $x - t$ lie in $[x - h, x + h]$. -/
private theorem mem_symm (hh : 0 < h) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) h) :
    x + t ∈ Icc (x - h) (x + h) ∧ x - t ∈ Icc (x - h) (x + h) :=
  ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩

/-- **Equation (6.1.3)** of [han2009theoretical], the centred difference quotient. Let $h > 0$, and
let $f$ have the derivatives $f'$, $f''$ and $f'''$ on $[x - h, x + h]$ with $|f'''(y)| \le M$
there. Then
$$\left| f'(x) - \frac{f(x + h) - f(x - h)}{2h} \right| \le \frac{h^2}{6} M.$$

The third derivative is needed: the Taylor expansions of $f(x + h)$ and $f(x - h)$ have the same
second-order terms, which cancel in the difference, so the leading error is the third-order
term. -/
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

/-- **Equation (6.1.4)** of [han2009theoretical], the centred second difference. Let $h > 0$, and
let $f$ have the derivatives $f'$, $f''$, $f'''$ and $f''''$ on $[x - h, x + h]$ with
$|f''''(y)| \le M$ there. Then
$$\left| f''(x) - \frac{f(x + h) - 2 f(x) + f(x - h)}{h^2} \right| \le \frac{h^2}{12} M.$$

The odd-order terms of the two Taylor expansions cancel, which turns the order $h$ of a naive
count into $h^2$. -/
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

/-- **Example 6.1.1** of [han2009theoretical], the three schemes for the heat equation. Let
$h_x \neq 0$, $h_t \neq 0$ and $r = \nu h_t / h_x^2$. Write $v = v_j^m$,
$v_\pm = v_{j \pm 1}^m$, $\bar v = v_j^{m-1}$, $\bar v_\pm = v_{j \pm 1}^{m-1}$ and
$w = v_j^{m+1}$, and let $f$ be a real number. The forward-time centred-space equation (6.1.8)
is equivalent to the explicit update (6.1.11):
$$\frac{w - v}{h_t} = \nu \frac{v_+ - 2v + v_-}{h_x^2} + f
  \iff w = (1 - 2r) v + r (v_+ + v_-) + h_t f.$$
The backward-time centred-space equation (6.1.12) is equivalent to the tridiagonal row (6.1.15):
$$\frac{v - \bar v}{h_t} = \nu \frac{v_+ - 2v + v_-}{h_x^2} + f
  \iff (1 + 2r) v - r (v_+ + v_-) = \bar v + h_t f.$$
The Crank–Nicolson equation (6.1.16) is equivalent to the tridiagonal row (6.1.19):
$$\frac{v - \bar v}{h_t} = \nu \frac{(v_+ - 2v + v_-) + (\bar v_+ - 2 \bar v + \bar v_-)}{2
  h_x^2} + f \iff (1 + r) v - \frac{r}{2} (v_+ + v_-) = (1 - r) \bar v + \frac{r}{2} (\bar v_+ +
  \bar v_-) + h_t f.$$

**Typo.** The book prints (6.1.19) with $u_{j \pm 1}^{m-1}$ where it means $v_{j \pm 1}^{m-1}$.

Each equivalence is what "can be written as" means in the book. The Lean variables `vp`, `vm`,
`vprev`, `vpprev` and `vmprev` stand for $v_+$, $v_-$, $\bar v$, $\bar v_+$ and $\bar v_-$. The
boundary and initial conditions (6.1.9)–(6.1.10), (6.1.13)–(6.1.14) and (6.1.17)–(6.1.18) are
data, not claims. -/
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

/-- **Example 6.1.1** of [han2009theoretical], the sample problem of Figures 6.1 and 6.2. For
$\nu = 1$, $f = 0$ and $u_0(x) = \sin x$, the function $u(x, t) = e^{-t} \sin x$ solves
(6.1.5)–(6.1.7), as the book says can be verified: $u_t = -e^{-t} \sin x$, $u_x = e^{-t} \cos x$
and $u_{xx} = -e^{-t} \sin x$, so $u_t = u_{xx}$; moreover $u(0, t) = u(\pi, t) = 0$ for all
$t$, and $u(x, 0) = \sin x$ for all $x$.

The statement is the conjunction of these six facts, with each derivative stated by
`HasDerivAt`. Figures 6.1 and 6.2 plot the errors of the forward and the backward schemes
against this solution; the plotted values are not stated. -/
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
