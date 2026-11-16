/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.AddCircle`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Fourier.TrigonometricBasis

/-!
# Products of trigonometric polynomials, and the sine products on a circle

Let $\mathbb{T}_T$ be the circle of circumference $T$, let $e_m(x) = e^{2 \pi i m x / T}$, let $t_m$
be the members of the real trigonometric system of `Numlib.Analysis.Fourier.TrigonometricBasis`, and
let $V_n$ be the space of trigonometric polynomials of degree at most $n$ (`trigPolyLE`). These
spaces are closed under multiplication in the graded sense: the product of a function in $V_a$ and a
function in $V_b$ lies in $V_{a + b}$ (`mul_mem_trigPolyLE`). This is the trigonometric counterpart
of `Polynomial.degree_mul_le`.

The main use of this fact is to build a trigonometric polynomial with prescribed zeros. The factor
$x \mapsto \sin(\pi (x - y) / T)$ is not a function on the circle, because it is antiperiodic with
period $T$. A product of an even number of such factors is a function on the circle. The sine
product $x \mapsto \prod_{j < 2s} \sin(\pi (x - y_j) / T)$ with the nodes $y_0, \dots, y_{2s - 1}$
lies in $V_s$ (`sinProd_mem_trigPolyLE`). It is the circle analogue of the monic polynomial
$\prod_j (X - y_j)$ of degree $2s$, which the alternation arguments of best uniform approximation
need in order to change sign at prescribed points.

## Main definitions

* `reFourier`: the function $x \mapsto \operatorname{Re}(c \, e_m(x))$, the general real function of
  frequency $m$. A product of two members of the real trigonometric system is a sum of such
  functions.
* `sinPair`: the function $x \mapsto \sin(\pi (x - u) / T) \sin(\pi (x - v) / T)$, written as a
  combination of $t_0$, $t_1$ and $t_{-1}$, so that it lies in $V_1$ by definition.
* `sinProd`: the sine product $x \mapsto \prod_{j < 2s} \sin(\pi (x - y_j) / T)$, as the product of
  $s$ functions `sinPair`.

## Main results

* `reFourier_mem_trigPolyLE`: for $|m| \le n$, the function $\operatorname{Re}(c \, e_m)$ lies in
  $V_n$.
* `trigFun_mul_trigFun`: $t_i t_j$ is a combination of real functions of frequencies $i + j$ and
  $i - j$.
* `mul_mem_trigPolyLE`: if $f \in V_a$ and $g \in V_b$, then $f g \in V_{a + b}$.
* `sinProd_mem_trigPolyLE`: the sine product with $2s$ nodes lies in $V_s$.
* `sinProd_coe`: the value of the sine product at $x$ is $\prod_{j < 2s} \sin(\pi (x - y_j) / T)$.
* `sin_pi_div_mul_pos`: for $0 < |s| < T$, the factor $\sin(\pi s / T)$ has the sign of $s$, so the
  sine product changes sign exactly at its nodes.
-/

open Complex MeasureTheory Set Submodule

open scoped ComplexConjugate Real

variable {T : ℝ}

/-! ### The real functions of a single frequency -/

/-- The **real function of frequency $m$** with coefficient $c \in \mathbb{C}$ on the circle of
circumference $T$: the continuous function
$$x \mapsto \operatorname{Re}\bigl(c \, e_m(x)\bigr), \qquad e_m(x) = e^{2 \pi i m x / T}.$$

For $c = w_m$ (`trigWeight m`) it is the member $t_m$ of the real trigonometric system. Every
real linear combination of $t_m$ and $t_{-m}$ has this form. The exponential $e_m$ is Mathlib's
`fourier m`. -/
noncomputable def reFourier (T : ℝ) (c : ℂ) (m : ℤ) : C(AddCircle T, ℝ) where
  toFun x := (c * fourier m x).re
  continuous_toFun :=
    Complex.continuous_re.comp (continuous_const.mul (fourier m).continuous)

/-- The value of the real function of frequency $m$ with coefficient $c$ at $x$ is
$\operatorname{Re}(c \, e_m(x))$. -/
@[simp]
theorem reFourier_apply (T : ℝ) (c : ℂ) (m : ℤ) (x : AddCircle T) :
    reFourier T c m x = (c * fourier m x).re :=
  rfl

/-- The member $t_m$ of the real trigonometric system is the real function of frequency $m$ with the
coefficient $w_m$. -/
theorem trigFun_eq_reFourier (T : ℝ) (m : ℤ) : trigFun T m = reFourier T (trigWeight m) m := rfl

/-- Let $c \in \mathbb{C}$, $m \in \mathbb{Z}$ and $n \in \mathbb{N}$ with $|m| \le n$. Then the
function $x \mapsto \operatorname{Re}(c \, e_m(x))$ lies in $V_n$.

The function is a linear combination of $t_m$ and $t_{-m}$. -/
theorem reFourier_mem_trigPolyLE (c : ℂ) {m : ℤ} {n : ℕ} (hm : m.natAbs ≤ n) :
    reFourier T c m ∈ trigPolyLE T n := by
  rcases lt_trichotomy m 0 with hneg | rfl | hpos
  · have key : reFourier T c m
        = (c.re / √2) • trigFun T (-m) + (c.im / √2) • trigFun T m := by
      ext x
      have hfm : fourier m x = conj (fourier (-m) x) := by
        rw [← fourier_neg, neg_neg]
      simp only [reFourier_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        smul_eq_mul, trigFun_apply, trigWeight_of_pos (by omega : (0 : ℤ) < -m),
        trigWeight_of_neg hneg, hfm]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    rw [key]
    exact add_mem (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by omega)))
      (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE hm))
  · have key : reFourier T c 0 = c.re • trigFun T 0 := by
      ext x
      simp [reFourier_apply]
    rw [key]
    exact Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by omega))
  · have key : reFourier T c m
        = (c.re / √2) • trigFun T m - (c.im / √2) • trigFun T (-m) := by
      ext x
      have hfm : fourier (-m) x = conj (fourier m x) := fourier_neg
      simp only [reFourier_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        smul_eq_mul, trigFun_apply, trigWeight_of_pos hpos,
        trigWeight_of_neg (by omega : -m < 0), hfm]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    rw [key]
    exact sub_mem (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE hm))
      (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by omega)))

/-! ### Degrees add under multiplication -/

/-- **The product of two members of the real trigonometric system**, resolved into the frequencies
$i + j$ and $i - j$: for $i, j \in \mathbb{Z}$,
$$t_i t_j = \frac{1}{2} \operatorname{Re}\bigl(w_i w_j \, e_{i + j}\bigr) + \frac{1}{2}
  \operatorname{Re}\bigl(w_i \overline{w_j} \, e_{i - j}\bigr).$$

The proof applies the identity $2 \operatorname{Re} u \operatorname{Re} v = \operatorname{Re}(u
v) + \operatorname{Re}(u \bar{v})$ to $u = w_i e_i(x)$ and $v = w_j e_j(x)$, together with
$e_i e_j = e_{i + j}$ and $e_i \overline{e_j} = e_{i - j}$. -/
theorem trigFun_mul_trigFun (T : ℝ) (i j : ℤ) :
    trigFun T i * trigFun T j
      = (1 / 2 : ℝ) • reFourier T (trigWeight i * trigWeight j) (i + j)
        + (1 / 2 : ℝ) • reFourier T (trigWeight i * conj (trigWeight j)) (i - j) := by
  ext x
  have hadd : fourier (i + j) x = fourier i x * fourier j x := fourier_add
  have hsub : fourier (i - j) x = fourier i x * conj (fourier j x) := by
    rw [sub_eq_add_neg, fourier_add, fourier_neg]
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    smul_eq_mul, trigFun_apply, reFourier_apply, hadd, hsub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Degrees add under multiplication of trigonometric polynomials**: let $a, b \in \mathbb{N}$,
let $f \in V_a$ and let $g \in V_b$. Then $f g \in V_{a + b}$. -/
theorem mul_mem_trigPolyLE {a b : ℕ} {f g : C(AddCircle T, ℝ)} (hf : f ∈ trigPolyLE T a)
    (hg : g ∈ trigPolyLE T b) : f * g ∈ trigPolyLE T (a + b) := by
  have hbase : ∀ i j : ℤ, i.natAbs ≤ a → j.natAbs ≤ b →
      trigFun T i * trigFun T j ∈ trigPolyLE T (a + b) := by
    intro i j hi hj
    rw [trigFun_mul_trigFun]
    exact add_mem (Submodule.smul_mem _ _ (reFourier_mem_trigPolyLE _ (by omega)))
      (Submodule.smul_mem _ _ (reFourier_mem_trigPolyLE _ (by omega)))
  obtain ⟨cf, rfl⟩ := mem_trigPolyLE_iff.mp hf
  obtain ⟨cg, rfl⟩ := mem_trigPolyLE_iff.mp hg
  rw [Finset.sum_mul_sum]
  refine sum_mem fun i hi => sum_mem fun j hj => ?_
  have hprod : (cf i • trigFun T i) * (cg j • trigFun T j)
      = cf i • (cg j • (trigFun T i * trigFun T j)) := by
    rw [smul_mul_assoc, mul_smul_comm]
  rw [hprod]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (hbase i j (by have := Finset.mem_Icc.mp hi; omega) (by have := Finset.mem_Icc.mp hj; omega)))

/-! ### Sine products -/

/-- For $u, v \in \mathbb{R}$, the function $x \mapsto \sin(\pi (x - u) / T) \sin(\pi (x - v) / T)$
on the circle of circumference $T$. It is defined as the combination
$$\frac{\cos(\pi (u - v) / T)}{2} t_0 - \frac{\cos(\pi (u + v) / T)}{2 \sqrt{2}} t_1 -
  \frac{\sin(\pi (u + v) / T)}{2 \sqrt{2}} t_{-1},$$
which equals the product of the two sines by $\sin A \sin B = (\cos(A - B) - \cos(A + B)) / 2$
(`sinPair_coe`).

Each factor alone is antiperiodic with period $T$, but the product is $T$-periodic. The
definition in the real trigonometric system makes `sinPair_mem_trigPolyLE` immediate. -/
noncomputable def sinPair (T u v : ℝ) : C(AddCircle T, ℝ) :=
  (Real.cos (π * (u - v) / T) / 2) • trigFun T 0
    - (Real.cos (π * (u + v) / T) / (2 * √2)) • trigFun T 1
    - (Real.sin (π * (u + v) / T) / (2 * √2)) • trigFun T (-1)

/-- For $u, v \in \mathbb{R}$, the function $x \mapsto \sin(\pi (x - u) / T) \sin(\pi (x - v) / T)$
lies in $V_1$. -/
theorem sinPair_mem_trigPolyLE (T u v : ℝ) : sinPair T u v ∈ trigPolyLE T 1 :=
  sub_mem (sub_mem (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by norm_num)))
      (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by norm_num))))
    (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by norm_num)))

/-- For $u, v, x \in \mathbb{R}$, the value of `sinPair T u v` at the class of $x$ on the circle is
$$\sin\Bigl(\frac{\pi (x - u)}{T}\Bigr) \sin\Bigl(\frac{\pi (x - v)}{T}\Bigr).$$
-/
theorem sinPair_coe (u v x : ℝ) :
    sinPair T u v (x : AddCircle T) = Real.sin (π * (x - u) / T) * Real.sin (π * (x - v) / T) := by
  have hprod : Real.sin (π * (x - u) / T) * Real.sin (π * (x - v) / T)
      = (Real.cos (π * (u - v) / T) - Real.cos (2 * π * x / T - π * (u + v) / T)) / 2 := by
    have e1 : π * (x - v) / T - π * (x - u) / T = π * (u - v) / T := by
      rw [div_sub_div_same]
      congr 1
      ring
    have e2 : π * (x - u) / T + π * (x - v) / T = 2 * π * x / T - π * (u + v) / T := by
      rw [← add_div, div_sub_div_same]
      congr 1
      ring
    rw [← e1, ← e2, Real.cos_sub, Real.cos_add]
    ring
  rw [sinPair]
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
    trigFun_zero, ContinuousMap.one_apply,
    trigFun_coe_apply_of_pos (by norm_num : (0 : ℤ) < 1),
    trigFun_coe_apply_of_neg (by norm_num : (-1 : ℤ) < 0)]
  rw [hprod, Real.cos_sub]
  push_cast
  have hs : Real.sin (-(2 * π * (-1 : ℝ) * x / T)) = Real.sin (2 * π * x / T) := by
    congr 1
    ring
  rw [hs]
  have hcc : Real.cos (2 * π * (1 : ℝ) * x / T) = Real.cos (2 * π * x / T) := by
    congr 1
    ring
  rw [hcc]
  field_simp
  ring

/-- The **sine product** with the nodes $y_0, \dots, y_{2s - 1}$ on the circle of circumference $T$:
the function
$$x \mapsto \prod_{j < 2s} \sin\Bigl(\frac{\pi (x - y_j)}{T}\Bigr).$$
It is defined as the product over $i < s$ of `sinPair T (y (2 * i)) (y (2 * i + 1))`, so that
each factor is periodic.

It is the circle analogue of the monic polynomial $\prod_j (X - y_j)$ with prescribed zeros.
Only the nodes $y_0, \dots, y_{2s - 1}$ of the sequence $y \colon \mathbb{N} \to \mathbb{R}$ are
used. -/
noncomputable def sinProd (T : ℝ) (y : ℕ → ℝ) (s : ℕ) : C(AddCircle T, ℝ) :=
  ∏ i ∈ Finset.range s, sinPair T (y (2 * i)) (y (2 * i + 1))

/-- **The sine product with $2s$ nodes is a trigonometric polynomial of degree at most $s$**: for
every $T \in \mathbb{R}$, every $y \colon \mathbb{N} \to \mathbb{R}$ and every
$s \in \mathbb{N}$, the sine product lies in $V_s$. -/
theorem sinProd_mem_trigPolyLE (T : ℝ) (y : ℕ → ℝ) (s : ℕ) :
    sinProd T y s ∈ trigPolyLE T s := by
  induction s with
  | zero =>
    have h1 : sinProd T y 0 = trigFun T 0 := by rw [sinProd, Finset.prod_range_zero, trigFun_zero]
    rw [h1]
    exact trigFun_mem_trigPolyLE (by norm_num)
  | succ s ih =>
    rw [sinProd, Finset.prod_range_succ]
    exact mul_mem_trigPolyLE ih (sinPair_mem_trigPolyLE T _ _)

/-- For $x \in \mathbb{R}$, the value of the sine product at the class of $x$ on the circle is
$$\prod_{j < 2s} \sin\Bigl(\frac{\pi (x - y_j)}{T}\Bigr).$$
-/
theorem sinProd_coe (y : ℕ → ℝ) (s : ℕ) (x : ℝ) :
    sinProd T y s (x : AddCircle T)
      = ∏ j ∈ Finset.range (2 * s), Real.sin (π * (x - y j) / T) := by
  induction s with
  | zero => simp [sinProd]
  | succ s ih =>
    rw [sinProd, Finset.prod_range_succ, ContinuousMap.mul_apply, ← sinProd, ih,
      sinPair_coe, show 2 * (s + 1) = 2 * s + 1 + 1 from by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, mul_assoc]

/-- Let $T > 0$ and let $s \in \mathbb{R}$ with $-T < s < T$ and $s \neq 0$. Then
$$\sin\Bigl(\frac{\pi s}{T}\Bigr) \cdot s > 0,$$
that is, on one period the factor $\sin(\pi s / T)$ has the sign of $s$.

This is what makes the sine product change sign exactly at each of its nodes. -/
theorem sin_pi_div_mul_pos (hT : 0 < T) {s : ℝ} (h1 : -T < s) (h2 : s < T) (hs : s ≠ 0) :
    0 < Real.sin (π * s / T) * s := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have hsin : Real.sin (π * s / T) < 0 := by
      have h : 0 < Real.sin (π * (-s) / T) := by
        refine Real.sin_pos_of_pos_of_lt_pi
          (div_pos (mul_pos Real.pi_pos (by linarith)) hT) ?_
        rw [div_lt_iff₀ hT]
        nlinarith [Real.pi_pos]
      have hneg' : Real.sin (π * (-s) / T) = -Real.sin (π * s / T) := by
        rw [show π * (-s) / T = -(π * s / T) from by ring, Real.sin_neg]
      linarith [hneg' ▸ h]
    nlinarith
  · have hsin : 0 < Real.sin (π * s / T) := by
      refine Real.sin_pos_of_pos_of_lt_pi (div_pos (mul_pos Real.pi_pos hpos) hT) ?_
      rw [div_lt_iff₀ hT]
      nlinarith [Real.pi_pos]
    exact mul_pos hsin hpos
