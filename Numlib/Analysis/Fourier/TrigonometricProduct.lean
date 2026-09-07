/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.AddCircle`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Fourier.TrigonometricBasis

/-!
# Products of trigonometric polynomials, and the sine products on a circle

The trigonometric polynomials of degree at most `n` on the circle of circumference `T`
(`trigPolyLE`) are closed under multiplication in the graded sense: a product of one of degree at
most `a` with one of degree at most `b` has degree at most `a + b`. That is the content of
`mul_mem_trigPolyLE`, and it is the trigonometric counterpart of `Polynomial.degree_mul_le`.

Its main use is to build a trigonometric polynomial with prescribed zeros. The factor `x ↦ sin (π (x
- y) / T)` is not a function on the circle — it is *anti*-periodic with period `T` — but a product
of an even number of such factors is, and `sinProd T y s` is the product of the `2 s` factors with
nodes `y 0, …, y (2 s - 1)`. It lies in `trigPolyLE T s` (`sinProd_mem_trigPolyLE`), so it is the
circle analogue of the monic polynomial `∏ (X - y j)` of degree `2 s`, which the alternation
arguments of best uniform approximation need in order to change sign at prescribed points.

## Main definitions

* `reFourier T c m : C(AddCircle T, ℝ)` is `x ↦ (c * fourier m x).re`, the general real member of
  the two-dimensional space of frequency `m`. It is the shape a product of two members of the real
  trigonometric system takes, and it lies in `trigPolyLE T n` as soon as `|m| ≤ n`.
* `sinPair T u v : C(AddCircle T, ℝ)` is `x ↦ sin (π (x - u) / T) * sin (π (x - v) / T)`, written
  out in the real trigonometric system so that its membership in `trigPolyLE T 1` is immediate.
* `sinProd T y s : C(AddCircle T, ℝ)` is the product of `sinPair T (y (2 i)) (y (2 i + 1))` over `i
  < s`, that is, `x ↦ ∏_{j < 2 s} sin (π (x - y j) / T)`.

## Main results

* `mul_mem_trigPolyLE`: degrees add under multiplication.
* `sinProd_mem_trigPolyLE` and `sinProd_coe`: the sine product is a trigonometric polynomial of
  degree at most `s`, and it evaluates to `∏_{j < 2 s} sin (π (x - y j) / T)`.
* `sin_pi_div_mul_pos`: on a period the factor `sin (π s / T)` has the sign of `s`, which is what
  makes the sine product change sign exactly at its nodes.
-/

open Complex MeasureTheory Set Submodule

open scoped ComplexConjugate Real

variable {T : ℝ}

/-! ### The real functions of a single frequency -/

/-- The general real function of frequency `m` on the circle of circumference `T`: the real part of
`c * fourier m`. For `c = trigWeight m` it is the `m`-th member `trigFun T m` of the real
trigonometric system, and every real linear combination of `trigFun T m` and `trigFun T (-m)` is of
this form. -/
noncomputable def reFourier (T : ℝ) (c : ℂ) (m : ℤ) : C(AddCircle T, ℝ) where
  toFun x := (c * fourier m x).re
  continuous_toFun :=
    Complex.continuous_re.comp (continuous_const.mul (fourier m).continuous)

@[simp]
theorem reFourier_apply (T : ℝ) (c : ℂ) (m : ℤ) (x : AddCircle T) :
    reFourier T c m x = (c * fourier m x).re :=
  rfl

theorem trigFun_eq_reFourier (T : ℝ) (m : ℤ) : trigFun T m = reFourier T (trigWeight m) m := rfl

/-- The real part of `c * fourier m` is a trigonometric polynomial of degree `|m|`: it is a linear
combination of `trigFun T m` and `trigFun T (-m)`. -/
theorem reFourier_mem_trigPolyLE (c : ℂ) {m : ℤ} {n : ℕ} (hm : m.natAbs ≤ n) :
    reFourier T c m ∈ trigPolyLE T n := by
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
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

/-- The product of two members of the real trigonometric system, resolved into the frequencies `i +
j` and `i - j`. It is the identity `2 (Re u) (Re v) = Re (u v) + Re (u conj v)` applied to `u =
trigWeight i * fourier i x` and `v = trigWeight j * fourier j x`, together with the multiplicativity
of the exponentials. -/
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

/-- **Degrees add under multiplication of trigonometric polynomials**: the product of one of degree
at most `a` with one of degree at most `b` has degree at most `a + b`. -/
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

/-- The product `x ↦ sin (π (x - u) / T) * sin (π (x - v) / T)` as a function on the circle of
circumference `T`. Each factor alone is anti-periodic, but the product is periodic; it is written
here in the real trigonometric system, through `sin A sin B = (cos (A - B) - cos (A + B)) / 2`, so
that `sinPair_mem_trigPolyLE` is immediate. -/
noncomputable def sinPair (T u v : ℝ) : C(AddCircle T, ℝ) :=
  (Real.cos (π * (u - v) / T) / 2) • trigFun T 0
    - (Real.cos (π * (u + v) / T) / (2 * √2)) • trigFun T 1
    - (Real.sin (π * (u + v) / T) / (2 * √2)) • trigFun T (-1)

theorem sinPair_mem_trigPolyLE (T u v : ℝ) : sinPair T u v ∈ trigPolyLE T 1 :=
  sub_mem (sub_mem (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by norm_num)))
      (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by norm_num))))
    (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by norm_num)))

/-- The value of `sinPair` at a real representative is the product of the two sines. -/
theorem sinPair_coe (u v x : ℝ) :
    sinPair T u v (x : AddCircle T) = Real.sin (π * (x - u) / T) * Real.sin (π * (x - v) / T) := by
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
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

/-- The product `x ↦ ∏_{j < 2 s} sin (π (x - y j) / T)` as a function on the circle of circumference
`T`, grouped into the `s` pairs of consecutive nodes so that each factor is periodic. It is the
circle analogue of the monic polynomial with prescribed zeros. -/
noncomputable def sinProd (T : ℝ) (y : ℕ → ℝ) (s : ℕ) : C(AddCircle T, ℝ) :=
  ∏ i ∈ Finset.range s, sinPair T (y (2 * i)) (y (2 * i + 1))

/-- **The sine product with `2 s` nodes is a trigonometric polynomial of degree at most `s`.** -/
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

/-- The value of the sine product at a real representative. -/
theorem sinProd_coe (y : ℕ → ℝ) (s : ℕ) (x : ℝ) :
    sinProd T y s (x : AddCircle T)
      = ∏ j ∈ Finset.range (2 * s), Real.sin (π * (x - y j) / T) := by
  induction s with
  | zero => simp [sinProd]
  | succ s ih =>
    rw [sinProd, Finset.prod_range_succ, ContinuousMap.mul_apply, ← sinProd, ih,
      sinPair_coe, show 2 * (s + 1) = 2 * s + 1 + 1 from by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, mul_assoc]

/-- On one period the factor `sin (π s / T)` has the sign of `s`: this is what makes the sine
product change sign exactly at each of its nodes. -/
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
