import Numlib.Analysis.Fourier.Dirichlet
import Numlib.Analysis.Fourier.TrigonometricBasis
import NumlibSurface.AtkinsonHan.Chapter01.Section02
import NumlibSurface.AtkinsonHan.Chapter02.Section04
import NumlibSurface.AtkinsonHan.Chapter03.Section01

/-!
# Atkinson–Han §4.1: Fourier series

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §4.1.

The book works on `(-π, π)` and always means the `2 π`-periodic extension: the coefficients
(4.1.2)–(4.1.3), the partial sums (4.1.1) and Parseval's equality (4.1.13) are statements about
periodic functions.  So `L^p(-π, π)` is read here as `L^p` of the circle `AddCircle (2 π)` with its
probability Haar measure, and a function on the circle is turned into a `2 π`-periodic function on
`ℝ` by `fun x : ℝ => g ↑x`.  The two readings differ only by the normalising factor `2 π` of the
measure, which is `integral_intervalIntegral_eq` below.

The book's `a_j` and `b_j` of (4.1.2)–(4.1.3) are the backbone `fourierCoeffCos` and
`fourierCoeffSin` verbatim, and its `S_N` of (4.1.1) is `fourierPartialSum`; no surface definition
of them is needed, contrary to what the plan for this section supposed.  What the surface adds is
the dictionary between those and the two coefficient families the backbone and Mathlib use for
`L²` theory — `realFourierCoeff` against the orthonormal system `trigFun`, and Mathlib's complex
`fourierCoeff`.

## Main results

* `equation_4_1_3_const`, `equation_4_1_3_cos`, `equation_4_1_3_sin` — the book's `a_0`, `a_j`,
  `b_j` are `2`, `√2` and `√2` times the coefficients against the orthonormal system.
* `equation_4_1_5`, `equation_4_1_6_const`, `equation_4_1_6_cos`, `equation_4_1_6_sin` — the
  complex form: `c_j = (2 π)⁻¹ ∫ f (x) e^{-i j x} dx`, `a_0 = 2 c_0`, `a_j = 2 Re c_j`,
  `b_j = -2 Im c_j`.
* `equation_4_1_10_odd`, `equation_4_1_10_even` — an odd function has a sine series and an even
  function a cosine series, with the coefficients as integrals over `(0, π)`.
* `theorem_4_1_1`, `theorem_4_1_1_continuous` — pointwise convergence to the mean of the one-sided
  limits, and to `f x` where `f` is differentiable.
* `theorem_4_1_2` — `L^p` convergence of a sequence of partial-sum operators holds for every `f` if
  and only if the operators are uniformly bounded.
* `equation_4_1_13` — Parseval's equality in the book's normalisation.
* `equation_4_1_14`, `equation_4_1_15` — the `L²` and the uniform truncation error of the partial
  sums, both as tails of the coefficient series.
* `example_4_1_3`, `example_4_1_4`, `example_4_1_5` — the three worked Fourier series of the
  section: the step function, `|x|/π` and `(π² - x²)²/π⁴`, each with its coefficients, the closed
  form of its partial sums, and the limit of those sums at every point.

## The three examples

Each of Examples 4.1.3–4.1.5 is about the `2 π`-periodic extension of a function given on one
period, so its `f` is described by hypotheses — `Function.Periodic f (2 π)` together with the
book's formula on `[-π, 0)` and `[0, π)`, or on `[-π, π]` — rather than written out as a closed
term.  Those hypotheses determine `f` everywhere, and the coefficients depend only on the values
over one period.

The book's series `F x` is stated as the convergence of its terms in the sense of Definition
1.2.17, the ordered form `∑_{i < n} v i → s`.  Mathlib's `HasSum` would be the wrong statement:
the series of Example 4.1.3 is only conditionally convergent, so it has no unordered sum.  The
convergence itself is Theorem 4.1.1 in each case, never reproved: the extensions are locally
constant off the jumps (4.1.3), or differentiable off the corners with matching one-sided
difference quotients at them (4.1.4, 4.1.5).

## Not formalized here

The Gibbs phenomenon that the book discusses beside Example 4.1.3.  Its overshoot span
`(2/π) Si(π) |f (x+) - f (x-)|`, with `(2/π) Si(π) ≈ 1.17898`, is asserted without proof and
referred out, and it is the one part of that example `example_4_1_3` does not state.

The `L^p` boundedness (4.1.12) for `1 < p < ∞`, which is the M. Riesz theorem and is not in
Mathlib.  The partial-sum operators of Theorem 4.1.2 are therefore *given* as
a sequence of bounded operators fixing the trigonometric polynomials in the limit, rather than
constructed on `L^p`; at `p = 2` they are the truncations of `hasSum_trigSeries`, whose uniform
bound is Bessel's inequality, and the conclusion there is `equation_4_1_13`.
-/

open Filter MeasureTheory Topology

open scoped ENNReal Real

namespace AtkinsonHan.Chapter04

local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-! ### The circle and the interval -/

/-- **The identification of `L^p(-π, π)` with `L^p` of the circle**: the integral of a function on
`AddCircle (2 π)` against the probability Haar measure is `(2 π)⁻¹` times the integral of the
associated `2 π`-periodic function over `(-π, π)`.  Every statement of this section that mixes the
book's normalisation with the backbone's goes through it. -/
theorem integral_intervalIntegral_eq (g : AddCircle (2 * π) → ℝ) :
    ∫ b : AddCircle (2 * π), g b ∂AddCircle.haarAddCircle
      = (2 * π)⁻¹ * ∫ x in -π..π, g ↑x := by
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * π) (-π) g, smul_eq_mul,
    show -π + 2 * π = π by ring]

/-- The real Fourier coefficient of a function on the circle as an integral over `(-π, π)`. -/
private theorem realFourierCoeff_eq_intervalIntegral (g : AddCircle (2 * π) → ℝ) (n : ℤ) :
    realFourierCoeff g n = (2 * π)⁻¹ * ∫ x in -π..π, trigFun (2 * π) n ↑x * g ↑x := by
  rw [realFourierCoeff_apply]
  exact integral_intervalIntegral_eq (fun b => trigFun (2 * π) n b * g b)

/-! ### The real coefficients (4.1.1)–(4.1.3) -/

/-- **(4.1.2) at `j = 0`**: the book's `a_0 = π⁻¹ ∫_{-π}^{π} f` is twice the coefficient of `f`
against the constant member of the orthonormal system. -/
theorem equation_4_1_3_const (g : AddCircle (2 * π) → ℝ) :
    fourierCoeffCos (fun x : ℝ => g ↑x) 0 = 2 * realFourierCoeff g 0 := by
  have h1 : ∀ t : ℝ, g ↑t * Real.cos (((0 : ℕ) : ℝ) * t) = g ↑t := by
    intro t; norm_num
  have h2 : ∀ t : ℝ, trigFun (2 * π) 0 (↑t : AddCircle (2 * π)) * g ↑t = g ↑t := by
    intro t; rw [trigFun_zero]; simp
  simp only [fourierCoeffCos, realFourierCoeff_eq_intervalIntegral]
  rw [intervalIntegral.integral_congr (fun t _ => h1 t),
    intervalIntegral.integral_congr (fun t _ => h2 t)]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **(4.1.2)**: the book's cosine coefficient `a_j = π⁻¹ ∫_{-π}^{π} f (x) cos (j x) dx` is `√2`
times the coefficient of `f` against `trigFun (2 π) j = √2 cos (j x)`. -/
theorem equation_4_1_3_cos (g : AddCircle (2 * π) → ℝ) {j : ℕ} (hj : 0 < j) :
    fourierCoeffCos (fun x : ℝ => g ↑x) j = √2 * realFourierCoeff g j := by
  have hj' : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h2 : ∀ t : ℝ, trigFun (2 * π) (j : ℤ) (↑t : AddCircle (2 * π)) * g ↑t
      = √2 * (g ↑t * Real.cos ((j : ℝ) * t)) := by
    intro t
    rw [trigFun_coe_apply_of_pos hj']
    have harg : 2 * π * ((j : ℤ) : ℝ) * t / (2 * π) = (j : ℝ) * t := by
      push_cast
      field_simp
    rw [harg]
    ring
  simp only [fourierCoeffCos, realFourierCoeff_eq_intervalIntegral]
  rw [intervalIntegral.integral_congr (fun t _ => h2 t), intervalIntegral.integral_const_mul]
  obtain ⟨I, hI⟩ : ∃ I : ℝ, (∫ t in -π..π, g ↑t * Real.cos ((j : ℝ) * t)) = I := ⟨_, rfl⟩
  rw [hI]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **(4.1.3)**: the book's sine coefficient `b_j = π⁻¹ ∫_{-π}^{π} f (x) sin (j x) dx` is `√2`
times the coefficient of `f` against `trigFun (2 π) (-j) = √2 sin (j x)`. -/
theorem equation_4_1_3_sin (g : AddCircle (2 * π) → ℝ) {j : ℕ} (hj : 0 < j) :
    fourierCoeffSin (fun x : ℝ => g ↑x) j = √2 * realFourierCoeff g (-j) := by
  have hj' : (-(j : ℤ)) < 0 := by exact_mod_cast Int.neg_neg_of_pos (by exact_mod_cast hj)
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h2 : ∀ t : ℝ, trigFun (2 * π) (-(j : ℤ)) (↑t : AddCircle (2 * π)) * g ↑t
      = √2 * (g ↑t * Real.sin ((j : ℝ) * t)) := by
    intro t
    rw [trigFun_coe_apply_of_neg hj']
    have harg : -(2 * π * ((-(j : ℤ) : ℤ) : ℝ) * t / (2 * π)) = (j : ℝ) * t := by
      push_cast
      field_simp
    rw [harg]
    ring
  simp only [fourierCoeffSin, realFourierCoeff_eq_intervalIntegral]
  rw [intervalIntegral.integral_congr (fun t _ => h2 t), intervalIntegral.integral_const_mul]
  obtain ⟨I, hI⟩ : ∃ I : ℝ, (∫ t in -π..π, g ↑t * Real.sin ((j : ℝ) * t)) = I := ⟨_, rfl⟩
  rw [hI]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-! ### The complex form (4.1.4)–(4.1.6) -/

/-- **(4.1.5)**: the complex Fourier coefficient `c_j = (2 π)⁻¹ ∫_{-π}^{π} f (x) e^{-i j x} dx`.
This is Mathlib's `fourierCoeff` on `AddCircle (2 π)`, whose character `e^{2 π i j x / T}` is
`e^{i j x}` at `T = 2 π`. -/
theorem equation_4_1_5 (g : AddCircle (2 * π) → ℝ) (j : ℤ) :
    fourierCoeff (fun b => ((g b : ℝ) : ℂ)) j
      = ((2 * π)⁻¹ : ℝ) • ∫ x in -π..π, Complex.exp (-(j * x) * Complex.I) * (g ↑x : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := fourierCoeff_eq_intervalIntegral (fun b => ((g b : ℝ) : ℂ)) j (-π)
  rw [show -π + 2 * π = π by ring] at h
  rw [h, one_div]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [fourier_coe_apply, smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- **(4.1.6) at `j = 0`**: `a_0 = 2 c_0`. -/
theorem equation_4_1_6_const {g : AddCircle (2 * π) → ℝ}
    (hg : Integrable g AddCircle.haarAddCircle) :
    fourierCoeffCos (fun x : ℝ => g ↑x) 0 = 2 * (fourierCoeff (fun b => ((g b : ℝ) : ℂ)) 0).re := by
  rw [equation_4_1_3_const, realFourierCoeff_eq_fourierCoeff hg 0]
  simp

/-- **(4.1.6)**: `a_j = 2 Re c_j`. -/
theorem equation_4_1_6_cos {g : AddCircle (2 * π) → ℝ}
    (hg : Integrable g AddCircle.haarAddCircle) {j : ℕ} (hj : 0 < j) :
    fourierCoeffCos (fun x : ℝ => g ↑x) j = 2 * (fourierCoeff (fun b => ((g b : ℝ) : ℂ)) j).re := by
  have hj' : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
  rw [equation_4_1_3_cos g hj, realFourierCoeff_of_pos hg hj', ← mul_assoc,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **(4.1.6)**: `b_j = -2 Im c_j`. -/
theorem equation_4_1_6_sin {g : AddCircle (2 * π) → ℝ}
    (hg : Integrable g AddCircle.haarAddCircle) {j : ℕ} (hj : 0 < j) :
    fourierCoeffSin (fun x : ℝ => g ↑x) j
      = -(2 * (fourierCoeff (fun b => ((g b : ℝ) : ℂ)) j).im) := by
  have hj' : (-(j : ℤ)) < 0 := by exact_mod_cast Int.neg_neg_of_pos (by exact_mod_cast hj)
  rw [equation_4_1_3_sin g hj, realFourierCoeff_of_neg hg hj', fourierCoeff_ofReal_neg,
    Complex.conj_im, ← mul_assoc, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-! ### Sine and cosine series (4.1.7)–(4.1.10) -/

/-- The left half of `(-π, π)` is a subinterval of it. -/
private theorem uIcc_subset_left : Set.uIcc (-π) (0 : ℝ) ⊆ Set.uIcc (-π) π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
  exact Set.Icc_subset_Icc le_rfl (by linarith)

/-- The right half of `(-π, π)` is a subinterval of it. -/
private theorem uIcc_subset_right : Set.uIcc (0 : ℝ) π ⊆ Set.uIcc (-π) π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
  exact Set.Icc_subset_Icc (by linarith) le_rfl

/-- An odd function integrates to zero over `(-π, π)`. -/
private theorem intervalIntegral_of_odd {g : ℝ → ℝ} (hg : ∀ t, g (-t) = -g t)
    (hgi : IntervalIntegrable g volume (-π) π) : (∫ t in -π..π, g t) = 0 := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgi.mono_set uIcc_subset_left) (hgi.mono_set uIcc_subset_right)
  have hflip : (∫ t in -π..(0 : ℝ), g t) = -∫ t in (0 : ℝ)..π, g t := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) g
    rw [neg_zero] at h
    rw [← h, ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun t _ => hg t
  rw [← hsplit, hflip]
  ring

/-- An even function integrates over `(-π, π)` to twice its integral over `(0, π)`. -/
private theorem intervalIntegral_of_even {g : ℝ → ℝ} (hg : ∀ t, g (-t) = g t)
    (hgi : IntervalIntegrable g volume (-π) π) :
    (∫ t in -π..π, g t) = 2 * ∫ t in (0 : ℝ)..π, g t := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgi.mono_set uIcc_subset_left) (hgi.mono_set uIcc_subset_right)
  have hsame : (∫ t in -π..(0 : ℝ), g t) = ∫ t in (0 : ℝ)..π, g t := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) g
    rw [neg_zero] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun t _ => hg t
  rw [← hsplit, hsame]
  ring

/-- **(4.1.7)–(4.1.8), Exercise 4.1.2**: the Fourier series of an odd function is a sine series,
`a_j = 0` and `b_j = (2/π) ∫_0^π f (x) sin (j x) dx`.  With the odd extension of a function given
on `(0, π)` this is the book's sine series of that function. -/
theorem equation_4_1_10_odd {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hfi : IntervalIntegrable f volume (-π) π) (j : ℕ) :
    fourierCoeffCos f j = 0 ∧
      fourierCoeffSin f j = 2 / π * ∫ x in (0 : ℝ)..π, f x * Real.sin (j * x) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, ?_⟩
  · have h0 := intervalIntegral_of_odd (g := fun t => f t * Real.cos ((j : ℝ) * t))
      (fun t => by rw [mul_neg, Real.cos_neg, hodd t]; ring)
      (hfi.mul_continuousOn (Continuous.continuousOn (by fun_prop)))
    simp only [fourierCoeffCos, h0, mul_zero]
  · have h0 := intervalIntegral_of_even (g := fun t => f t * Real.sin ((j : ℝ) * t))
      (fun t => by rw [mul_neg, Real.sin_neg, hodd t]; ring)
      (hfi.mul_continuousOn (Continuous.continuousOn (by fun_prop)))
    simp only [fourierCoeffSin, h0]
    field_simp

/-- **(4.1.9)–(4.1.10), Exercise 4.1.3**: the Fourier series of an even function is a cosine
series, `b_j = 0` and `a_j = (2/π) ∫_0^π f (x) cos (j x) dx`. -/
theorem equation_4_1_10_even {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x)
    (hfi : IntervalIntegrable f volume (-π) π) (j : ℕ) :
    fourierCoeffSin f j = 0 ∧
      fourierCoeffCos f j = 2 / π * ∫ x in (0 : ℝ)..π, f x * Real.cos (j * x) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, ?_⟩
  · have h0 := intervalIntegral_of_odd (g := fun t => f t * Real.sin ((j : ℝ) * t))
      (fun t => by rw [mul_neg, Real.sin_neg, heven t]; ring)
      (hfi.mul_continuousOn (Continuous.continuousOn (by fun_prop)))
    simp only [fourierCoeffSin, h0, mul_zero]
  · have h0 := intervalIntegral_of_even (g := fun t => f t * Real.cos ((j : ℝ) * t))
      (fun t => by rw [mul_neg, Real.cos_neg, heven t])
      (hfi.mul_continuousOn (Continuous.continuousOn (by fun_prop)))
    simp only [fourierCoeffCos, h0]
    field_simp

/-! ### Pointwise convergence (Theorem 4.1.1) -/

/-- **Theorem 4.1.1**: at a point `x` where the `2 π`-periodic, interval-integrable `f` has
one-sided limits `f (x-) = fL` and `f (x+) = fR` *and* one-sided derivatives — both of which are
packed into the convergence of the one-sided difference quotients — the Fourier partial sums
converge to the mean `(f (x-) + f (x+)) / 2`.

The book's hypothesis "piecewise continuous" is read as interval integrability over one period,
which is all its proof uses.  The criterion behind it is Dini's,
`tendsto_fourierPartialSum_of_dini`, and the work here is only to check Dini's integrability
hypothesis: the symmetrised quotient is `(f (x + t) - fR)/t + (f (x - t) - fL)/t`, which is
bounded near `0` because each summand converges. -/
theorem theorem_4_1_1 {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π))
    (hfi : IntervalIntegrable f volume (-π) π) {x fL fR cL cR : ℝ}
    (hR : Tendsto (fun t : ℝ => (f (x + t) - fR) / t) (𝓝[>] 0) (𝓝 cR))
    (hL : Tendsto (fun t : ℝ => (f (x - t) - fL) / t) (𝓝[>] 0) (𝓝 cL)) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 ((fL + fR) / 2)) := by
  have hall := intervalIntegrable_of_periodic hf hfi
  have hshift : ∀ a b : ℝ, IntervalIntegrable (fun t => f (x + t)) volume a b := fun a b => by
    simpa using (hall (x + a) (x + b)).comp_add_left x
  have hrefl : ∀ a b : ℝ, IntervalIntegrable (fun t => f (x - t)) volume a b := fun a b => by
    simpa using (hall (x - a) (x - b)).comp_sub_left x
  have hφ : ∀ a b : ℝ,
      IntervalIntegrable (fun t => f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) volume a b :=
    fun a b => ((hshift a b).add (hrefl a b)).sub intervalIntegrable_const
  have hlim : Tendsto (fun t : ℝ => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (cR + cL)) := by
    refine Filter.Tendsto.congr (fun t => ?_) (hR.add hL)
    rw [← add_div]
    congr 1
    ring
  obtain ⟨δ, hδ0, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim 1 one_pos
  have hδ₀0 : 0 < min (δ / 2) π := lt_min (by linarith) Real.pi_pos
  have hδ₀π : min (δ / 2) π ≤ π := min_le_right _ _
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) (min (δ / 2) π),
      ‖(f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t‖ ≤ |cR + cL| + 1 := by
    intro t ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      calc t ≤ min (δ / 2) π := ht.2
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have h := hδ (Set.mem_Ioi.2 ht.1) hdist
    rw [Real.dist_eq] at h
    have habs := abs_sub_abs_le_abs_sub
      ((f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t) (cR + cL)
    rw [Real.norm_eq_abs]
    linarith
  have hq1 : IntervalIntegrable
      (fun t => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t) volume 0
      (min (δ / 2) π) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ₀0.le]
    have hm := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ₀0.le).mp
      (hφ 0 (min (δ / 2) π))).aestronglyMeasurable
    refine Integrable.mono' (integrable_const (|cR + cL| + 1))
      (hm.aemeasurable.div aemeasurable_id).aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hbound)
  have hq2 : IntervalIntegrable
      (fun t => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t) volume
      (min (δ / 2) π) π := by
    have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc (min (δ / 2) π) π) := by
      refine ContinuousOn.inv₀ continuousOn_id fun t ht => ?_
      rw [Set.uIcc_of_le hδ₀π] at ht
      exact ne_of_gt (lt_of_lt_of_le hδ₀0 ht.1)
    have heq : (fun t => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t)
        = fun t => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) * t⁻¹ :=
      funext fun t => div_eq_mul_inv _ _
    rw [heq]
    exact (hφ (min (δ / 2) π) π).mul_continuousOn hcont
  exact tendsto_fourierPartialSum_of_dini hf hfi (hq1.trans hq2)

/-- **Theorem 4.1.1**, the second clause: where `f` is differentiable the Fourier partial sums
converge to `f x`. -/
theorem theorem_4_1_1_continuous {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π))
    (hfi : IntervalIntegrable f volume (-π) π) {x c : ℝ} (hd : HasDerivAt f c x) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) :=
  tendsto_fourierPartialSum_of_hasDerivAt hf hfi hd

/-! ### `L^p` convergence (Theorem 4.1.2) -/

/-- The trigonometric polynomials are dense in `L^p` of the circle, for `1 ≤ p < ∞`: they are
dense in `C(AddCircle (2 π), ℝ)` by Corollary 3.1.4, and the continuous functions are dense in
`L^p`. -/
theorem dense_image_toLp_trigSpan {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense (ContinuousMap.toLp (E := ℝ) p
        (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ ''
      (Submodule.span ℝ (Set.range (trigFun (2 * π))) : Set C(AddCircle (2 * π), ℝ))) := by
  have hWdense : Dense (Submodule.span ℝ (Set.range (trigFun (2 * π))) :
      Set C(AddCircle (2 * π), ℝ)) := by
    intro f
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq, hqf⟩ := AtkinsonHan.Chapter03.corollary_3_1_4 f hε
    exact ⟨q, hq, by rwa [dist_eq_norm, norm_sub_rev]⟩
  have hTd := ContinuousMap.toLp_denseRange ℝ
    (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ hp (p := p)
  have hsub : Set.range (ContinuousMap.toLp (E := ℝ) p
      (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ) ⊆
      closure (ContinuousMap.toLp (E := ℝ) p
        (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ ''
        (Submodule.span ℝ (Set.range (trigFun (2 * π))) : Set C(AddCircle (2 * π), ℝ))) := by
    rintro _ ⟨q, rfl⟩
    refine image_closure_subset_closure_image (map_continuous _) ⟨q, ?_, rfl⟩
    rw [hWdense.closure_eq]
    trivial
  exact fun x => closure_minimal hsub isClosed_closure (hTd x)

/-- **Theorem 4.1.2** with (4.1.11)–(4.1.12): for `1 ≤ p < ∞`, a sequence of bounded operators on
`L^p(-π, π)` that converges to the identity on the trigonometric polynomials converges to the
identity on all of `L^p` **if and only if** it is uniformly bounded.

Forward is the principle of uniform boundedness (Theorem 2.4.4); backward is the density of the
trigonometric polynomials (Corollary 3.1.4) together with the backbone's density criterion.  The
book states this for the Fourier partial-sum operators `S_N`, which do converge to the identity on
trigonometric polynomials — each is fixed by `S_N` for all large `N` — and whose `L^p` boundedness
for a fixed `N` is elementary; the surface takes the operators as data, since Mathlib has no `L^p`
partial-sum operator to name.  At `p = 2` the uniform bound holds with constant `1` by Bessel's
inequality, and the resulting convergence is `equation_4_1_13`. -/
theorem theorem_4_1_2 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (S : ℕ → Lp ℝ p (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) →L[ℝ]
      Lp ℝ p (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))))
    (hS : ∀ q ∈ Submodule.span ℝ (Set.range (trigFun (2 * π))),
      Tendsto (fun N => S N (ContinuousMap.toLp (E := ℝ) p AddCircle.haarAddCircle ℝ q)) atTop
        (𝓝 (ContinuousMap.toLp (E := ℝ) p AddCircle.haarAddCircle ℝ q))) :
    (∀ f, Tendsto (fun N => ‖S N f - f‖) atTop (𝓝 0)) ↔ ∃ C : ℝ, ∀ N, ‖S N‖ ≤ C := by
  constructor
  · intro h
    refine AtkinsonHan.Chapter02.theorem_2_4_4 S fun v => ?_
    have hv : Tendsto (fun N => S N v) atTop (𝓝 v) := tendsto_iff_norm_sub_tendsto_zero.2 (h v)
    obtain ⟨M, hM⟩ := hv.norm.bddAbove_range
    exact ⟨M, fun N => hM ⟨N, rfl⟩⟩
  · rintro ⟨C, hC⟩ f
    have hon : ∀ w ∈ (ContinuousMap.toLp (E := ℝ) p
        (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ ''
        (Submodule.span ℝ (Set.range (trigFun (2 * π))) : Set C(AddCircle (2 * π), ℝ))),
        Tendsto (fun N => S N w) atTop
          (𝓝 (ContinuousLinearMap.id ℝ
            (Lp ℝ p (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) w)) := by
      rintro w ⟨q, hq, rfl⟩
      simpa using hS q hq
    have hid := ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded
      (dense_image_toLp_trigSpan (p := p) hp) hC hon f
    rw [ContinuousLinearMap.id_apply] at hid
    exact tendsto_iff_norm_sub_tendsto_zero.1 hid

/-! ### Parseval's equality (4.1.13) -/

/-- Fold an absolutely convergent sum over `ℤ` onto `ℕ` by pairing `n` with `-n`: the `0`-th term
stays alone and the `j`-th is `c j + c (-j)`.  This is the shape in which the book writes every
series over the trigonometric system. -/
private theorem hasSum_int_fold {c : ℤ → ℝ} {S : ℝ} (h : HasSum c S) :
    HasSum (fun j : ℕ => if j = 0 then c 0 else c j + c (-j)) S := by
  have h1 : HasSum (fun n : ℕ => c n + c (-n)) (S + c 0) := h.nat_add_neg
  have h2 := h1.update 0 (c 0)
  have hfun : Function.update (fun n : ℕ => c ↑n + c (-↑n)) 0 (c 0)
      = fun j : ℕ => if j = 0 then c 0 else c j + c (-j) := by
    funext j
    rw [Function.update_apply]
  have hval : c 0 - ((fun n : ℕ => c ↑n + c (-↑n)) 0) + (S + c 0) = S := by
    simp only [Nat.cast_zero, neg_zero]
    ring
  rw [hfun, hval] at h2
  exact h2

/-- The squared `L²` norm for the probability measure of the circle, as the book's integral over
`(-π, π)`: the two differ by the normalising factor `2 π` of the measure. -/
private theorem norm_sq_eq_intervalIntegral
    (F : Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
    ‖F‖ ^ 2 = (2 * π)⁻¹ * ∫ x in -π..π, (F : AddCircle (2 * π) → ℝ) ↑x ^ 2 := by
  rw [← integral_intervalIntegral_eq (fun b => (F : AddCircle (2 * π) → ℝ) b ^ 2),
    ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  dsimp only
  rw [RCLike.inner_apply]
  simp [sq]

/-- The coefficient dictionary in squared form: the book's `a_j²` is twice the square of the
coefficient against the orthonormal system. -/
private theorem sq_realFourierCoeff_cos (G : AddCircle (2 * π) → ℝ) {j : ℕ} (hj : 0 < j) :
    realFourierCoeff G j ^ 2 = fourierCoeffCos (fun x : ℝ => G ↑x) j ^ 2 / 2 := by
  rw [equation_4_1_3_cos G hj, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The coefficient dictionary in squared form, for the sines. -/
private theorem sq_realFourierCoeff_sin (G : AddCircle (2 * π) → ℝ) {j : ℕ} (hj : 0 < j) :
    realFourierCoeff G (-j) ^ 2 = fourierCoeffSin (fun x : ℝ => G ↑x) j ^ 2 / 2 := by
  rw [equation_4_1_3_sin G hj, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- **Parseval's equality (4.1.13)** in the book's normalisation:

`‖f‖²_{L²(-π,π)} = π (|a_0|²/2 + ∑_{j ≥ 1} (|a_j|² + |b_j|²))`.

The sum is stated as a `HasSum` over `ℕ` whose `0`-th term is `π |a_0|²/2`, which is the book's
display read literally.  It is `tsum_sq_realFourierCoeff` — Parseval for the orthonormal system —
transported by the coefficient dictionary of `equation_4_1_3_*` and the measure normalisation of
`integral_intervalIntegral_eq`. -/
theorem equation_4_1_13 (F : Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
    HasSum (fun j : ℕ =>
        if j = 0 then π * fourierCoeffCos (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) 0 ^ 2 / 2
        else π * (fourierCoeffCos (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) j ^ 2
          + fourierCoeffSin (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) j ^ 2))
      (∫ x in -π..π, (F : AddCircle (2 * π) → ℝ) ↑x ^ 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨G, hG⟩ : ∃ G : AddCircle (2 * π) → ℝ, (F : AddCircle (2 * π) → ℝ) = G := ⟨_, rfl⟩
  rw [hG]
  -- Parseval for the orthonormal system
  have hA : HasSum (fun n : ℤ => realFourierCoeff G n ^ 2) (‖F‖ ^ 2) := by
    have h := (trigBasis (2 * π)).hasSum_inner_mul_inner F F
    have hfe : (fun n : ℤ => inner ℝ F ((trigBasis (2 * π)) n) * inner ℝ ((trigBasis (2 * π)) n) F)
        = fun n : ℤ => realFourierCoeff G n ^ 2 := by
      funext n
      rw [coe_trigBasis, real_inner_comm, inner_trigLp, hG]
      ring
    rw [hfe, real_inner_self_eq_norm_sq] at h
    exact h
  -- the `L²` norm against the probability measure, and against the book's interval
  have hnorm : ‖F‖ ^ 2 = (2 * π)⁻¹ * ∫ x in -π..π, G ↑x ^ 2 := by
    rw [← hG]
    exact norm_sq_eq_intervalIntegral F
  -- the coefficient dictionary
  have hc0 : realFourierCoeff G 0 = fourierCoeffCos (fun x : ℝ => G ↑x) 0 / 2 := by
    rw [equation_4_1_3_const]; ring
  have hcj : ∀ j : ℕ, 0 < j →
      realFourierCoeff G j ^ 2 = fourierCoeffCos (fun x : ℝ => G ↑x) j ^ 2 / 2 :=
    fun j hj => sq_realFourierCoeff_cos G hj
  have hsj : ∀ j : ℕ, 0 < j →
      realFourierCoeff G (-j) ^ 2 = fourierCoeffSin (fun x : ℝ => G ↑x) j ^ 2 / 2 :=
    fun j hj => sq_realFourierCoeff_sin G hj
  -- fold the sum over `ℤ` onto `ℕ`, then rescale
  have hB := (hasSum_int_fold hA).mul_left (2 * π)
  have hfun : (fun j : ℕ => 2 * π *
        if j = 0 then realFourierCoeff G 0 ^ 2
        else realFourierCoeff G j ^ 2 + realFourierCoeff G (-j) ^ 2)
      = fun j : ℕ =>
        if j = 0 then π * fourierCoeffCos (fun x : ℝ => G ↑x) 0 ^ 2 / 2
        else π * (fourierCoeffCos (fun x : ℝ => G ↑x) j ^ 2
          + fourierCoeffSin (fun x : ℝ => G ↑x) j ^ 2) := by
    funext j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [ite_eq_left rfl, ite_eq_left rfl, hc0]
      ring
    · rw [ite_eq_right hj, ite_eq_right hj, hcj j (Nat.pos_of_ne_zero hj),
        hsj j (Nat.pos_of_ne_zero hj)]
      ring
  rw [hfun] at hB
  have hval : 2 * π * ‖F‖ ^ 2 = ∫ x in -π..π, G ↑x ^ 2 := by
    rw [hnorm]
    field_simp
  rwa [hval] at hB

/-! ### Examples 4.1.3–4.1.5: three concrete Fourier series -/

/-- The `n`-th partial sum of a Fourier series is `2 π`-periodic: its terms are `cos (j x)` and
`sin (j x)` with integer frequencies. Together with the periodicity of `f` this is what carries the
three examples below from one period to all of `ℝ`. -/
private theorem fourierPartialSum_periodic (f : ℝ → ℝ) (n : ℕ) :
    Function.Periodic (fourierPartialSum f n) (2 * π) := by
  intro x
  simp only [fourierPartialSum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (j : ℝ) * (x + 2 * π) = (j : ℝ) * x + (j : ℕ) * (2 * π) by ring,
    Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

/-- Every real number lands in `[-π, π)` after subtracting an integer multiple of `2 π`. -/
private theorem exists_int_sub_mem_Ico (x : ℝ) :
    ∃ k : ℤ, x - k * (2 * π) ∈ Set.Ico (-π) π := by
  refine ⟨toIcoDiv Real.two_pi_pos (-π) x, ?_⟩
  have hmem := toIcoMod_mem_Ico Real.two_pi_pos (-π) x
  have heq := toIcoMod_sub_self Real.two_pi_pos (-π) x
  rw [zsmul_eq_mul] at heq
  rw [show -π + 2 * π = π by ring] at hmem
  have hrw : toIcoMod Real.two_pi_pos (-π) x
      = x - (toIcoDiv Real.two_pi_pos (-π) x : ℤ) * (2 * π) := by
    push_cast at heq
    linarith
  rwa [hrw] at hmem

/-- `∫_{-π}^{0} cos (j t) dt = 0` for `j ≥ 1`. -/
private theorem integral_cos_neg_pi_zero {j : ℕ} (hj : 0 < j) :
    (∫ t in -π..(0 : ℝ), Real.cos ((j : ℝ) * t)) = 0 := by
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hd : ∀ t ∈ Set.uIcc (-π) (0 : ℝ),
      HasDerivAt (fun s : ℝ => Real.sin ((j : ℝ) * s) / j) (Real.cos ((j : ℝ) * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (j : ℝ) * s) (j : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (j : ℝ)
    have h2 := (Real.hasDerivAt_sin ((j : ℝ) * t)).comp t h1
    simpa [Function.comp_def, mul_div_assoc, div_self hj0] using h2.div_const (j : ℝ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => Real.cos ((j : ℝ) * t)).intervalIntegrable _ _)]
  simp [mul_neg, Real.sin_nat_mul_pi]

/-- `∫_{-π}^{0} sin (j t) dt = ((-1)^j - 1) / j` for `j ≥ 1`. -/
private theorem integral_sin_neg_pi_zero {j : ℕ} (hj : 0 < j) :
    (∫ t in -π..(0 : ℝ), Real.sin ((j : ℝ) * t)) = ((-1 : ℝ) ^ j - 1) / j := by
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hd : ∀ t ∈ Set.uIcc (-π) (0 : ℝ),
      HasDerivAt (fun s : ℝ => -(Real.cos ((j : ℝ) * s) / j)) (Real.sin ((j : ℝ) * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (j : ℝ) * s) (j : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (j : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => Real.cos ((j : ℝ) * s))
        (-Real.sin ((j : ℝ) * t) * (j : ℝ)) t :=
      (Real.hasDerivAt_cos ((j : ℝ) * t)).comp t h1
    have h3 := (h2.div_const (j : ℝ)).neg
    have hv : -(-Real.sin ((j : ℝ) * t) * (j : ℝ) / (j : ℝ)) = Real.sin ((j : ℝ) * t) := by
      field_simp
    rwa [hv] at h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => Real.sin ((j : ℝ) * t)).intervalIntegrable _ _)]
  rw [mul_zero, Real.cos_zero, show (j : ℝ) * -π = -((j : ℝ) * π) by ring, Real.cos_neg,
    Real.cos_nat_mul_pi]
  field_simp
  ring

/-- Convergence of the Fourier partial sums at every point of one period carries to all of `ℝ`:
both `f` and the partial sums are `2 π`-periodic. -/
private theorem tendsto_fourierPartialSum_of_Ico {f : ℝ → ℝ}
    (hper : Function.Periodic f (2 * π))
    (h : ∀ y ∈ Set.Ico (-π) π, Tendsto (fun n : ℕ => fourierPartialSum f n y) atTop (𝓝 (f y)))
    (x : ℝ) : Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) := by
  obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico x
  rw [← hper.sub_int_mul_eq (x := x) k]
  exact (h _ hk).congr fun n => (fourierPartialSum_periodic f n).sub_int_mul_eq k

/-- A quotient with an explicit form just to the right of `0` has the corresponding limit there:
the shape in which the one-sided derivative hypotheses of Theorem 4.1.1 are met. -/
private theorem tendsto_quotient_of_eventually_eq {g q : ℝ → ℝ} {c d : ℝ}
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) π, (g t - c) / t = q t) (hq : Tendsto q (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun t : ℝ => (g t - c) / t) (𝓝[>] 0) (𝓝 d) := by
  refine hq.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with t ht
  exact (h t ht).symm

/-- The special case of `tendsto_quotient_of_eventually_eq` with a constant quotient. -/
private theorem tendsto_quotient_of_eventually_const {g : ℝ → ℝ} {c d : ℝ}
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) π, (g t - c) / t = d) :
    Tendsto (fun t : ℝ => (g t - c) / t) (𝓝[>] 0) (𝓝 d) :=
  tendsto_quotient_of_eventually_eq h tendsto_const_nhds

/-- A function agreeing on `[-π, π]` with a continuous one is interval-integrable there. -/
private theorem intervalIntegrable_of_eqOn {f F : ℝ → ℝ} (hF : Continuous F)
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = F x) : IntervalIntegrable f volume (-π) π := by
  refine (hF.intervalIntegrable _ _).congr fun t ht => ?_
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos]), Set.mem_Ioc] at ht
  exact (hval t ⟨ht.1.le, ht.2⟩).symm

/-- A function agreeing on `[-π, π]` with another has the same integrals against any weight. -/
private theorem integral_congr_of_eqOn {f F : ℝ → ℝ}
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = F x) (g : ℝ → ℝ) :
    (∫ t in -π..π, f t * g t) = ∫ t in -π..π, F t * g t := by
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
  rw [hval t ht]

/-! #### Example 4.1.3: a step function -/

/-- Against a continuous weight only the left half of the period contributes to the integral of the
step function of Example 4.1.3, on which the function is `1`. -/
private theorem step_integral {f : ℝ → ℝ} (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1)
    (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) {g : ℝ → ℝ} (hg : Continuous g) :
    IntervalIntegrable (fun t => f t * g t) volume (-π) π ∧
      (∫ t in -π..π, f t * g t) = ∫ t in -π..(0 : ℝ), g t := by
  have hπ := Real.pi_pos
  have h1 : Set.EqOn g (fun t => f t * g t) (Set.uIoo (-π) 0) := by
    intro t ht
    rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at ht
    simp [hneg t ⟨ht.1.le, ht.2⟩]
  have h2 : Set.EqOn (fun _ : ℝ => (0 : ℝ)) (fun t => f t * g t) (Set.uIoo 0 π) := by
    intro t ht
    rw [Set.uIoo_of_le hπ.le, Set.mem_Ioo] at ht
    simp [hpos t ⟨ht.1.le, ht.2⟩]
  have hi1 : IntervalIntegrable (fun t => f t * g t) volume (-π) 0 :=
    (hg.intervalIntegrable _ _).congr_uIoo h1
  have hi2 : IntervalIntegrable (fun t => f t * g t) volume 0 π :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo h2
  refine ⟨hi1.trans hi2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    ← intervalIntegral.integral_congr_uIoo h1, ← intervalIntegral.integral_congr_uIoo h2]
  simp

/-- The step function of Example 4.1.3 is interval-integrable over a period. -/
private theorem step_intervalIntegrable {f : ℝ → ℝ} (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1)
    (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) : IntervalIntegrable f volume (-π) π := by
  simpa using (step_integral hneg hpos (g := fun _ => (1 : ℝ)) continuous_const).1

/-- The cosine coefficients of the step function: `a_0 = 1` and `a_j = 0` for `j ≥ 1`. -/
private theorem step_fourierCoeffCos {f : ℝ → ℝ} (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1)
    (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) :
    fourierCoeffCos f 0 = 1 ∧ ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  constructor
  · have hval : (∫ t in -π..(0 : ℝ), Real.cos (((0 : ℕ) : ℝ) * t)) = π := by simp
    rw [fourierCoeffCos, (step_integral hneg hpos (g := fun t => Real.cos (((0 : ℕ) : ℝ) * t))
      (by fun_prop)).2, hval]
    field_simp
  · intro j hj
    rw [fourierCoeffCos, (step_integral hneg hpos (g := fun t => Real.cos ((j : ℝ) * t))
      (by fun_prop)).2, integral_cos_neg_pi_zero hj, mul_zero]

/-- The sine coefficients of the step function: `b_j = -(1 - (-1)^j) / (π j)` for `j ≥ 1`. -/
private theorem step_fourierCoeffSin {f : ℝ → ℝ} (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1)
    (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) (j : ℕ) (hj : 0 < j) :
    fourierCoeffSin f j = -(1 - (-1 : ℝ) ^ j) / (π * j) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  rw [fourierCoeffSin, (step_integral hneg hpos (g := fun t => Real.sin ((j : ℝ) * t))
    (by fun_prop)).2, integral_sin_neg_pi_zero hj]
  field_simp
  ring

/-- The partial sums of the step function's Fourier series in the book's closed form,
`S_n x = 1/2 - (2/π) ∑_{i < n} sin ((2 i + 1) x) / (2 i + 1)`, the even-indexed coefficients
being zero. -/
private theorem step_fourierPartialSum {f : ℝ → ℝ} (hcos0 : fourierCoeffCos f 0 = 1)
    (hcos : ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 0)
    (hsin : ∀ j : ℕ, 0 < j → fourierCoeffSin f j = -(1 - (-1 : ℝ) ^ j) / (π * j)) (n : ℕ)
    (x : ℝ) :
    fourierPartialSum f (2 * n) x
      = 1 / 2 - 2 / π * ∑ i ∈ Finset.range n, Real.sin ((2 * i + 1) * x) / (2 * i + 1) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  induction n with
  | zero => simp [fourierPartialSum, hcos0]
  | succ n ih =>
      have hstep : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      have hodd : ((-1 : ℝ)) ^ (2 * n + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      have heven : ((-1 : ℝ)) ^ (2 * n + 1 + 1) = 1 := by
        rw [pow_succ, hodd]; norm_num
      have hne : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      rw [hstep, fourierPartialSum_succ, fourierPartialSum_succ, ih, Finset.sum_range_succ,
        hcos (2 * n + 1) (by omega), hcos (2 * n + 1 + 1) (by omega),
        hsin (2 * n + 1) (by omega), hsin (2 * n + 1 + 1) (by omega), hodd, heven]
      set S := ∑ i ∈ Finset.range n, Real.sin ((2 * (i : ℝ) + 1) * x) / (2 * (i : ℝ) + 1) with hS
      simp only [sub_self, neg_zero, zero_div, zero_mul, add_zero, zero_add]
      push_cast
      field_simp
      ring

/-- The step function is constant on a neighbourhood of any point that is not a multiple of `π`,
hence differentiable there with derivative `0`. -/
private theorem step_hasDerivAt {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1) (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) {x : ℝ}
    (hx : ∀ k : ℤ, x ≠ k * π) : HasDerivAt f 0 x := by
  have hπ := Real.pi_pos
  obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico x
  have hval : ∀ t : ℝ, f t = f (t - k * (2 * π)) := fun t =>
    (hper.sub_int_mul_eq (x := t) k).symm
  have hy0 : x - k * (2 * π) ≠ 0 := fun h => hx (2 * k) (by push_cast; linarith)
  have hyπ : -π < x - k * (2 * π) :=
    lt_of_le_of_ne hk.1 fun h => hx (2 * k - 1) (by push_cast; linarith)
  rcases lt_or_gt_of_ne hy0 with hlt | hgt
  · have hnb : ∀ᶠ t in 𝓝 x, f t = 1 := by
      have hopen : Set.Ioo (-π + k * (2 * π)) (0 + k * (2 * π)) ∈ 𝓝 x :=
        isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
      filter_upwards [hopen] with t ht
      exact (hval t).trans (hneg _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq hnb
  · have hnb : ∀ᶠ t in 𝓝 x, f t = 0 := by
      have hopen : Set.Ioo (0 + k * (2 * π)) (π + k * (2 * π)) ∈ 𝓝 x :=
        isOpen_Ioo.mem_nhds ⟨by linarith, by linarith [hk.2]⟩
      filter_upwards [hopen] with t ht
      exact (hval t).trans (hpos _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hnb

/-- At a multiple of `π` the step function of Example 4.1.3 jumps between `0` and `1`, so its
Fourier partial sums converge to the mean `1/2` of the one-sided limits. -/
private theorem step_tendsto_at_pi {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1) (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) (k : ℤ) :
    Tendsto (fun n : ℕ => fourierPartialSum f n ((k : ℝ) * π)) atTop (𝓝 (1 / 2)) := by
  have hπ := Real.pi_pos
  have hval : ∀ (t : ℝ) (m : ℤ), f t = f (t - m * (2 * π)) := fun t m =>
    (hper.sub_int_mul_eq (x := t) m).symm
  obtain ⟨fL, fR, hLval, hRval, hmean⟩ :
      ∃ fL fR : ℝ, (∀ t ∈ Set.Ioo (0 : ℝ) π, f ((k : ℝ) * π - t) = fL) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) π, f ((k : ℝ) * π + t) = fR) ∧ (fL + fR) / 2 = 1 / 2 := by
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      refine ⟨1, 0, fun t ht => ?_, fun t ht => ?_, by norm_num⟩
      · rw [hval _ m]
        refine hneg _ ⟨?_, ?_⟩ <;> push_cast <;> linarith [ht.1, ht.2]
      · rw [hval _ m]
        refine hpos _ ⟨?_, ?_⟩ <;> push_cast <;> linarith [ht.1, ht.2]
    · subst hm
      refine ⟨0, 1, fun t ht => ?_, fun t ht => ?_, by norm_num⟩
      · rw [hval _ m]
        refine hpos _ ⟨?_, ?_⟩ <;> push_cast <;> linarith [ht.1, ht.2]
      · rw [hval _ (m + 1)]
        refine hneg _ ⟨?_, ?_⟩ <;> push_cast <;> linarith [ht.1, ht.2]
  rw [← hmean]
  exact theorem_4_1_1 hper (step_intervalIntegrable hneg hpos)
    (tendsto_quotient_of_eventually_const (d := 0)
      fun t ht => by rw [hRval t ht, sub_self, zero_div])
    (tendsto_quotient_of_eventually_const (d := 0)
      fun t ht => by rw [hLval t ht, sub_self, zero_div])

/-- **Example 4.1.3.** The Fourier series of the step function `f x = 1` on `[-π, 0)` and
`f x = 0` on `[0, π)`, extended `2 π`-periodically. Its coefficients are `a_0 = 1`, `a_j = 0` for
`j ≥ 1` and `b_j = -(1 - (-1)^j) / (π j)`, so the even harmonics drop out and the partial sums are
the book's

`S_n x = 1/2 - (2/π) ∑_{i < n} sin ((2 i + 1) x) / (2 i + 1)`

(the book indexes the sum from `j = 1` to `n` with terms `sin ((2 j - 1) x) / (2 j - 1)`, which is
the same series reindexed). By Theorem 4.1.1 the Fourier series converges to `f x` at every `x`
that is not a multiple of `π`, and to `1/2` at every multiple of `π`, the mean of the two one-sided
limits at the jump; the last clause is the book's `F x = f x`, written as convergence of the series
`∑_{i ≥ 0} -(2/π) sin ((2 i + 1) x) / (2 i + 1)` to `f x - 1/2` in the sense of Definition 1.2.17.

Not stated: the Gibbs phenomenon that the book discusses beside this example, whose overshoot span
`(2/π) Si(π) |f (x+) - f (x-)|` with `(2/π) Si(π) ≈ 1.17898` it asserts without proof and refers
out. Beware the near-match: `equation_4_1_3_const`, `equation_4_1_3_cos` and `equation_4_1_3_sin`
are the book's *displayed* equations (4.1.3), the real Fourier coefficients, and have nothing to do
with this example. -/
theorem example_4_1_3 {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1) (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) :
    fourierCoeffCos f 0 = 1 ∧
      (∀ j : ℕ, 0 < j → fourierCoeffCos f j = 0) ∧
      (∀ j : ℕ, 0 < j → fourierCoeffSin f j = -(1 - (-1 : ℝ) ^ j) / (π * j)) ∧
      (∀ (n : ℕ) (x : ℝ), fourierPartialSum f (2 * n) x
        = 1 / 2 - 2 / π * ∑ i ∈ Finset.range n, Real.sin ((2 * i + 1) * x) / (2 * i + 1)) ∧
      (∀ x : ℝ, (∀ k : ℤ, x ≠ (k : ℝ) * π) →
        Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x))) ∧
      (∀ k : ℤ, Tendsto (fun n : ℕ => fourierPartialSum f n ((k : ℝ) * π)) atTop (𝓝 (1 / 2))) ∧
      ∀ x : ℝ, (∀ k : ℤ, x ≠ (k : ℝ) * π) →
        Chapter01.definition_1_2_17
          (fun i : ℕ => -(2 / π) * (Real.sin ((2 * i + 1) * x) / (2 * i + 1))) (f x - 1 / 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨hcos0, hcos⟩ := step_fourierCoeffCos hneg hpos
  have hsin := step_fourierCoeffSin hneg hpos
  have hpartial := step_fourierPartialSum hcos0 hcos hsin
  have hconv : ∀ x : ℝ, (∀ k : ℤ, x ≠ (k : ℝ) * π) →
      Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) := fun x hx =>
    theorem_4_1_1_continuous hper (step_intervalIntegrable hneg hpos)
      (step_hasDerivAt hper hneg hpos hx)
  refine ⟨hcos0, hcos, hsin, hpartial, hconv, step_tendsto_at_pi hper hneg hpos, fun x hx => ?_⟩
  have hdouble : Tendsto (fun n : ℕ => fourierPartialSum f (2 * n) x) atTop (𝓝 (f x)) :=
    (hconv x hx).comp (Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have hclosed : Tendsto (fun n : ℕ =>
      1 / 2 - 2 / π * ∑ i ∈ Finset.range n, Real.sin ((2 * i + 1) * x) / (2 * i + 1)) atTop
      (𝓝 (f x)) := hdouble.congr fun n => hpartial n x
  refine (Chapter01.definition_1_2_17_iff _ _).mpr ((hclosed.sub_const (1 / 2)).congr fun n => ?_)
  rw [← Finset.mul_sum]
  ring

/-! #### Example 4.1.4: `|x| / π` -/

/-- `∫_0^π t cos (j t) dt = ((-1)^j - 1) / j²` for `j ≥ 1`, by parts. -/
private theorem integral_mul_cos_zero_pi {j : ℕ} (hj : 0 < j) :
    (∫ t in (0 : ℝ)..π, t * Real.cos ((j : ℝ) * t)) = ((-1 : ℝ) ^ j - 1) / j ^ 2 := by
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) π,
      HasDerivAt (fun s : ℝ => s * Real.sin ((j : ℝ) * s) / j + Real.cos ((j : ℝ) * s) / j ^ 2)
        (t * Real.cos ((j : ℝ) * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (j : ℝ) * s) (j : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (j : ℝ)
    have hs : HasDerivAt (fun s : ℝ => Real.sin ((j : ℝ) * s))
        (Real.cos ((j : ℝ) * t) * (j : ℝ)) t := (Real.hasDerivAt_sin _).comp t h1
    have hc : HasDerivAt (fun s : ℝ => Real.cos ((j : ℝ) * s))
        (-Real.sin ((j : ℝ) * t) * (j : ℝ)) t := (Real.hasDerivAt_cos _).comp t h1
    have h2 : HasDerivAt (fun s : ℝ => s * Real.sin ((j : ℝ) * s) / j
          + Real.cos ((j : ℝ) * s) / j ^ 2)
        ((1 * Real.sin ((j : ℝ) * t) + t * (Real.cos ((j : ℝ) * t) * (j : ℝ))) / (j : ℝ)
          + -Real.sin ((j : ℝ) * t) * (j : ℝ) / (j : ℝ) ^ 2) t :=
      (((hasDerivAt_id t).mul hs).div_const (j : ℝ)).add (hc.div_const ((j : ℝ) ^ 2))
    have hv : (1 * Real.sin ((j : ℝ) * t) + t * (Real.cos ((j : ℝ) * t) * (j : ℝ))) / (j : ℝ)
          + -Real.sin ((j : ℝ) * t) * (j : ℝ) / (j : ℝ) ^ 2 = t * Real.cos ((j : ℝ) * t) := by
      field_simp
      ring
    rwa [hv] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => t * Real.cos ((j : ℝ) * t)).intervalIntegrable _ _),
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, zero_add]
  rw [div_sub_div_same]

/-- The Fourier coefficients of `|x| / π`: the sines vanish because the function is even, and
`a_0 = 1`, `a_j = 2 ((-1)^j - 1) / (π² j²)`. -/
private theorem abs_fourierCoeff {f : ℝ → ℝ} (hval : ∀ x ∈ Set.Icc (-π) π, f x = |x| / π) :
    (∀ j : ℕ, fourierCoeffSin f j = 0) ∧ fourierCoeffCos f 0 = 1 ∧
      ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 2 * ((-1 : ℝ) ^ j - 1) / (π ^ 2 * j ^ 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hπ0 := Real.pi_pos
  refine ⟨fun j => ?_, ?_, fun j hj => ?_⟩
  · rw [fourierCoeffSin, integral_congr_of_eqOn hval _,
      intervalIntegral_of_odd (g := fun t => |t| / π * Real.sin ((j : ℝ) * t))
        (fun t => by rw [abs_neg, mul_neg, Real.sin_neg]; ring)
        ((by fun_prop : Continuous fun t : ℝ =>
          |t| / π * Real.sin ((j : ℝ) * t)).intervalIntegrable _ _), mul_zero]
  · have hEq : ∀ t ∈ Set.uIcc (0 : ℝ) π, |t| / π = t / π := by
      intro t ht
      rw [Set.uIcc_of_le hπ0.le, Set.mem_Icc] at ht
      rw [abs_of_nonneg ht.1]
    have heven : (∫ t in -π..π, |t| / π * Real.cos (((0 : ℕ) : ℝ) * t))
        = 2 * ∫ t in (0 : ℝ)..π, |t| / π * Real.cos (((0 : ℕ) : ℝ) * t) :=
      intervalIntegral_of_even (fun t => by rw [abs_neg, mul_neg, Real.cos_neg])
        ((by fun_prop : Continuous fun t : ℝ =>
          |t| / π * Real.cos (((0 : ℕ) : ℝ) * t)).intervalIntegrable _ _)
    rw [fourierCoeffCos, integral_congr_of_eqOn hval _, heven]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_div, integral_id]
    field_simp
    ring
  · have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
    have hEq : ∀ t ∈ Set.uIcc (0 : ℝ) π,
        |t| / π * Real.cos ((j : ℝ) * t) = t * Real.cos ((j : ℝ) * t) / π := by
      intro t ht
      rw [Set.uIcc_of_le hπ0.le, Set.mem_Icc] at ht
      rw [abs_of_nonneg ht.1]
      ring
    have heven : (∫ t in -π..π, |t| / π * Real.cos ((j : ℝ) * t))
        = 2 * ∫ t in (0 : ℝ)..π, |t| / π * Real.cos ((j : ℝ) * t) :=
      intervalIntegral_of_even (fun t => by rw [abs_neg, mul_neg, Real.cos_neg])
        ((by fun_prop : Continuous fun t : ℝ =>
          |t| / π * Real.cos ((j : ℝ) * t)).intervalIntegrable _ _)
    rw [fourierCoeffCos, integral_congr_of_eqOn hval _, heven,
      intervalIntegral.integral_congr hEq, intervalIntegral.integral_div,
      integral_mul_cos_zero_pi hj]
    field_simp

/-- The partial sums of the Fourier series of `|x| / π` in the book's closed form,
`S_n x = 1/2 - (4/π²) ∑_{i < n} cos ((2 i + 1) x) / (2 i + 1)²`. -/
private theorem abs_fourierPartialSum {f : ℝ → ℝ} (hsin : ∀ j : ℕ, fourierCoeffSin f j = 0)
    (hcos0 : fourierCoeffCos f 0 = 1)
    (hcos : ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 2 * ((-1 : ℝ) ^ j - 1) / (π ^ 2 * j ^ 2))
    (n : ℕ) (x : ℝ) :
    fourierPartialSum f (2 * n) x
      = 1 / 2 - 4 / π ^ 2 * ∑ i ∈ Finset.range n,
          Real.cos ((2 * i + 1) * x) / (2 * i + 1) ^ 2 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  induction n with
  | zero => simp [fourierPartialSum, hcos0]
  | succ n ih =>
      have hstep : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      have hodd : ((-1 : ℝ)) ^ (2 * n + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      have heven : ((-1 : ℝ)) ^ (2 * n + 1 + 1) = 1 := by
        rw [pow_succ, hodd]; norm_num
      have hne : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      rw [hstep, fourierPartialSum_succ, fourierPartialSum_succ, ih, Finset.sum_range_succ,
        hcos (2 * n + 1) (by omega), hcos (2 * n + 1 + 1) (by omega), hsin (2 * n + 1),
        hsin (2 * n + 1 + 1), hodd, heven]
      set S := ∑ i ∈ Finset.range n, Real.cos ((2 * (i : ℝ) + 1) * x) / (2 * (i : ℝ) + 1) ^ 2
        with hS
      simp only [sub_self, mul_zero, zero_div, zero_mul, add_zero]
      push_cast
      field_simp
      ring

/-- The Fourier series of `|x| / π` converges to the function at every real point: the periodic
extension is continuous, differentiable off the multiples of `π`, and has equal one-sided
difference quotients at the corners `x = 0` and `x = ±π`, so Theorem 4.1.1 applies everywhere. -/
private theorem abs_tendsto {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = |x| / π) (x : ℝ) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) := by
  have hπ := Real.pi_pos
  have hπ' : π ≠ 0 := Real.pi_ne_zero
  have hfi := intervalIntegrable_of_eqOn (F := fun x : ℝ => |x| / π) (by fun_prop) hval
  refine tendsto_fourierPartialSum_of_Ico hper (fun y hy => ?_) x
  rcases eq_or_lt_of_le hy.1 with hyl | hyl
  · -- `y = -π`: the peak of the periodic extension
    subst hyl
    have hfy : f (-π) = 1 := by
      rw [hval _ ⟨le_rfl, by linarith⟩, abs_neg, abs_of_pos hπ]
      field_simp
    have hR : ∀ t ∈ Set.Ioo (0 : ℝ) π, (f (-π + t) - 1) / t = -(1 / π) := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [hval _ ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        abs_of_nonpos (by linarith [ht.2] : -π + t ≤ 0)]
      field_simp
      ring
    have hL : ∀ t ∈ Set.Ioo (0 : ℝ) π, (f (-π - t) - 1) / t = -(1 / π) := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [← hper.sub_int_mul_eq (x := -π - t) (-1),
        hval _ ⟨by push_cast; linarith [ht.2], by push_cast; linarith [ht.1]⟩,
        abs_of_nonneg (by push_cast; linarith [ht.2] :
          (0 : ℝ) ≤ -π - t - ((-1 : ℤ) : ℝ) * (2 * π))]
      push_cast
      field_simp
      ring
    have hconv := theorem_4_1_1 hper hfi (tendsto_quotient_of_eventually_const hR)
      (tendsto_quotient_of_eventually_const hL)
    rw [hfy]
    rwa [show ((1 : ℝ) + 1) / 2 = 1 by norm_num] at hconv
  rcases lt_trichotomy y 0 with hlt | heq | hgt
  · -- `y ∈ (-π, 0)`: the extension is `-y/π` near `y`
    have hnb : ∀ᶠ t in 𝓝 y, f t = -t / π := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨hyl, hlt⟩ : y ∈ Set.Ioo (-π) 0)] with t ht
      rw [hval t ⟨ht.1.le, by linarith [ht.2]⟩, abs_of_neg ht.2]
    have hderiv : HasDerivAt (fun t : ℝ => -t / π) (-1 / π) y :=
      ((hasDerivAt_id y).neg).div_const π
    exact theorem_4_1_1_continuous hper hfi (hderiv.congr_of_eventuallyEq hnb)
  · -- `y = 0`: the corner at the bottom
    subst heq
    have hfy : f 0 = 0 := by rw [hval _ ⟨by linarith, by linarith⟩]; simp
    have hR : ∀ t ∈ Set.Ioo (0 : ℝ) π, (f (0 + t) - 0) / t = 1 / π := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [zero_add, hval _ ⟨by linarith [ht.1], ht.2.le⟩, abs_of_pos ht.1]
      field_simp
      ring
    have hL : ∀ t ∈ Set.Ioo (0 : ℝ) π, (f (0 - t) - 0) / t = 1 / π := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [zero_sub, hval _ ⟨by linarith [ht.2], by linarith [ht.1]⟩, abs_neg, abs_of_pos ht.1]
      field_simp
      ring
    have hconv := theorem_4_1_1 hper hfi (tendsto_quotient_of_eventually_const hR)
      (tendsto_quotient_of_eventually_const hL)
    rw [hfy]
    rwa [show ((0 : ℝ) + 0) / 2 = 0 by norm_num] at hconv
  · -- `y ∈ (0, π)`: the extension is `y/π` near `y`
    have hnb : ∀ᶠ t in 𝓝 y, f t = t / π := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨hgt, hy.2⟩ : y ∈ Set.Ioo 0 π)] with t ht
      rw [hval t ⟨by linarith [ht.1], ht.2.le⟩, abs_of_pos ht.1]
    have hderiv : HasDerivAt (fun t : ℝ => t / π) (1 / π) y := (hasDerivAt_id y).div_const π
    exact theorem_4_1_1_continuous hper hfi (hderiv.congr_of_eventuallyEq hnb)

/-- **Example 4.1.4.** The Fourier series of `f x = |x| / π` on `[-π, π]`, extended
`2 π`-periodically — the extension is continuous because `f (-π) = f π`. The function is even, so
its series carries no sine term; the cosine coefficients are `a_0 = 1` and
`a_j = 2 ((-1)^j - 1) / (π² j²)`, which vanish for even `j`, so the partial sums are the book's

`S_n x = 1/2 - (4/π²) ∑_{i < n} cos ((2 i + 1) x) / (2 i + 1)²`

(the book indexes the sum from `j = 1` to `n` with terms `cos ((2 j - 1) x) / (2 j - 1)²`, the same
series reindexed). The extension is differentiable off the multiples of `π` and has equal one-sided
difference quotients at the corners, so by Theorem 4.1.1 the series converges to `f x` at every
`x`; the last clause is the book's `F x = f x`, written as convergence of the series
`∑_{i ≥ 0} -(4/π²) cos ((2 i + 1) x) / (2 i + 1)²` to `f x - 1/2` in the sense of Definition
1.2.17. The book's other assertion here, convergence in `L²(-π, π)`, is `equation_4_1_14` for this
`f`. -/
theorem example_4_1_4 {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = |x| / π) :
    (∀ j : ℕ, fourierCoeffSin f j = 0) ∧
      fourierCoeffCos f 0 = 1 ∧
      (∀ j : ℕ, 0 < j → fourierCoeffCos f j = 2 * ((-1 : ℝ) ^ j - 1) / (π ^ 2 * j ^ 2)) ∧
      (∀ (n : ℕ) (x : ℝ), fourierPartialSum f (2 * n) x
        = 1 / 2 - 4 / π ^ 2 * ∑ i ∈ Finset.range n,
            Real.cos ((2 * i + 1) * x) / (2 * i + 1) ^ 2) ∧
      (∀ x : ℝ, Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x))) ∧
      ∀ x : ℝ, Chapter01.definition_1_2_17
        (fun i : ℕ => -(4 / π ^ 2) * (Real.cos ((2 * i + 1) * x) / (2 * i + 1) ^ 2))
        (f x - 1 / 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨hsin, hcos0, hcos⟩ := abs_fourierCoeff hval
  have hpartial := abs_fourierPartialSum hsin hcos0 hcos
  have hconv := abs_tendsto hper hval
  refine ⟨hsin, hcos0, hcos, hpartial, hconv, fun x => ?_⟩
  have hdouble : Tendsto (fun n : ℕ => fourierPartialSum f (2 * n) x) atTop (𝓝 (f x)) :=
    (hconv x).comp (Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have hclosed : Tendsto (fun n : ℕ => 1 / 2 - 4 / π ^ 2 * ∑ i ∈ Finset.range n,
      Real.cos ((2 * i + 1) * x) / (2 * i + 1) ^ 2) atTop (𝓝 (f x)) :=
    hdouble.congr fun n => hpartial n x
  refine (Chapter01.definition_1_2_17_iff _ _).mpr ((hclosed.sub_const (1 / 2)).congr fun n => ?_)
  rw [← Finset.mul_sum]
  ring

/-! #### Example 4.1.5: `(π² - x²)² / π⁴` -/

/-- The derivative of `P s * sin (w s)`, the shape the antiderivative below is built from. -/
private theorem hasDerivAt_mul_sin {P : ℝ → ℝ} {c w t : ℝ} (hP : HasDerivAt P c t) :
    HasDerivAt (fun s => P s * Real.sin (w * s))
      (c * Real.sin (w * t) + P t * (Real.cos (w * t) * w)) t :=
  hP.mul ((Real.hasDerivAt_sin (w * t)).comp t (by simpa using (hasDerivAt_id t).const_mul w))

/-- The derivative of `P s * cos (w s)`. -/
private theorem hasDerivAt_mul_cos {P : ℝ → ℝ} {c w t : ℝ} (hP : HasDerivAt P c t) :
    HasDerivAt (fun s => P s * Real.cos (w * s))
      (c * Real.cos (w * t) + P t * (-Real.sin (w * t) * w)) t :=
  hP.mul ((Real.hasDerivAt_cos (w * t)).comp t (by simpa using (hasDerivAt_id t).const_mul w))

/-- The derivative of a general quintic. -/
private theorem hasDerivAt_quintic (a b c d e g t : ℝ) :
    HasDerivAt (fun s : ℝ => a * s ^ 5 + b * s ^ 4 + c * s ^ 3 + d * s ^ 2 + e * s + g)
      (5 * a * t ^ 4 + 4 * b * t ^ 3 + 3 * c * t ^ 2 + 2 * d * t + e) t := by
  refine HasDerivAt.congr_deriv
    (((((((hasDerivAt_pow 5 t).const_mul a).add ((hasDerivAt_pow 4 t).const_mul b)).add
      ((hasDerivAt_pow 3 t).const_mul c)).add ((hasDerivAt_pow 2 t).const_mul d)).add
      ((hasDerivAt_id t).const_mul e)).add_const g) ?_
  push_cast
  ring

/-- The derivative of `(π² - x²)² / π⁴`. -/
private theorem hasDerivAt_quarticNorm (y : ℝ) :
    HasDerivAt (fun t : ℝ => (π ^ 2 - t ^ 2) ^ 2 / π ^ 4)
      ((4 * y ^ 3 - 4 * π ^ 2 * y) / π ^ 4) y := by
  refine HasDerivAt.congr_deriv
    ((((hasDerivAt_pow 2 y).const_sub (π ^ 2)).pow 2).div_const (π ^ 4)) ?_
  push_cast
  ring

/-- The second derivative of `(π² - x²)² / π⁴`. -/
private theorem hasDerivAt_quarticNorm' (y : ℝ) :
    HasDerivAt (fun t : ℝ => (4 * t ^ 3 - 4 * π ^ 2 * t) / π ^ 4)
      ((12 * y ^ 2 - 4 * π ^ 2) / π ^ 4) y := by
  refine HasDerivAt.congr_deriv
    ((((hasDerivAt_pow 3 y).const_mul (4 : ℝ)).sub
      ((hasDerivAt_id y).const_mul (4 * π ^ 2))).div_const (π ^ 4)) ?_
  push_cast
  ring

/-- `∫_{-π}^{π} (π² - t²)² dt = 16 π⁵ / 15`. -/
private theorem integral_quartic : (∫ t in -π..π, (π ^ 2 - t ^ 2) ^ 2) = 16 * π ^ 5 / 15 := by
  have hd : ∀ t ∈ Set.uIcc (-π) π,
      HasDerivAt (fun s : ℝ => (1 / 5) * s ^ 5 + 0 * s ^ 4 + (-(2 * π ^ 2) / 3) * s ^ 3
          + 0 * s ^ 2 + π ^ 4 * s + 0)
        ((π ^ 2 - t ^ 2) ^ 2) t := fun t _ =>
    (hasDerivAt_quintic (1 / 5) 0 (-(2 * π ^ 2) / 3) 0 (π ^ 4) 0 t).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => (π ^ 2 - t ^ 2) ^ 2).intervalIntegrable _ _)]
  ring

/-- `∫_{-π}^{π} (π² - t²)² cos (j t) dt = -48 π (-1)^j / j⁴` for `j ≥ 1`: four integrations by
parts, packaged as the antiderivative `(R s sin (j s) + T s cos (j s)) / j⁵` with `R` and `T` the
polynomials `j⁴ p - j² p'' + p''''` and `j³ p' - j p'''` of `p s = (π² - s²)²`. -/
private theorem integral_quartic_mul_cos {j : ℕ} (hj : 0 < j) :
    (∫ t in -π..π, (π ^ 2 - t ^ 2) ^ 2 * Real.cos ((j : ℝ) * t))
      = -48 * π * (-1 : ℝ) ^ j / j ^ 4 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hd : ∀ t ∈ Set.uIcc (-π) π,
      HasDerivAt (fun s : ℝ =>
          ((0 * s ^ 5 + (j : ℝ) ^ 4 * s ^ 4 + 0 * s ^ 3
                + (-(2 * π ^ 2 * (j : ℝ) ^ 4) - 12 * (j : ℝ) ^ 2) * s ^ 2 + 0 * s
                + (π ^ 4 * (j : ℝ) ^ 4 + 4 * π ^ 2 * (j : ℝ) ^ 2 + 24)) * Real.sin ((j : ℝ) * s)
            + (0 * s ^ 5 + 0 * s ^ 4 + 4 * (j : ℝ) ^ 3 * s ^ 3 + 0 * s ^ 2
                + (-(4 * π ^ 2 * (j : ℝ) ^ 3) - 24 * (j : ℝ)) * s + 0) * Real.cos ((j : ℝ) * s))
          / (j : ℝ) ^ 5)
        ((π ^ 2 - t ^ 2) ^ 2 * Real.cos ((j : ℝ) * t)) t := by
    intro t _
    refine HasDerivAt.congr_deriv
      (((hasDerivAt_mul_sin (hasDerivAt_quintic 0 ((j : ℝ) ^ 4) 0
            (-(2 * π ^ 2 * (j : ℝ) ^ 4) - 12 * (j : ℝ) ^ 2) 0
            (π ^ 4 * (j : ℝ) ^ 4 + 4 * π ^ 2 * (j : ℝ) ^ 2 + 24) t)).add
        (hasDerivAt_mul_cos (hasDerivAt_quintic 0 0 (4 * (j : ℝ) ^ 3) 0
            (-(4 * π ^ 2 * (j : ℝ) ^ 3) - 24 * (j : ℝ)) 0 t))).div_const ((j : ℝ) ^ 5)) ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ =>
      (π ^ 2 - t ^ 2) ^ 2 * Real.cos ((j : ℝ) * t)).intervalIntegrable _ _),
    show ((j : ℝ)) * -π = -((j : ℝ) * π) by ring, Real.sin_neg, Real.cos_neg,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  field_simp
  ring

/-- The Fourier coefficients of `(π² - x²)² / π⁴`: the sines vanish because the function is even,
and `a_0 = 16/15`, `a_j = 48 (-1)^{j+1} / (π⁴ j⁴)`. -/
private theorem quartic_fourierCoeff {f : ℝ → ℝ}
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) :
    (∀ j : ℕ, fourierCoeffSin f j = 0) ∧ fourierCoeffCos f 0 = 16 / 15 ∧
      ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 48 * (-1 : ℝ) ^ (j + 1) / (π ^ 4 * j ^ 4) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine ⟨fun j => ?_, ?_, fun j hj => ?_⟩
  · rw [fourierCoeffSin, integral_congr_of_eqOn hval _,
      intervalIntegral_of_odd (g := fun t => (π ^ 2 - t ^ 2) ^ 2 / π ^ 4 * Real.sin ((j : ℝ) * t))
        (fun t => by rw [mul_neg, Real.sin_neg]; ring)
        ((by fun_prop : Continuous fun t : ℝ =>
          (π ^ 2 - t ^ 2) ^ 2 / π ^ 4 * Real.sin ((j : ℝ) * t)).intervalIntegrable _ _), mul_zero]
  · rw [fourierCoeffCos, integral_congr_of_eqOn hval _]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
    rw [intervalIntegral.integral_div, integral_quartic]
    field_simp
  · have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
    rw [fourierCoeffCos, integral_congr_of_eqOn hval _]
    simp only [div_mul_eq_mul_div]
    rw [intervalIntegral.integral_div, integral_quartic_mul_cos hj]
    field_simp
    ring

/-- The partial sums of the Fourier series of `(π² - x²)² / π⁴` in the book's closed form,
`S_n x = 8/15 + (48/π⁴) ∑_{i < n} (-1)^i cos ((i + 1) x) / (i + 1)⁴`. -/
private theorem quartic_fourierPartialSum {f : ℝ → ℝ} (hsin : ∀ j : ℕ, fourierCoeffSin f j = 0)
    (hcos0 : fourierCoeffCos f 0 = 16 / 15)
    (hcos : ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 48 * (-1 : ℝ) ^ (j + 1) / (π ^ 4 * j ^ 4))
    (n : ℕ) (x : ℝ) :
    fourierPartialSum f n x
      = 8 / 15 + 48 / π ^ 4 * ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * (Real.cos ((i + 1) * x) / (i + 1) ^ 4) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  induction n with
  | zero => simp [fourierPartialSum, hcos0]; norm_num
  | succ n ih =>
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      rw [fourierPartialSum_succ, ih, Finset.sum_range_succ, hcos (n + 1) (by omega),
        hsin (n + 1)]
      set S := ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (Real.cos (((i : ℝ) + 1) * x) / ((i : ℝ) + 1) ^ 4) with hS
      simp only [zero_mul, add_zero]
      push_cast
      field_simp
      ring

/-- The Fourier series of `(π² - x²)² / π⁴` converges to the function at every real point: the
periodic extension is continuously differentiable, being smooth on `(-π, π)` and having matching
one-sided difference quotients at `±π`, so Theorem 4.1.1 applies everywhere. -/
private theorem quartic_tendsto {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) (x : ℝ) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) := by
  have hπ := Real.pi_pos
  have hπ' : π ≠ 0 := Real.pi_ne_zero
  have hfi := intervalIntegrable_of_eqOn (F := fun x : ℝ => (π ^ 2 - x ^ 2) ^ 2 / π ^ 4)
    (by fun_prop) hval
  have hq : Tendsto (fun t : ℝ => t * (2 * π - t) ^ 2 / π ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => t * (2 * π - t) ^ 2 / π ^ 4 := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine tendsto_fourierPartialSum_of_Ico hper (fun y hy => ?_) x
  rcases eq_or_lt_of_le hy.1 with hyl | hyl
  · -- `y = -π`: the junction of the periodic extension
    subst hyl
    have hfy : f (-π) = 0 := by rw [hval _ ⟨le_rfl, by linarith⟩]; ring
    have hR : ∀ t ∈ Set.Ioo (0 : ℝ) π,
        (f (-π + t) - 0) / t = t * (2 * π - t) ^ 2 / π ^ 4 := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [hval _ ⟨by linarith [ht.1], by linarith [ht.2]⟩]
      field_simp
      ring
    have hL : ∀ t ∈ Set.Ioo (0 : ℝ) π,
        (f (-π - t) - 0) / t = t * (2 * π - t) ^ 2 / π ^ 4 := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [← hper.sub_int_mul_eq (x := -π - t) (-1),
        hval _ ⟨by push_cast; linarith [ht.2], by push_cast; linarith [ht.1]⟩]
      push_cast
      field_simp
      ring
    have hconv := theorem_4_1_1 hper hfi (tendsto_quotient_of_eventually_eq hR hq)
      (tendsto_quotient_of_eventually_eq hL hq)
    rw [hfy]
    rwa [show ((0 : ℝ) + 0) / 2 = 0 by norm_num] at hconv
  · -- `y ∈ (-π, π)`: the extension agrees with the polynomial near `y`
    have hnb : ∀ᶠ t in 𝓝 y, f t = (π ^ 2 - t ^ 2) ^ 2 / π ^ 4 := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨hyl, hy.2⟩ : y ∈ Set.Ioo (-π) π)] with t ht
      exact hval t ⟨ht.1.le, ht.2.le⟩
    exact theorem_4_1_1_continuous hper hfi
      ((hasDerivAt_quarticNorm y).congr_of_eventuallyEq hnb)

/-- **Example 4.1.5.** The Fourier series of `f x = (π² - x²)² / π⁴` on `[-π, π]`, extended
`2 π`-periodically. The endpoint conditions `f⁽ˡ⁾(-π) = f⁽ˡ⁾(π)` hold for `l = 0, 1, 2`, so the
extension is twice continuously differentiable; the function is even, so its series carries no sine
term, and `a_0 = 16/15`, `a_j = 48 (-1)^{j+1} / (π⁴ j⁴)`, giving the book's partial sums

`S_n x = 8/15 + (48/π⁴) ∑_{j = 1}^{n} (-1)^{j+1} cos (j x) / j⁴`

(written below over `i < n` with `j = i + 1`, so that `(-1)^{j+1}` is `(-1)^i`). The series
converges to `f x` at every `x` by Theorem 4.1.1, which is the book's "this function is equal to
its Fourier series pointwise"; the last clause says it in the sense of Definition 1.2.17.

The endpoint conditions are stated for the polynomial `(π² - x²)² / π⁴` itself rather than for the
extension `f`, which is how the book verifies them; `l = 3` already fails, matching the book's
`k = 4` for this example. Beware the near-match: `equation_4_1_5` is the book's *displayed*
equation (4.1.5), the complex Fourier coefficient, and has nothing to do with this example. -/
theorem example_4_1_5 {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) :
    (∀ l ≤ 2, iteratedDeriv l (fun x : ℝ => (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) (-π)
        = iteratedDeriv l (fun x : ℝ => (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) π) ∧
      (∀ j : ℕ, fourierCoeffSin f j = 0) ∧
      fourierCoeffCos f 0 = 16 / 15 ∧
      (∀ j : ℕ, 0 < j → fourierCoeffCos f j = 48 * (-1 : ℝ) ^ (j + 1) / (π ^ 4 * j ^ 4)) ∧
      (∀ (n : ℕ) (x : ℝ), fourierPartialSum f n x
        = 8 / 15 + 48 / π ^ 4 * ∑ i ∈ Finset.range n,
            (-1 : ℝ) ^ i * (Real.cos ((i + 1) * x) / (i + 1) ^ 4)) ∧
      (∀ x : ℝ, Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x))) ∧
      ∀ x : ℝ, Chapter01.definition_1_2_17
        (fun i : ℕ => 48 / π ^ 4 * ((-1 : ℝ) ^ i * (Real.cos ((i + 1) * x) / (i + 1) ^ 4)))
        (f x - 8 / 15) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨hsin, hcos0, hcos⟩ := quartic_fourierCoeff hval
  have hpartial := quartic_fourierPartialSum hsin hcos0 hcos
  have hconv := quartic_tendsto hper hval
  have hderiv1 : deriv (fun x : ℝ => (π ^ 2 - x ^ 2) ^ 2 / π ^ 4)
      = fun t : ℝ => (4 * t ^ 3 - 4 * π ^ 2 * t) / π ^ 4 :=
    funext fun y => (hasDerivAt_quarticNorm y).deriv
  refine ⟨fun l hl => ?_, hsin, hcos0, hcos, hpartial, hconv, fun x => ?_⟩
  · interval_cases l
    · simp only [iteratedDeriv_zero]
      ring
    · rw [iteratedDeriv_one, hderiv1]
      ring
    · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv1,
        (hasDerivAt_quarticNorm' (-π)).deriv, (hasDerivAt_quarticNorm' π).deriv]
      ring
  · have hclosed : Tendsto (fun n : ℕ => 8 / 15 + 48 / π ^ 4 * ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (Real.cos ((i + 1) * x) / (i + 1) ^ 4)) atTop (𝓝 (f x)) :=
      (hconv x).congr fun n => hpartial n x
    refine (Chapter01.definition_1_2_17_iff _ _).mpr
      ((hclosed.sub_const (8 / 15)).congr fun n => ?_)
    rw [← Finset.mul_sum]
    ring

/-! ### The truncation error (4.1.14)–(4.1.15) -/

/-- **(4.1.14)**, the `L²` truncation error of the Fourier series:

`‖f - S_n f‖²_{L²(-π,π)} = π ∑_{j > n} (|a_j|² + |b_j|²)`,

the tail of Parseval's equality (4.1.13), of which `equation_4_1_13` is the case `n = -1`.  It is
stated as a `HasSum` over `ℕ` whose terms of index at most `n` vanish, the shape in which the book
writes a series over the trigonometric system.

The book's `S_n` here is the `L²` partial sum, the backbone `trigPartialSum n`: the truncation of
the Fourier series to the frequencies of absolute value at most `n`, which by the coefficient
dictionary `equation_4_1_3_const`, `equation_4_1_3_cos` and `equation_4_1_3_sin` is
`a₀/2 + ∑_{j=1}^{n} (a_j cos (j x) + b_j sin (j x))`. -/
theorem equation_4_1_14 (n : ℕ)
    (F : Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
    HasSum (fun j : ℕ =>
        if j ≤ n then 0
        else π * (fourierCoeffCos (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) j ^ 2
          + fourierCoeffSin (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) j ^ 2))
      (∫ x in -π..π,
        ((F - trigPartialSum n F : Lp ℝ 2
          (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) : AddCircle (2 * π) → ℝ)
            ↑x ^ 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨G, hG⟩ : ∃ G : AddCircle (2 * π) → ℝ, (F : AddCircle (2 * π) → ℝ) = G := ⟨_, rfl⟩
  -- the tail of Parseval's identity, folded onto `ℕ` and rescaled to the book's normalisation
  have hB := (hasSum_int_fold (hasSum_sq_realFourierCoeff_compl n F)).mul_left (2 * π)
  rw [hG] at hB ⊢
  have hfun : (fun j : ℕ => 2 * π *
        if j = 0 then (if (0 : ℤ).natAbs ≤ n then 0 else realFourierCoeff G 0 ^ 2)
        else (if ((j : ℤ)).natAbs ≤ n then 0 else realFourierCoeff G (j : ℤ) ^ 2)
          + (if (-(j : ℤ)).natAbs ≤ n then 0 else realFourierCoeff G (-(j : ℤ)) ^ 2))
      = fun j : ℕ =>
        if j ≤ n then 0
        else π * (fourierCoeffCos (fun x : ℝ => G ↑x) j ^ 2
          + fourierCoeffSin (fun x : ℝ => G ↑x) j ^ 2) := by
    funext j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [ite_eq_left rfl]
      simp
    · rw [ite_eq_right hj, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast]
      by_cases hjn : j ≤ n
      · rw [ite_eq_left hjn, ite_eq_left hjn, ite_eq_left hjn, add_zero, mul_zero]
      · rw [ite_eq_right hjn, ite_eq_right hjn, ite_eq_right hjn,
          sq_realFourierCoeff_cos G (Nat.pos_of_ne_zero hj),
          sq_realFourierCoeff_sin G (Nat.pos_of_ne_zero hj)]
        ring
  rw [hfun] at hB
  -- the squared norm of the error, as the book's integral over `(-π, π)`
  have hval : 2 * π * ‖F - trigPartialSum n F‖ ^ 2
      = ∫ x in -π..π, ((F - trigPartialSum n F :
          Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
            AddCircle (2 * π) → ℝ) ↑x ^ 2 := by
    rw [norm_sq_eq_intervalIntegral]
    field_simp
  rwa [hval] at hB

/-- The `j`-th term of the real Fourier series of `f` at `x`, with the constant `a_0 / 2` carried
by the term `j = 0`, so that the `m`-th partial sum of the series is the sum over
`Finset.range (m + 1)`. -/
private noncomputable def fourierTerm (f : ℝ → ℝ) (x : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then fourierCoeffCos f 0 / 2
  else fourierCoeffCos f j * Real.cos (j * x) + fourierCoeffSin f j * Real.sin (j * x)

private theorem sum_range_fourierTerm (f : ℝ → ℝ) (x : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), fourierTerm f x j = fourierPartialSum f m x := by
  induction m with
  | zero =>
      rw [Finset.sum_range_one, fourierTerm, ite_eq_left rfl, fourierPartialSum]
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, fourierPartialSum_succ, fourierTerm,
        ite_eq_right (Nat.succ_ne_zero m)]

private theorem norm_fourierTerm_le (f : ℝ → ℝ) (x : ℝ) (j : ℕ) :
    ‖fourierTerm f x (j + 1)‖ ≤ |fourierCoeffCos f (j + 1)| + |fourierCoeffSin f (j + 1)| := by
  rw [fourierTerm, ite_eq_right (Nat.succ_ne_zero j), Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

private theorem summable_fourierTerm {f : ℝ → ℝ}
    (hs : Summable fun j : ℕ => |fourierCoeffCos f j| + |fourierCoeffSin f j|) (x : ℝ) :
    Summable (fourierTerm f x) :=
  (summable_nat_add_iff 1).mp
    (Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hs) (norm_fourierTerm_le f x))

/-- **(4.1.15)**, the uniform truncation error: when the Fourier coefficients are absolutely
summable and the Fourier series converges to `f`, the partial sums satisfy

`|f x - S_n x| ≤ ∑_{j > n} (|a_j| + |b_j|)`

at every `x`, so in particular the maximum over `[-π, π]` obeys the same bound.

The summability hypothesis is the book's "the Fourier series is absolutely convergent", and it
cannot be dropped: without it the right-hand side is Mathlib's junk value `0` for a non-summable
`tsum` and the inequality is false.  The convergence hypothesis is the book's "`f` is continuous
after possibly being modified on a set of measure zero", under which the display the bound is read
off, `f x - S_n x = ∑_{j > n} [a_j cos (j x) + b_j sin (j x)]`, holds. -/
theorem equation_4_1_15 {f : ℝ → ℝ}
    (hs : Summable fun j : ℕ => |fourierCoeffCos f j| + |fourierCoeffSin f j|)
    (hconv : ∀ y : ℝ, Tendsto (fun m : ℕ => fourierPartialSum f m y) atTop (𝓝 (f y)))
    (n : ℕ) (x : ℝ) :
    |f x - fourierPartialSum f n x|
      ≤ ∑' j : ℕ, (|fourierCoeffCos f (j + (n + 1))| + |fourierCoeffSin f (j + (n + 1))|) := by
  have hsum := summable_fourierTerm hs x
  -- the series sums to `f x`
  have hfx : ∑' j : ℕ, fourierTerm f x j = f x :=
    tendsto_nhds_unique
      ((hsum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)).congr
        (sum_range_fourierTerm f x))
      (hconv x)
  -- the truncation error is the tail of the series
  have htail : f x - fourierPartialSum f n x = ∑' j : ℕ, fourierTerm f x (j + (n + 1)) := by
    have h := hsum.sum_add_tsum_nat_add (n + 1)
    rw [sum_range_fourierTerm f x n, hfx] at h
    linarith
  have hcsum : Summable fun j : ℕ =>
      |fourierCoeffCos f (j + (n + 1))| + |fourierCoeffSin f (j + (n + 1))| :=
    (summable_nat_add_iff
      (f := fun j : ℕ => |fourierCoeffCos f j| + |fourierCoeffSin f j|) (n + 1)).mpr hs
  have hnormsum : Summable fun j : ℕ => ‖fourierTerm f x (j + (n + 1))‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => norm_fourierTerm_le f x (j + n))
      hcsum
  rw [htail, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hnormsum).trans
    (hnormsum.tsum_le_tsum (fun j => norm_fourierTerm_le f x (j + n)) hcsum)

end AtkinsonHan.Chapter04
