import Numlib.Analysis.Fourier.Dirichlet
import Numlib.Analysis.Fourier.TrigonometricBasis
import NumlibSurface.AtkinsonHan.Chapter02.Section04
import NumlibSurface.AtkinsonHan.Chapter03.Section01

/-!
# Atkinson–Han §4.1: Fourier series

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

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

## Not formalized here

Examples 4.1.3–4.1.5 (the Fourier series of a step function, of `|x|/π` and of `(π² - x²)²/π⁴`) and
the Gibbs phenomenon, which are numerical illustrations and whose constant `(2/π) Si(π)` the book
asserts without proof; and the `L^p` boundedness (4.1.12) for `1 < p < ∞`, which is the M. Riesz
theorem and is not in Mathlib.  The partial-sum operators of Theorem 4.1.2 are therefore *given* as
a sequence of bounded operators fixing the trigonometric polynomials in the limit, rather than
constructed on `L^p`; at `p = 2` they are the truncations of `hasSum_trigSeries`, whose uniform
bound is Bessel's inequality, and the conclusion there is `equation_4_1_13`.
-/

open Filter MeasureTheory Topology

open scoped ENNReal Real

namespace AtkinsonHan.Ch04

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

/-- The two halves of `(-π, π)` are subintervals of it. -/
private theorem uIcc_subset_left : Set.uIcc (-π) (0 : ℝ) ⊆ Set.uIcc (-π) π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
  exact Set.Icc_subset_Icc le_rfl (by linarith)

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
theorem denseRange_toLp_trigSpan {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense (ContinuousMap.toLp (E := ℝ) p
        (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ ''
      (Submodule.span ℝ (Set.range (trigFun (2 * π))) : Set C(AddCircle (2 * π), ℝ))) := by
  have hWdense : Dense (Submodule.span ℝ (Set.range (trigFun (2 * π))) :
      Set C(AddCircle (2 * π), ℝ)) := by
    intro f
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq, hqf⟩ := AtkinsonHan.Ch03.corollary_3_1_4 f hε
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
    refine AtkinsonHan.Ch02.theorem_2_4_4 S fun v => ?_
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
      (denseRange_toLp_trigSpan (p := p) hp) hC hon f
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
    rw [← integral_intervalIntegral_eq (fun b => G b ^ 2), ← real_inner_self_eq_norm_sq,
      MeasureTheory.L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    dsimp only
    rw [RCLike.inner_apply, hG]
    simp [sq]
  -- the coefficient dictionary
  have hc0 : realFourierCoeff G 0 = fourierCoeffCos (fun x : ℝ => G ↑x) 0 / 2 := by
    rw [equation_4_1_3_const]; ring
  have hcj : ∀ j : ℕ, 0 < j →
      realFourierCoeff G j ^ 2 = fourierCoeffCos (fun x : ℝ => G ↑x) j ^ 2 / 2 := by
    intro j hj
    rw [equation_4_1_3_cos G hj, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hsj : ∀ j : ℕ, 0 < j →
      realFourierCoeff G (-j) ^ 2 = fourierCoeffSin (fun x : ℝ => G ↑x) j ^ 2 / 2 := by
    intro j hj
    rw [equation_4_1_3_sin G hj, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
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

end AtkinsonHan.Ch04
