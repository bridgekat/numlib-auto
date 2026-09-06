/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.AddCircle`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The real trigonometric system as a Hilbert basis of `L²` on a circle

Mathlib's `fourierBasis` is the Hilbert basis of `Lp ℂ 2 haarAddCircle` formed by the complex
exponentials `fourier n : x ↦ exp (2 π i n x / T)`. Classical analysis states the same theory over
the reals, with the system

`1`, `√2 cos (2 π n x / T)`, `√2 sin (2 π n x / T)`, for `n ≥ 1`,

which is orthonormal for the probability measure `haarAddCircle` on the circle `AddCircle T` of
circumference `T`. This file defines that system as `trigFun`, indexed by `ℤ` so that a single
family carries the constant (`n = 0`), the cosines (`n > 0`) and the sines (`n < 0`); proves it
orthonormal; records the dictionary between the real coefficients and Mathlib's complex
`fourierCoeff`; and assembles the system into
`trigBasis : HilbertBasis ℤ ℝ (Lp ℝ 2 haarAddCircle)`.

The file is organised around the single identity
`trigFun T n x = (trigWeight n * fourier n x).re`, where `trigWeight n` is `1`, `√2` or `√2 * i`
according to the sign of `n`. It turns every computation about the real system into one about the
complex exponentials, so that nothing here repeats an argument Mathlib already has: orthonormality
reduces to `∫ fourier n = 0` for `n ≠ 0`, and completeness to `fourierBasis` through
`realFourierCoeff_eq_fourierCoeff`, not to a second Stone-Weierstrass argument.

Atkinson and Han[^atkinson-han] state the orthonormal basis as Theorem 1.3.13 and the coefficient
dictionary as (4.1.6). The normalisation used here — `‖trigFun T n‖ = 1` in `L²` of the
*probability* Haar measure — is the one that makes the system a Hilbert basis; the book's `a_j`,
`b_j` of (4.1.2)-(4.1.3), for which the series reads `a₀/2 + ∑ (a_j cos + b_j sin)`, are
`√2 * realFourierCoeff f j` and `√2 * realFourierCoeff f (-j)`.

## Main definitions

* `trigWeight n`, the complex weight relating `trigFun` to `fourier`;
* `trigFun T n : C(AddCircle T, ℝ)`, the real trigonometric system;
* `trigLp T n : Lp ℝ 2 haarAddCircle`, the same as an element of `L²`;
* `realFourierCoeff f n`, the coefficient of `f` against `trigFun T n`;
* `trigBasis T : HilbertBasis ℤ ℝ (Lp ℝ 2 haarAddCircle)`;
* `trigPolyLE T n`, the subspace of `C(AddCircle T, ℝ)` of the trigonometric polynomials of degree
  at most `n`, spanned by the `trigFun T m` with `|m| ≤ n`.

## Main results

* `orthonormal_trigFun`: the system is orthonormal;
* `realFourierCoeff_eq_fourierCoeff`: the dictionary to Mathlib's complex `fourierCoeff`;
* `hasSum_trigSeries`: the real Fourier series of an `L²` function converges to it in `L²`;
* `tsum_sq_realFourierCoeff`: Parseval's identity in real form;
* `mem_trigPolyLE_iff`, `linearIndependent_trigFun` and `finrank_trigPolyLE`: the trigonometric
  polynomials of degree at most `n` are the linear combinations of the `trigFun T m` with
  `|m| ≤ n`, and they form a space of dimension `2 n + 1`.  That space is what the Fourier
  projection and trigonometric interpolation project onto, and the Haar subspace of the
  trigonometric equioscillation theorem, so it is defined once here rather than in each of them.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open Complex MeasureTheory Set Submodule

open scoped ComplexConjugate ENNReal Real

variable {T : ℝ}

/-! ### The system -/

/-- The complex weight that turns the exponential `fourier n` into the `n`-th member of the real
trigonometric system: `trigWeight 0 = 1`, `trigWeight n = √2` for `n > 0` and
`trigWeight n = √2 * I` for `n < 0`. Its modulus is the constant that normalises the system for
the probability measure `haarAddCircle`, and its argument selects a cosine or a sine, through
`trigFun_apply : trigFun T n x = (trigWeight n * fourier n x).re`. -/
noncomputable def trigWeight (n : ℤ) : ℂ :=
  if n = 0 then 1 else if 0 < n then (√2 : ℝ) else (√2 : ℝ) * I

@[simp]
theorem trigWeight_zero : trigWeight 0 = 1 := ite_eq_left rfl

theorem trigWeight_of_pos {n : ℤ} (hn : 0 < n) : trigWeight n = (√2 : ℝ) := by
  rw [trigWeight, ite_eq_right hn.ne', ite_eq_left hn]

theorem trigWeight_of_neg {n : ℤ} (hn : n < 0) : trigWeight n = (√2 : ℝ) * I := by
  rw [trigWeight, ite_eq_right hn.ne, ite_eq_right (by omega)]

/-- The real trigonometric system on the circle of circumference `T`, normalised for the
probability measure `haarAddCircle`: `trigFun T 0 = 1`, `trigFun T n = √2 cos (2 π n x / T)` for
`n > 0`, and `trigFun T n = √2 sin (-2 π n x / T)` for `n < 0`. Indexing by `ℤ` keeps a single
family where the classical statement has three. -/
noncomputable def trigFun (T : ℝ) (n : ℤ) : C(AddCircle T, ℝ) where
  toFun x := (trigWeight n * fourier n x).re
  continuous_toFun := Complex.continuous_re.comp (continuous_const.mul (fourier n).continuous)

@[simp]
theorem trigFun_apply (T : ℝ) (n : ℤ) (x : AddCircle T) :
    trigFun T n x = (trigWeight n * fourier n x).re :=
  rfl

@[simp]
theorem trigFun_zero : trigFun T 0 = 1 := by
  ext x; simp

private theorem fourier_coe_apply_mul_I (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle T) = Complex.exp (((2 * π * n * x / T : ℝ) : ℂ) * I) := by
  rw [fourier_coe_apply]
  push_cast
  ring_nf

theorem trigFun_coe_apply_of_pos {n : ℤ} (hn : 0 < n) (x : ℝ) :
    trigFun T n (x : AddCircle T) = √2 * Real.cos (2 * π * n * x / T) := by
  rw [trigFun_apply, trigWeight_of_pos hn, fourier_coe_apply_mul_I, re_ofReal_mul,
    exp_ofReal_mul_I_re]

theorem trigFun_coe_apply_of_neg {n : ℤ} (hn : n < 0) (x : ℝ) :
    trigFun T n (x : AddCircle T) = √2 * Real.sin (-(2 * π * n * x / T)) := by
  rw [trigFun_apply, trigWeight_of_neg hn, fourier_coe_apply_mul_I, mul_assoc, re_ofReal_mul,
    Real.sin_neg, Complex.I_mul_re, exp_ofReal_mul_I_im]

/-- The `n`-th member of the real trigonometric system, as an element of `L²` of the circle. -/
noncomputable abbrev trigLp (T : ℝ) [hT : Fact (0 < T)] (n : ℤ) :
    Lp ℝ 2 (@AddCircle.haarAddCircle T hT) :=
  ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ (trigFun T n)

private theorem norm_fourier_apply (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

section Circle

variable [hT : Fact (0 < T)]

open AddCircle

/-! ### Integrals of the exponentials -/

private theorem integrable_const_mul_fourier (c : ℂ) (n : ℤ) :
    Integrable (fun x : AddCircle T => c * fourier n x) haarAddCircle :=
  Integrable.mul_bdd (c := 1)
    (integrable_const (μ := (haarAddCircle : Measure (AddCircle T))) c)
    (map_continuous (fourier n)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_fourier_apply n x).le)

/-- The integral of `fourier n` against the probability Haar measure: `1` at `n = 0` and `0`
elsewhere. -/
theorem integral_fourier (n : ℤ) :
    ∫ x : AddCircle T, fourier n x ∂haarAddCircle = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) n) 0
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, smul_eq_mul, one_mul] at h
  rw [h, Pi.single_apply]
  simp [eq_comm]

private theorem integral_re_const_mul_fourier (c : ℂ) (n : ℤ) :
    ∫ x : AddCircle T, (c * fourier n x).re ∂haarAddCircle = if n = 0 then c.re else 0 := by
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM
    (integrable_const_mul_fourier (T := T) c n)
  simp only [Complex.reCLM_apply] at h
  rw [h, integral_const_mul, integral_fourier]
  split_ifs with hn <;> simp

/-! ### Orthonormality -/

private theorem integral_trigFun_mul (i j : ℤ) :
    ∫ x : AddCircle T, trigFun T j x * trigFun T i x ∂haarAddCircle = if i = j then 1 else 0 := by
  have key : ∀ x : AddCircle T, trigFun T j x * trigFun T i x
      = 2⁻¹ * ((trigWeight i * trigWeight j * fourier (i + j) x).re
        + (trigWeight i * conj (trigWeight j) * fourier (i - j) x).re) := by
    intro x
    have hadd : fourier (i + j) x = fourier i x * fourier j x := fourier_add
    have hsub : fourier (i - j) x = fourier i x * conj (fourier j x) := by
      rw [sub_eq_add_neg, fourier_add, fourier_neg]
    rw [trigFun_apply, trigFun_apply, hadd, hsub]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hint : ∀ c : ℂ, ∀ m : ℤ,
      Integrable (fun x : AddCircle T => (c * fourier m x).re) haarAddCircle := fun c m =>
    Integrable.re (integrable_const_mul_fourier c m)
  rw [integral_congr_ae (Filter.Eventually.of_forall key), integral_const_mul,
    integral_add (hint _ _) (hint _ _), integral_re_const_mul_fourier,
    integral_re_const_mul_fourier]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl, ite_eq_left (sub_self i)]
    rcases eq_or_ne i 0 with rfl | hi
    · norm_num
    · rw [ite_eq_right (by omega), trigWeight, ite_eq_right hi]
      split_ifs <;>
        · simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
          nlinarith [h2]
  · rw [ite_eq_right hij, ite_eq_right (sub_ne_zero.mpr hij), add_zero]
    rcases eq_or_ne (i + j) 0 with hij0 | hij0
    · have hi : i ≠ 0 := by omega
      rw [ite_eq_left hij0, trigWeight, trigWeight, ite_eq_right hi,
        ite_eq_right (show j ≠ 0 by omega)]
      rcases lt_or_gt_of_ne hi with h | h
      · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        simp [Complex.mul_re]
      · rw [ite_eq_left h, ite_eq_right (by omega)]
        simp [Complex.mul_re]
    · rw [ite_eq_right hij0]; ring

/-- The real trigonometric system is orthonormal in `L²` of the circle with its probability Haar
measure. This is the orthonormality half of Atkinson and Han, *Theoretical Numerical Analysis*,
Theorem 1.3.13. -/
theorem orthonormal_trigFun : Orthonormal ℝ (trigLp T) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [ContinuousMap.inner_toLp AddCircle.haarAddCircle (trigFun T i) (trigFun T j)]
  simpa using integral_trigFun_mul i j

/-! ### The real Fourier coefficients -/

/-- The `n`-th real Fourier coefficient of `f : AddCircle T → ℝ`: the integral of `f` against
`trigFun T n` for the probability Haar measure. The classical `a_j` and `b_j`, normalised so that
the series reads `a₀/2 + ∑ (a_j cos + b_j sin)`, are `√2 * realFourierCoeff f j` and
`√2 * realFourierCoeff f (-j)`. -/
noncomputable def realFourierCoeff (f : AddCircle T → ℝ) (n : ℤ) : ℝ :=
  ∫ x : AddCircle T, trigFun T n x * f x ∂haarAddCircle

theorem realFourierCoeff_apply (f : AddCircle T → ℝ) (n : ℤ) :
    realFourierCoeff f n = ∫ x : AddCircle T, trigFun T n x * f x ∂haarAddCircle :=
  rfl

@[simp]
theorem realFourierCoeff_zero (f : AddCircle T → ℝ) :
    realFourierCoeff f 0 = ∫ x : AddCircle T, f x ∂haarAddCircle := by
  simp [realFourierCoeff_apply]

/-- The real Fourier coefficients of a member of the real trigonometric system: the system is its
own coefficient sequence.  This is `orthonormal_trigFun` read on the continuous functions rather
than on `L²`, and it is what makes the Fourier projection of `Numlib/Approximation/Trigonometric`
fix the trigonometric polynomials. -/
@[simp]
theorem realFourierCoeff_trigFun (i j : ℤ) :
    realFourierCoeff (trigFun T i) j = if i = j then 1 else 0 :=
  integral_trigFun_mul i j

/-- The complex Fourier coefficients of a real-valued function are conjugate-symmetric. -/
theorem fourierCoeff_ofReal_neg (f : AddCircle T → ℝ) (n : ℤ) :
    fourierCoeff (fun x => (f x : ℂ)) (-n) = conj (fourierCoeff (fun x => (f x : ℂ)) n) := by
  have h : ∀ x : AddCircle T, conj (fourier (-n) x) = fourier n x := by
    intro x; rw [← fourier_neg, neg_neg]
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, neg_neg, h]

/-- The dictionary between the real trigonometric coefficients and Mathlib's complex
`fourierCoeff`: for a real-valued integrable `f`,
`realFourierCoeff f n = (trigWeight n * fourierCoeff (fun x => (f x : ℂ)) (-n)).re`.
Since `trigWeight` is `1`, `√2` and `√2 * i` according to the sign of `n`, this says that the
constant coefficient is the constant complex coefficient, that the cosine coefficients are `√2`
times real parts and the sine coefficients `√2` times imaginary parts; see
`realFourierCoeff_of_pos`, `realFourierCoeff_of_neg` and `fourierCoeff_ofReal`. -/
theorem realFourierCoeff_eq_fourierCoeff {f : AddCircle T → ℝ}
    (hf : Integrable f haarAddCircle) (n : ℤ) :
    realFourierCoeff f n = (trigWeight n * fourierCoeff (fun x => (f x : ℂ)) (-n)).re := by
  have hint : Integrable (fun x : AddCircle T => trigWeight n * fourier n x * (f x : ℂ))
      haarAddCircle :=
    Integrable.bdd_mul (c := ‖trigWeight n‖) (Integrable.ofReal hf)
      (continuous_const.mul (map_continuous (fourier n))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [norm_mul, norm_fourier_apply, mul_one])
  have hre : ∀ x : AddCircle T,
      trigFun T n x * f x = (trigWeight n * fourier n x * (f x : ℂ)).re := by
    intro x
    rw [trigFun_apply]
    simp [Complex.mul_re]
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hint
  simp only [Complex.reCLM_apply] at h
  rw [realFourierCoeff_apply, integral_congr_ae (Filter.Eventually.of_forall hre), h, fourierCoeff,
    neg_neg]
  congr 1
  simp_rw [smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

/-- The cosine coefficients are `√2` times the real parts of the complex Fourier coefficients. -/
theorem realFourierCoeff_of_pos {f : AddCircle T → ℝ} (hf : Integrable f haarAddCircle)
    {n : ℤ} (hn : 0 < n) :
    realFourierCoeff f n = √2 * (fourierCoeff (fun x => (f x : ℂ)) n).re := by
  rw [realFourierCoeff_eq_fourierCoeff hf, trigWeight_of_pos hn, re_ofReal_mul,
    fourierCoeff_ofReal_neg, Complex.conj_re]

/-- The sine coefficients are `√2` times the imaginary parts of the complex Fourier coefficients. -/
theorem realFourierCoeff_of_neg {f : AddCircle T → ℝ} (hf : Integrable f haarAddCircle)
    {n : ℤ} (hn : n < 0) :
    realFourierCoeff f n = √2 * (fourierCoeff (fun x => (f x : ℂ)) n).im := by
  rw [realFourierCoeff_eq_fourierCoeff hf, trigWeight_of_neg hn, mul_assoc, re_ofReal_mul,
    fourierCoeff_ofReal_neg]
  simp [Complex.mul_re]

/-- The classical form of the dictionary: for `n > 0` the complex Fourier coefficient is
`(a_n - i b_n) / 2` in the book's normalisation, here `(aₙ - i bₙ) / √2` with `aₙ` and `bₙ` the
real coefficients at `n` and `-n`. -/
theorem fourierCoeff_ofReal {f : AddCircle T → ℝ} (hf : Integrable f haarAddCircle)
    {n : ℤ} (hn : 0 < n) :
    fourierCoeff (fun x => (f x : ℂ)) n =
      ((realFourierCoeff f n : ℂ) - I * (realFourierCoeff f (-n) : ℂ)) / (√2 : ℝ) := by
  have h2 : ((√2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  rw [realFourierCoeff_of_pos hf hn, realFourierCoeff_of_neg hf (show -n < 0 by omega),
    fourierCoeff_ofReal_neg, Complex.conj_im, eq_div_iff h2]
  push_cast
  linear_combination (-((√2 : ℝ) : ℂ)) * Complex.re_add_im (fourierCoeff (fun x => (f x : ℂ)) n)

/-! ### Completeness -/

private theorem fourierCoeff_eq_zero_of_realFourierCoeff_eq_zero {f : AddCircle T → ℝ}
    (hf : Integrable f haarAddCircle) (h : ∀ n, realFourierCoeff f n = 0) (n : ℤ) :
    fourierCoeff (fun x => (f x : ℂ)) n = 0 := by
  have h2 : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hre : ∀ m : ℤ, 0 < m → (fourierCoeff (fun x => (f x : ℂ)) m).re = 0 := by
    intro m hm
    have hh : √2 * (fourierCoeff (fun x => (f x : ℂ)) m).re = 0 :=
      (realFourierCoeff_of_pos hf hm).symm.trans (h m)
    exact (mul_eq_zero.mp hh).resolve_left h2
  have him : ∀ m : ℤ, m < 0 → (fourierCoeff (fun x => (f x : ℂ)) m).im = 0 := by
    intro m hm
    have hh : √2 * (fourierCoeff (fun x => (f x : ℂ)) m).im = 0 :=
      (realFourierCoeff_of_neg hf hm).symm.trans (h m)
    exact (mul_eq_zero.mp hh).resolve_left h2
  refine Complex.ext ?_ ?_
  · rcases lt_trichotomy n 0 with hn | rfl | hn
    · have := hre (-n) (by omega)
      rwa [fourierCoeff_ofReal_neg, Complex.conj_re] at this
    · have := h 0
      rw [realFourierCoeff_zero] at this
      rw [fourierCoeff]
      simp only [neg_zero, fourier_zero, one_smul, integral_complex_ofReal, this]
      simp
    · exact hre n hn
  · rcases lt_trichotomy n 0 with hn | rfl | hn
    · exact him n hn
    · rw [fourierCoeff]
      simp only [neg_zero, fourier_zero, one_smul, integral_complex_ofReal]
      simp
    · have := him (-n) (by omega)
      rw [fourierCoeff_ofReal_neg, Complex.conj_im, neg_eq_zero] at this
      simpa using this

/-- The inner product of an `L²` function with a member of the real trigonometric system is the
corresponding real Fourier coefficient. -/
theorem inner_trigLp (n : ℤ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    inner ℝ (trigLp T n) f = realFourierCoeff (f : AddCircle T → ℝ) n := by
  rw [MeasureTheory.L2.inner_def, realFourierCoeff_apply]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (𝕜 := ℝ) haarAddCircle
    (trigFun T n)] with x hx
  rw [hx, RCLike.inner_apply]
  simp [mul_comm]

/-- The span of the real trigonometric system is dense in `L²`: its orthogonal complement is
trivial, because a function orthogonal to every member has all its complex Fourier coefficients
zero, and Mathlib's `fourierBasis` is complete. -/
theorem orthogonal_span_trigLp_eq_bot : (span ℝ (range (trigLp T)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hcoeff : ∀ n : ℤ, realFourierCoeff (f : AddCircle T → ℝ) n = 0 := by
    intro n
    rw [← inner_trigLp n f]
    exact (Submodule.mem_orthogonal _ _).mp hf _ (subset_span ⟨n, rfl⟩)
  have hf1 : Integrable (f : AddCircle T → ℝ) haarAddCircle :=
    memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num))
  -- the complexification of `f`, as an element of `Lp ℂ 2`
  set F : Lp ℂ 2 (@haarAddCircle T hT) := Complex.ofRealCLM.compLp f with hF
  have hFae : (F : AddCircle T → ℂ) =ᵐ[haarAddCircle] fun x => ((f : AddCircle T → ℝ) x : ℂ) :=
    Complex.ofRealCLM.coeFn_compLp' f
  have hFcoeff : ∀ n : ℤ, fourierCoeff (F : AddCircle T → ℂ) n = 0 := by
    intro n
    rw [fourierCoeff_congr_ae hFae]
    exact fourierCoeff_eq_zero_of_realFourierCoeff_eq_zero hf1 hcoeff n
  have hF0 : F = 0 := by
    have : fourierBasis.repr F = 0 := by
      ext n
      rw [fourierBasis_repr, hFcoeff n]
      simp
    simpa using congrArg (fourierBasis (T := T)).repr.symm this
  have : (f : AddCircle T → ℝ) =ᵐ[haarAddCircle] 0 := by
    have h0 : (F : AddCircle T → ℂ) =ᵐ[haarAddCircle] 0 := by rw [hF0]; exact Lp.coeFn_zero _ _ _
    filter_upwards [hFae, h0] with x hx1 hx2
    have hx : ((f : AddCircle T → ℝ) x : ℂ) = 0 := by rw [← hx1, hx2]; rfl
    exact_mod_cast hx
  exact Lp.eq_zero_iff_ae_eq_zero.mpr this

/-- **The real trigonometric system is a Hilbert basis of `L²` on the circle.** This is Atkinson
and Han, *Theoretical Numerical Analysis*, Theorem 1.3.13. -/
noncomputable def trigBasis (T : ℝ) [hT : Fact (0 < T)] :
    HilbertBasis ℤ ℝ (Lp ℝ 2 (@haarAddCircle T hT)) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_trigFun orthogonal_span_trigLp_eq_bot

@[simp]
theorem coe_trigBasis : ⇑(trigBasis T) = trigLp T :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The coordinates of an `L²` function in the Hilbert basis `trigBasis` are its real Fourier
coefficients. -/
theorem trigBasis_repr (f : Lp ℝ 2 (@haarAddCircle T hT)) (n : ℤ) :
    (trigBasis T).repr f n = realFourierCoeff (f : AddCircle T → ℝ) n := by
  rw [HilbertBasis.repr_apply_apply, coe_trigBasis, inner_trigLp]

/-- The real Fourier series of an `L²` function converges to it in `L²`. This is the `p = 2` case
of the classical `Lᵖ` convergence theorem, and Atkinson and Han, *Theoretical Numerical Analysis*,
Example 1.3.15. -/
theorem hasSum_trigSeries (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    HasSum (fun n : ℤ => realFourierCoeff (f : AddCircle T → ℝ) n • trigLp T n) f := by
  simpa only [trigBasis_repr, coe_trigBasis] using (trigBasis T).hasSum_repr f

/-- **Parseval's identity** in real form: the sum of the squares of the real Fourier coefficients
of an `L²` function is the square of its `L²` norm. -/
theorem tsum_sq_realFourierCoeff (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    ∑' n : ℤ, realFourierCoeff (f : AddCircle T → ℝ) n ^ 2 = ‖f‖ ^ 2 := by
  have h := (trigBasis T).tsum_inner_mul_inner f f
  simp only [coe_trigBasis, inner_trigLp, real_inner_self_eq_norm_sq] at h
  rw [← h]
  refine tsum_congr fun n => ?_
  rw [real_inner_comm, inner_trigLp]
  ring

end Circle

/-! ### The trigonometric polynomials of degree at most `n` -/

/-- The **trigonometric polynomials of degree at most `n`** on the circle of circumference `T`:
the subspace of `C(AddCircle T, ℝ)` spanned by the members `trigFun T m` of the real trigonometric
system with `|m| ≤ n`, that is, by the constant together with the cosines and the sines of
frequencies `1, …, n`.

This is the subspace that the Fourier projection and trigonometric interpolation project onto, and
the Haar subspace of the trigonometric equioscillation theorem. It is `2 n + 1`-dimensional
(`finrank_trigPolyLE`). -/
noncomputable def trigPolyLE (T : ℝ) (n : ℕ) : Submodule ℝ C(AddCircle T, ℝ) :=
  span ℝ (trigFun T '' Set.Icc (-(n : ℤ)) n)

variable {n : ℕ}

theorem mem_Icc_iff_natAbs_le {m : ℤ} : m ∈ Set.Icc (-(n : ℤ)) n ↔ m.natAbs ≤ n := by
  rw [Set.mem_Icc]
  omega

/-- Each member of the real trigonometric system of index at most `n` in absolute value is a
trigonometric polynomial of degree at most `n`. -/
theorem trigFun_mem_trigPolyLE {m : ℤ} (hm : m.natAbs ≤ n) : trigFun T m ∈ trigPolyLE T n :=
  subset_span ⟨m, mem_Icc_iff_natAbs_le.2 hm, rfl⟩

/-- The trigonometric polynomials of degree at most `n` are exactly the linear combinations of the
`2 n + 1` members of the real trigonometric system of index at most `n` in absolute value. -/
theorem mem_trigPolyLE_iff {f : C(AddCircle T, ℝ)} :
    f ∈ trigPolyLE T n ↔ ∃ c : ℤ → ℝ, f = ∑ m ∈ Finset.Icc (-(n : ℤ)) n, c m • trigFun T m := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      refine ⟨fun j => if j = m then 1 else 0, ?_⟩
      rw [Finset.sum_eq_single m (fun j _ hj => by simp [hj]) fun hm' => ?_]
      · simp
      · exact absurd (Finset.mem_Icc.2 (Set.mem_Icc.1 hm)) hm'
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨cx, rfl⟩ := hx
      obtain ⟨cy, rfl⟩ := hy
      exact ⟨cx + cy, by simp [← Finset.sum_add_distrib, add_smul]⟩
    | smul r x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨r • c, by simp [Finset.smul_sum, smul_smul]⟩
  · rintro ⟨c, rfl⟩
    exact sum_mem fun m hm =>
      Submodule.smul_mem _ _ (subset_span ⟨m, Set.mem_Icc.2 (Finset.mem_Icc.1 hm), rfl⟩)

/-- The trigonometric polynomials of degree at most `n` form an increasing family of subspaces. -/
theorem trigPolyLE_mono {m n : ℕ} (h : m ≤ n) : trigPolyLE T m ≤ trigPolyLE T n :=
  span_mono (Set.image_mono fun _j hj => mem_Icc_iff_natAbs_le.2
    ((mem_Icc_iff_natAbs_le.1 hj).trans h))

instance : FiniteDimensional ℝ (trigPolyLE T n) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_Icc _ _).image _)

section Circle

variable [hT : Fact (0 < T)]

/-- The real trigonometric system is linearly independent in `C(AddCircle T, ℝ)`, because it is
orthonormal in `L²` and the inclusion of the continuous functions is linear. -/
theorem linearIndependent_trigFun : LinearIndependent ℝ (trigFun T) :=
  orthonormal_trigFun.linearIndependent.of_comp
    (ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ).toLinearMap

/-- **The trigonometric polynomials of degree at most `n` form a space of dimension `2 n + 1`**:
the constant, and a cosine and a sine for each frequency `1, …, n`. -/
theorem finrank_trigPolyLE (T : ℝ) [Fact (0 < T)] (n : ℕ) :
    Module.finrank ℝ (trigPolyLE T n) = 2 * n + 1 := by
  have hrange : trigFun T '' Set.Icc (-(n : ℤ)) n
      = Set.range (trigFun T ∘ (Subtype.val : ↑(Set.Icc (-(n : ℤ)) (n : ℤ)) → ℤ)) := by
    rw [Set.range_comp, Subtype.range_coe]
  rw [trigPolyLE, hrange,
    finrank_span_eq_card (linearIndependent_trigFun.comp _ Subtype.val_injective),
    Fintype.card_Icc, Int.card_Icc]
  omega

end Circle
