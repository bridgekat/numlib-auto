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
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The real trigonometric system as a Hilbert basis of $L^2$ on a circle

Let $T > 0$, let $\mathbb{T}_T = \mathbb{R} / T \mathbb{Z}$ be the circle of circumference $T$, and
let $\mu$ be its Haar probability measure. Mathlib's `fourierBasis` is the Hilbert basis of the
complex space $L^2(\mathbb{T}_T)$ formed by the exponentials $e_n(x) = \exp(2 \pi i n x / T)$,
$n \in \mathbb{Z}$. This module states the same theory over the reals, with the system
$$1, \qquad \sqrt{2} \cos(2 \pi n x / T), \qquad \sqrt{2} \sin(2 \pi n x / T), \qquad n \ge 1,$$
which is orthonormal for $\mu$. It writes $t_n$ for the members of this system, indexed by
$n \in \mathbb{Z}$, and $r_n(f) = \int t_n f \, d\mu$ for the real Fourier coefficients. The module
proves that $(t_n)$ is a Hilbert basis of the real space $L^2(\mathbb{T}_T)$, relates $r_n(f)$ to
the complex coefficients $c_n(f) = \int e_{-n} f \, d\mu$, proves Parseval's identity and the error
formula for the partial sums $S_n f = \sum_{|m| \le n} r_m(f) t_m$, shows that the space $V_n$ of
trigonometric polynomials of degree at most $n$ has dimension $2n + 1$, and proves that the real
trigonometric polynomials are uniformly dense in the continuous functions on $\mathbb{T}_T$.

[han2009theoretical] state the orthonormal basis as Theorem 1.3.13 and the relation between the real
and the complex coefficients as (4.1.6). The normalization here, $\|t_n\| = 1$ in $L^2$ of the
probability measure $\mu$, is the one that makes the system a Hilbert basis. The coefficients $a_j$
and $b_j$ of (4.1.2)–(4.1.3), for which the series reads
$a_0 / 2 + \sum_{j \ge 1} (a_j \cos + b_j \sin)$, are $a_j = \sqrt{2} \, r_j(f)$ and
$b_j = \sqrt{2} \, r_{-j}(f)$ for $j \ge 1$, and $a_0 = 2 r_0(f)$.

## Main definitions

* `trigWeight`: the complex weight $w_n$, equal to $1$, $\sqrt{2}$ or $\sqrt{2} \, i$, with
  $t_n = \operatorname{Re}(w_n e_n)$.
* `trigFun`: the real trigonometric system $t_n$, as continuous functions on $\mathbb{T}_T$.
* `trigLp`: the function $t_n$ as an element of $L^2(\mathbb{T}_T)$.
* `realFourierCoeff`: the real Fourier coefficient $r_n(f) = \int t_n f \, d\mu$.
* `trigBasis`: the real trigonometric system as a Hilbert basis of $L^2(\mathbb{T}_T)$, indexed by
  $\mathbb{Z}$.
* `trigPartialSum`: the partial sum $S_n f = \sum_{|m| \le n} r_m(f) t_m$ of the Fourier series.
* `trigPolyLE`: the space $V_n$ of trigonometric polynomials of degree at most $n$, spanned by the
  $t_m$ with $|m| \le n$.

## Main results

* `orthonormal_trigFun`: the system $(t_n)$ is orthonormal in $L^2(\mathbb{T}_T)$.
* `realFourierCoeff_eq_fourierCoeff`: for integrable $f$,
  $r_n(f) = \operatorname{Re}(w_n c_{-n}(f))$.
* `trigBasis_repr`: the coordinates of $f$ in the Hilbert basis are the coefficients $r_n(f)$.
* `hasSum_trigSeries`: the real Fourier series of $f \in L^2(\mathbb{T}_T)$ converges to $f$ in
  $L^2$.
* `tsum_sq_realFourierCoeff`: Parseval's identity $\sum_n r_n(f)^2 = \|f\|^2$.
* `norm_sub_trigPartialSum_sq`: $\|f - S_n f\|^2 = \|f\|^2 - \sum_{|m| \le n} r_m(f)^2$.
* `hasSum_sq_realFourierCoeff_compl`: $\sum_{|m| > n} r_m(f)^2 = \|f - S_n f\|^2$.
* `mem_trigPolyLE_iff`: $V_n$ consists of the linear combinations of the $t_m$ with $|m| \le n$.
* `linearIndependent_trigFun`: the functions $t_n$ are linearly independent.
* `finrank_trigPolyLE`: $\dim V_n = 2n + 1$.
* `exists_mem_span_trigFun_norm_sub_lt`: every continuous real function on $\mathbb{T}_T$ is a
  uniform limit of real trigonometric polynomials.
* `span_trigFun_closure_eq_top`: the span of $(t_n)$ is dense in the continuous real functions on
  $\mathbb{T}_T$.

## Implementation notes

* The system is indexed by $\mathbb{Z}$, so that one family carries the constant ($n = 0$), the
  cosines ($n > 0$) and the sines ($n < 0$). For $n < 0$, $t_n(x) = \sqrt{2} \sin(-2 \pi n x / T)$,
  so $t_{-j}(x) = \sqrt{2} \sin(2 \pi j x / T)$ for $j > 0$.
* The module is built on the identity $t_n(x) = \operatorname{Re}(w_n e_n(x))$ (`trigFun_apply`). It
  turns each computation about the real system into one about the complex exponentials, so that no
  argument of Mathlib is repeated: orthonormality reduces to $\int e_n \, d\mu = 0$ for $n \neq 0$,
  completeness reduces to the completeness of `fourierBasis` through
  `realFourierCoeff_eq_fourierCoeff`, and uniform density reduces to `span_fourier_closure_eq_top`
  by taking real parts, not to a second Stone–Weierstrass argument.
* The measure $\mu$ is `AddCircle.haarAddCircle`, and the hypothesis $T > 0$ is the instance
  `Fact (0 < T)`. An instance supplies `Fact (0 < 2 * π)` for the classical circle of circumference
  $2 \pi$.
* The space $V_n$ is defined here once, because it is the range of the Fourier projection and of
  trigonometric interpolation, and the Haar subspace of the trigonometric equioscillation theorem.
-/

open Complex MeasureTheory Set Submodule

open scoped ComplexConjugate ENNReal Real

variable {T : ℝ}

/-! ### The real trigonometric system -/

/-- The complex weight $w_n$ that turns the exponential $e_n(x) = \exp(2 \pi i n x / T)$ into the
member $t_n$ of the real trigonometric system:
$$w_n = \begin{cases} 1 & \text{if } n = 0, \\ \sqrt{2} & \text{if } n > 0, \\
  \sqrt{2} \, i & \text{if } n < 0. \end{cases}$$

The modulus of $w_n$ normalizes the system for the probability measure
`AddCircle.haarAddCircle`, and its argument selects a cosine or a sine through
$t_n(x) = \operatorname{Re}(w_n e_n(x))$ (`trigFun_apply`). -/
noncomputable def trigWeight (n : ℤ) : ℂ :=
  if n = 0 then 1 else if 0 < n then (√2 : ℝ) else (√2 : ℝ) * I

/-- The weight of index $0$ is $w_0 = 1$. -/
@[simp]
theorem trigWeight_zero : trigWeight 0 = 1 := ite_eq_left rfl

/-- For $n > 0$, the weight is $w_n = \sqrt{2}$. -/
theorem trigWeight_of_pos {n : ℤ} (hn : 0 < n) : trigWeight n = (√2 : ℝ) := by
  rw [trigWeight, ite_eq_right hn.ne', ite_eq_left hn]

/-- For $n < 0$, the weight is $w_n = \sqrt{2} \, i$. -/
theorem trigWeight_of_neg {n : ℤ} (hn : n < 0) : trigWeight n = (√2 : ℝ) * I := by
  rw [trigWeight, ite_eq_right hn.ne, ite_eq_right (by omega)]

/-- The **real trigonometric system** on the circle $\mathbb{T}_T$ of circumference $T$: for
$n \in \mathbb{Z}$, the continuous real function $t_n(x) = \operatorname{Re}(w_n e_n(x))$, where
$e_n(x) = \exp(2 \pi i n x / T)$. That is,
$$t_0 = 1, \qquad t_n(x) = \sqrt{2} \cos(2 \pi n x / T) \ (n > 0), \qquad t_n(x) = \sqrt{2}
  \sin(-2 \pi n x / T) \ (n < 0).$$

The system is normalized for the probability measure `AddCircle.haarAddCircle`. The index set
$\mathbb{Z}$ keeps in one family what the classical statement writes as three families. The
exponential $e_n$ is Mathlib's `fourier n`, and $w_n$ is `trigWeight n`. -/
noncomputable def trigFun (T : ℝ) (n : ℤ) : C(AddCircle T, ℝ) where
  toFun x := (trigWeight n * fourier n x).re
  continuous_toFun := Complex.continuous_re.comp (continuous_const.mul (fourier n).continuous)

/-- For $n \in \mathbb{Z}$ and $x \in \mathbb{T}_T$, $t_n(x) = \operatorname{Re}(w_n e_n(x))$. -/
@[simp]
theorem trigFun_apply (T : ℝ) (n : ℤ) (x : AddCircle T) :
    trigFun T n x = (trigWeight n * fourier n x).re :=
  rfl

/-- The member of index $0$ is the constant function $t_0 = 1$. -/
@[simp]
theorem trigFun_zero : trigFun T 0 = 1 := by
  ext x; simp

private theorem fourier_coe_apply_mul_I (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle T) = Complex.exp (((2 * π * n * x / T : ℝ) : ℂ) * I) := by
  rw [fourier_coe_apply]
  push_cast
  ring_nf

/-- For $n > 0$ and $x \in \mathbb{R}$, the member of index $n$ is the cosine
$t_n(x) = \sqrt{2} \cos(2 \pi n x / T)$. -/
theorem trigFun_coe_apply_of_pos {n : ℤ} (hn : 0 < n) (x : ℝ) :
    trigFun T n (x : AddCircle T) = √2 * Real.cos (2 * π * n * x / T) := by
  rw [trigFun_apply, trigWeight_of_pos hn, fourier_coe_apply_mul_I, re_ofReal_mul,
    exp_ofReal_mul_I_re]

/-- For $n < 0$ and $x \in \mathbb{R}$, the member of index $n$ is the sine
$t_n(x) = \sqrt{2} \sin(-2 \pi n x / T)$. For $n = -j$ with $j > 0$, this is
$\sqrt{2} \sin(2 \pi j x / T)$. -/
theorem trigFun_coe_apply_of_neg {n : ℤ} (hn : n < 0) (x : ℝ) :
    trigFun T n (x : AddCircle T) = √2 * Real.sin (-(2 * π * n * x / T)) := by
  rw [trigFun_apply, trigWeight_of_neg hn, fourier_coe_apply_mul_I, mul_assoc, re_ofReal_mul,
    Real.sin_neg, Complex.I_mul_re, exp_ofReal_mul_I_im]

/-- On the circle of circumference $2 \pi$, for $j > 0$ and $t \in \mathbb{R}$, the member of index
$j$ is $t_j(t) = \sqrt{2} \cos(j t)$. -/
theorem trigFun_coe_of_pos {j : ℤ} (hj : 0 < j) (t : ℝ) :
    trigFun (2 * π) j ↑t = √2 * Real.cos (j * t) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h : 2 * π * (j : ℝ) * t / (2 * π) = (j : ℝ) * t := by field_simp
  rw [trigFun_coe_apply_of_pos hj, h]

/-- On the circle of circumference $2 \pi$, for $j < 0$ and $t \in \mathbb{R}$, the member of index
$j$ is $t_j(t) = \sqrt{2} \sin(-j t)$. -/
theorem trigFun_coe_of_neg {j : ℤ} (hj : j < 0) (t : ℝ) :
    trigFun (2 * π) j ↑t = √2 * Real.sin (-(j : ℝ) * t) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h : -(2 * π * (j : ℝ) * t / (2 * π)) = -(j : ℝ) * t := by field_simp
  rw [trigFun_coe_apply_of_neg hj, h]

/-- For $T > 0$ and $n \in \mathbb{Z}$, the member $t_n$ of the real trigonometric system as an
element of $L^2(\mathbb{T}_T)$ for the Haar probability measure.

The hypothesis $T > 0$ is the instance `Fact (0 < T)`. -/
noncomputable abbrev trigLp (T : ℝ) [hT : Fact (0 < T)] (n : ℤ) :
    Lp ℝ 2 (@AddCircle.haarAddCircle T hT) :=
  ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ (trigFun T n)

/-- For $n \in \mathbb{Z}$ and every point $x$ of the circle, $|e_n(x)| = 1$. -/
theorem norm_fourier_apply (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- The circle of circumference $2 \pi$, on which the classical Fourier series lives, needs
$0 < 2 \pi$ as a `Fact` for its Haar measure and its compactness. -/
instance : Fact (0 < 2 * π) := ⟨by positivity⟩

section Circle

variable [hT : Fact (0 < T)]

open AddCircle

/-- For $T > 0$, the circle of circumference $T$ is infinite, because it is in bijection with the
interval $[0, T)$. -/
instance instInfiniteAddCircle : Infinite (AddCircle T) :=
  have : Infinite (Set.Ico (0 : ℝ) (0 + T)) := Set.Ico.infinite (by simpa using hT.out)
  (AddCircle.equivIco T 0).infinite_iff.2 this

/-! ### Integrals of the exponentials -/

private theorem integrable_const_mul_fourier (c : ℂ) (n : ℤ) :
    Integrable (fun x : AddCircle T => c * fourier n x) haarAddCircle :=
  Integrable.mul_bdd (c := 1)
    (integrable_const (μ := (haarAddCircle : Measure (AddCircle T))) c)
    (map_continuous (fourier n)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_fourier_apply n x).le)

/-- For $T > 0$ and $n \in \mathbb{Z}$, the integral of $e_n$ against the Haar probability measure
is $1$ if $n = 0$ and $0$ otherwise. -/
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

/-- For $T > 0$, the real trigonometric system $(t_n)_{n \in \mathbb{Z}}$ is **orthonormal** in
$L^2(\mathbb{T}_T)$ for the Haar probability measure. This is the orthonormality part of Theorem
1.3.13 of [han2009theoretical]. -/
theorem orthonormal_trigFun : Orthonormal ℝ (trigLp T) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [ContinuousMap.inner_toLp AddCircle.haarAddCircle (trigFun T i) (trigFun T j)]
  simpa using integral_trigFun_mul i j

/-! ### The real Fourier coefficients -/

/-- The **real Fourier coefficient** of index $n \in \mathbb{Z}$ of a function
$f \colon \mathbb{T}_T \to \mathbb{R}$, for $T > 0$:
$$r_n(f) = \int t_n(x) f(x) \, d\mu(x),$$
where $\mu$ is the Haar probability measure.

The classical coefficients $a_j$ and $b_j$, normalized so that the series reads
$a_0 / 2 + \sum_{j \ge 1} (a_j \cos + b_j \sin)$, are $a_j = \sqrt{2} \, r_j(f)$ and
$b_j = \sqrt{2} \, r_{-j}(f)$ for $j \ge 1$, and $a_0 = 2 r_0(f)$. The integral is a Bochner
integral, so $r_n(f) = 0$ when $t_n f$ is not integrable. -/
noncomputable def realFourierCoeff (f : AddCircle T → ℝ) (n : ℤ) : ℝ :=
  ∫ x : AddCircle T, trigFun T n x * f x ∂haarAddCircle

/-- The defining formula $r_n(f) = \int t_n(x) f(x) \, d\mu(x)$ of the real Fourier coefficient. -/
theorem realFourierCoeff_apply (f : AddCircle T → ℝ) (n : ℤ) :
    realFourierCoeff f n = ∫ x : AddCircle T, trigFun T n x * f x ∂haarAddCircle :=
  rfl

/-- The coefficient of index $0$ is the mean value: $r_0(f) = \int f \, d\mu$. -/
@[simp]
theorem realFourierCoeff_zero (f : AddCircle T → ℝ) :
    realFourierCoeff f 0 = ∫ x : AddCircle T, f x ∂haarAddCircle := by
  simp [realFourierCoeff_apply]

/-- The real Fourier coefficients of a member of the real trigonometric system: for
$i, j \in \mathbb{Z}$, $r_j(t_i)$ is $1$ if $i = j$ and $0$ otherwise.

This is `orthonormal_trigFun` for continuous functions instead of $L^2$. It makes the Fourier
projection of `Numlib.Approximation.Trigonometric` fix the trigonometric polynomials. -/
@[simp]
theorem realFourierCoeff_trigFun (i j : ℤ) :
    realFourierCoeff (trigFun T i) j = if i = j then 1 else 0 :=
  integral_trigFun_mul i j

/-- The complex Fourier coefficients of a real function are conjugate symmetric: for
$f \colon \mathbb{T}_T \to \mathbb{R}$ and $n \in \mathbb{Z}$, $c_{-n}(f) = \overline{c_n(f)}$,
where $c_n$ is Mathlib's `fourierCoeff`. -/
theorem fourierCoeff_ofReal_neg (f : AddCircle T → ℝ) (n : ℤ) :
    fourierCoeff (fun x => (f x : ℂ)) (-n) = conj (fourierCoeff (fun x => (f x : ℂ)) n) := by
  have h : ∀ x : AddCircle T, conj (fourier (-n) x) = fourier n x := by
    intro x; rw [← fourier_neg, neg_neg]
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, neg_neg, h]

/-- The relation between the real and the complex Fourier coefficients. Let $T > 0$ and let
$f \colon \mathbb{T}_T \to \mathbb{R}$ be integrable for the Haar probability measure $\mu$.
Then for every $n \in \mathbb{Z}$,
$$r_n(f) = \operatorname{Re}\bigl(w_n \, c_{-n}(f)\bigr),$$
where $c_m(f) = \int e_{-m} f \, d\mu$ is the complex Fourier coefficient.

Since $w_n$ is $1$, $\sqrt{2}$ or $\sqrt{2} \, i$ according to the sign of $n$, the identity
says that $r_0(f)$ is the real part of $c_0(f)$, that the cosine coefficients are $\sqrt{2}$
times real parts of complex coefficients, and that the sine coefficients are $\sqrt{2}$ times
imaginary parts; see `realFourierCoeff_of_pos`, `realFourierCoeff_of_neg` and
`fourierCoeff_ofReal`. The complex coefficient $c_m(f)$ is Mathlib's `fourierCoeff` of the
complex function $x \mapsto f(x)$. -/
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

/-- The cosine coefficients: let $f \colon \mathbb{T}_T \to \mathbb{R}$ be integrable and let
$n > 0$. Then $r_n(f) = \sqrt{2} \operatorname{Re} c_n(f)$. -/
theorem realFourierCoeff_of_pos {f : AddCircle T → ℝ} (hf : Integrable f haarAddCircle)
    {n : ℤ} (hn : 0 < n) :
    realFourierCoeff f n = √2 * (fourierCoeff (fun x => (f x : ℂ)) n).re := by
  rw [realFourierCoeff_eq_fourierCoeff hf, trigWeight_of_pos hn, re_ofReal_mul,
    fourierCoeff_ofReal_neg, Complex.conj_re]

/-- The sine coefficients: let $f \colon \mathbb{T}_T \to \mathbb{R}$ be integrable and let $n < 0$.
Then $r_n(f) = \sqrt{2} \operatorname{Im} c_n(f)$. -/
theorem realFourierCoeff_of_neg {f : AddCircle T → ℝ} (hf : Integrable f haarAddCircle)
    {n : ℤ} (hn : n < 0) :
    realFourierCoeff f n = √2 * (fourierCoeff (fun x => (f x : ℂ)) n).im := by
  rw [realFourierCoeff_eq_fourierCoeff hf, trigWeight_of_neg hn, mul_assoc, re_ofReal_mul,
    fourierCoeff_ofReal_neg]
  simp [Complex.mul_re]

/-- The classical form of the relation between the coefficients: let
$f \colon \mathbb{T}_T \to \mathbb{R}$ be integrable and let $n > 0$. Then
$$c_n(f) = \frac{r_n(f) - i \, r_{-n}(f)}{\sqrt{2}}.$$

With $a_n = \sqrt{2} \, r_n(f)$ and $b_n = \sqrt{2} \, r_{-n}(f)$, this is the classical formula
$c_n = (a_n - i b_n) / 2$. -/
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

/-- For $f \in L^2(\mathbb{T}_T)$ and $n \in \mathbb{Z}$, the inner product $\langle t_n, f \rangle$
in $L^2$ is the real Fourier coefficient $r_n(f)$. -/
theorem inner_trigLp (n : ℤ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    inner ℝ (trigLp T n) f = realFourierCoeff (f : AddCircle T → ℝ) n := by
  rw [MeasureTheory.L2.inner_def, realFourierCoeff_apply]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (𝕜 := ℝ) haarAddCircle
    (trigFun T n)] with x hx
  rw [hx, RCLike.inner_apply]
  simp [mul_comm]

/-- **Completeness of the real trigonometric system**: for $T > 0$, the orthogonal complement in
$L^2(\mathbb{T}_T)$ of the span of the functions $t_n$, $n \in \mathbb{Z}$, is $\{0\}$.

A function that is orthogonal to every $t_n$ has all its complex Fourier coefficients equal to
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
  set F : Lp ℂ 2 (@haarAddCircle T hT) := Complex.ofRealCLM.compLp f
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

/-- For $T > 0$, the real trigonometric system $(t_n)_{n \in \mathbb{Z}}$ as a **Hilbert basis** of
$L^2(\mathbb{T}_T)$ for the Haar probability measure. This is Theorem 1.3.13 of
[han2009theoretical].

It is built from `orthonormal_trigFun` and `orthogonal_span_trigLp_eq_bot`. -/
noncomputable def trigBasis (T : ℝ) [hT : Fact (0 < T)] :
    HilbertBasis ℤ ℝ (Lp ℝ 2 (@haarAddCircle T hT)) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_trigFun orthogonal_span_trigLp_eq_bot

/-- The members of the Hilbert basis `trigBasis T` are the elements `trigLp T n`. -/
@[simp]
theorem coe_trigBasis : ⇑(trigBasis T) = trigLp T :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- For $f \in L^2(\mathbb{T}_T)$ and $n \in \mathbb{Z}$, the coordinate of index $n$ of $f$ in the
Hilbert basis `trigBasis T` is the real Fourier coefficient $r_n(f)$. -/
theorem trigBasis_repr (f : Lp ℝ 2 (@haarAddCircle T hT)) (n : ℤ) :
    (trigBasis T).repr f n = realFourierCoeff (f : AddCircle T → ℝ) n := by
  rw [HilbertBasis.repr_apply_apply, coe_trigBasis, inner_trigLp]

/-- **Convergence of the Fourier series in $L^2$**: for $T > 0$ and $f \in L^2(\mathbb{T}_T)$,
$$f = \sum_{n \in \mathbb{Z}} r_n(f) \, t_n,$$
where the series converges unconditionally in $L^2$. This is the case $p = 2$ of the classical
$L^p$ convergence theorem, and Example 1.3.15 of [han2009theoretical]. -/
theorem hasSum_trigSeries (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    HasSum (fun n : ℤ => realFourierCoeff (f : AddCircle T → ℝ) n • trigLp T n) f := by
  simpa only [trigBasis_repr, coe_trigBasis] using (trigBasis T).hasSum_repr f

/-- **Parseval's identity** in real form: for $T > 0$ and $f \in L^2(\mathbb{T}_T)$,
$$\sum_{n \in \mathbb{Z}} r_n(f)^2 = \|f\|^2.$$

The sum is a Lean `tsum`. The family is summable by `hasSum_sq_realFourierCoeff`. -/
theorem tsum_sq_realFourierCoeff (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    ∑' n : ℤ, realFourierCoeff (f : AddCircle T → ℝ) n ^ 2 = ‖f‖ ^ 2 := by
  have h := (trigBasis T).tsum_inner_mul_inner f f
  simp only [coe_trigBasis, inner_trigLp, real_inner_self_eq_norm_sq] at h
  rw [← h]
  refine tsum_congr fun n => ?_
  rw [real_inner_comm, inner_trigLp]
  ring

/-- **Parseval's identity** with summability: for $f \in L^2(\mathbb{T}_T)$, the family
$(r_n(f)^2)_{n \in \mathbb{Z}}$ is summable, and its sum is $\|f\|^2$. -/
theorem hasSum_sq_realFourierCoeff (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    HasSum (fun n : ℤ => realFourierCoeff (f : AddCircle T → ℝ) n ^ 2) (‖f‖ ^ 2) := by
  have h := (trigBasis T).hasSum_inner_mul_inner f f
  simp only [coe_trigBasis, real_inner_self_eq_norm_sq] at h
  refine h.congr_fun fun n => ?_
  have h1 : inner ℝ f (trigLp T n) = realFourierCoeff (f : AddCircle T → ℝ) n := by
    rw [← inner_trigLp n f]
    exact real_inner_comm _ _
  rw [h1, inner_trigLp, sq]

/-! ### The partial sums of the Fourier series -/

/-- The **partial sum** of the real Fourier series of $f \in L^2(\mathbb{T}_T)$ of order
$n \in \mathbb{N}$:
$$S_n f = \sum_{m = -n}^{n} r_m(f) \, t_m.$$

It is the orthogonal projection of $f$ onto the trigonometric polynomials of degree at most $n$.
For $T = 2 \pi$, in the classical coefficients, it is $a_0 / 2 + \sum_{j = 1}^{n} (a_j \cos(j
x) + b_j \sin(j x))$. -/
noncomputable def trigPartialSum (n : ℕ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    Lp ℝ 2 (@haarAddCircle T hT) :=
  ∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), realFourierCoeff (f : AddCircle T → ℝ) m • trigLp T m

/-- The defining formula of the partial sum: $S_n f = \sum_{m = -n}^{n} r_m(f) \, t_m$. -/
theorem trigPartialSum_def (n : ℕ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    trigPartialSum n f
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
          realFourierCoeff (f : AddCircle T → ℝ) m • trigLp T m :=
  rfl

/-- The partial sum satisfies $\langle S_n f, f \rangle = \sum_{|m| \le n} r_m(f)^2$. -/
private theorem inner_trigPartialSum_left (n : ℕ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    inner ℝ (trigPartialSum n f) f
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), realFourierCoeff (f : AddCircle T → ℝ) m ^ 2 := by
  rw [trigPartialSum_def, sum_inner]
  exact Finset.sum_congr rfl fun m _ => by rw [real_inner_smul_left, inner_trigLp, sq]

private theorem norm_trigPartialSum_sq (n : ℕ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    ‖trigPartialSum n f‖ ^ 2
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), realFourierCoeff (f : AddCircle T → ℝ) m ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, trigPartialSum_def, sum_inner]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [real_inner_smul_left, orthonormal_trigFun.inner_right_sum _ hm, sq]

/-- **The $L^2$ error of the partial sum**: for $T > 0$, $f \in L^2(\mathbb{T}_T)$ and
$n \in \mathbb{N}$,
$$\|f - S_n f\|^2 = \|f\|^2 - \sum_{|m| \le n} r_m(f)^2.$$

Subtracting the partial sum removes exactly the coefficients that it keeps. -/
theorem norm_sub_trigPartialSum_sq (n : ℕ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    ‖f - trigPartialSum n f‖ ^ 2
      = ‖f‖ ^ 2 - ∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
          realFourierCoeff (f : AddCircle T → ℝ) m ^ 2 := by
  rw [norm_sub_sq_real, real_inner_comm, inner_trigPartialSum_left, norm_trigPartialSum_sq]
  ring

/-- **The tail form of Parseval's identity**: for $T > 0$, $f \in L^2(\mathbb{T}_T)$ and
$n \in \mathbb{N}$, the squares $r_m(f)^2$ of the coefficients with $|m| > n$ form a summable
family, and
$$\sum_{|m| > n} r_m(f)^2 = \|f - S_n f\|^2.$$

This is Parseval's identity with the finitely many coefficients of the partial sum taken out.
The Lean family is indexed by all of $\mathbb{Z}$ and is $0$ at the indices $m$ with
$|m| \le n$. -/
theorem hasSum_sq_realFourierCoeff_compl (n : ℕ) (f : Lp ℝ 2 (@haarAddCircle T hT)) :
    HasSum (fun m : ℤ =>
        if m.natAbs ≤ n then 0 else realFourierCoeff (f : AddCircle T → ℝ) m ^ 2)
      (‖f - trigPartialSum n f‖ ^ 2) := by
  have hmem : ∀ m : ℤ, m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) ↔ m.natAbs ≤ n := by
    intro m
    rw [Finset.mem_Icc]
    omega
  have hfin : HasSum (fun m : ℤ => if m.natAbs ≤ n then
      realFourierCoeff (f : AddCircle T → ℝ) m ^ 2 else 0)
      (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), realFourierCoeff (f : AddCircle T → ℝ) m ^ 2) := by
    have heq : (∑ b ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        if b.natAbs ≤ n then realFourierCoeff (f : AddCircle T → ℝ) b ^ 2 else 0)
        = ∑ b ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), realFourierCoeff (f : AddCircle T → ℝ) b ^ 2 :=
      Finset.sum_congr rfl fun m hm => ite_eq_left ((hmem m).mp hm)
    rw [← heq]
    exact hasSum_sum_of_ne_finset_zero fun m hm => ite_eq_right fun h => hm ((hmem m).mpr h)
  have hsub := (hasSum_sq_realFourierCoeff f).sub hfin
  rw [← norm_sub_trigPartialSum_sq] at hsub
  refine hsub.congr_fun fun m => ?_
  by_cases hm : m.natAbs ≤ n
  · rw [ite_eq_left hm, ite_eq_left hm, sub_self]
  · rw [ite_eq_right hm, ite_eq_right hm, sub_zero]

end Circle

/-! ### The trigonometric polynomials of degree at most $n$ -/

/-- The space $V_n$ of **trigonometric polynomials of degree at most $n$** on the circle
$\mathbb{T}_T$ of circumference $T$: the subspace of the continuous real functions on
$\mathbb{T}_T$ spanned by the functions $t_m$ with $|m| \le n$. That is, $V_n$ is spanned by the
constant together with the cosines and the sines of the frequencies $1, \dots, n$.

This is the space onto which the Fourier projection and trigonometric interpolation project, and
the Haar subspace of the trigonometric equioscillation theorem. For $T > 0$ it has dimension
$2n + 1$ (`finrank_trigPolyLE`). -/
noncomputable def trigPolyLE (T : ℝ) (n : ℕ) : Submodule ℝ C(AddCircle T, ℝ) :=
  span ℝ (trigFun T '' Set.Icc (-(n : ℤ)) n)

variable {n : ℕ}

/-- For $m \in \mathbb{Z}$ and $n \in \mathbb{N}$, $-n \le m \le n$ if and only if $|m| \le n$. -/
theorem mem_Icc_iff_natAbs_le {m : ℤ} : m ∈ Set.Icc (-(n : ℤ)) n ↔ m.natAbs ≤ n := by
  rw [Set.mem_Icc]
  omega

/-- For $m \in \mathbb{Z}$ with $|m| \le n$, the function $t_m$ lies in $V_n$. -/
theorem trigFun_mem_trigPolyLE {m : ℤ} (hm : m.natAbs ≤ n) : trigFun T m ∈ trigPolyLE T n :=
  subset_span ⟨m, mem_Icc_iff_natAbs_le.2 hm, rfl⟩

/-- A continuous real function $f$ on $\mathbb{T}_T$ lies in $V_n$ if and only if there are
coefficients $c \colon \mathbb{Z} \to \mathbb{R}$ with
$$f = \sum_{m = -n}^{n} c_m t_m.$$
-/
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

/-- The spaces $V_n$ increase with $n$: for $m \le n$, $V_m \subseteq V_n$. -/
theorem trigPolyLE_mono {m n : ℕ} (h : m ≤ n) : trigPolyLE T m ≤ trigPolyLE T n :=
  span_mono (Set.image_mono fun _j hj => mem_Icc_iff_natAbs_le.2
    ((mem_Icc_iff_natAbs_le.1 hj).trans h))

instance : FiniteDimensional ℝ (trigPolyLE T n) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_Icc _ _).image _)

section Circle

variable [hT : Fact (0 < T)]

/-- For $T > 0$, the functions $t_n$, $n \in \mathbb{Z}$, are **linearly independent** in the space
of continuous real functions on $\mathbb{T}_T$.

They are orthonormal in $L^2$, and the map from the continuous functions to $L^2$ is linear. -/
theorem linearIndependent_trigFun : LinearIndependent ℝ (trigFun T) :=
  orthonormal_trigFun.linearIndependent.of_comp
    (ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ).toLinearMap

/-- **Dimension of the trigonometric polynomials**: for $T > 0$ and $n \in \mathbb{N}$,
$$\dim V_n = 2n + 1.$$
A basis is the constant, together with a cosine and a sine for each frequency $1, \dots, n$. -/
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

/-! ### Uniform density of the trigonometric polynomials -/

section Density

/-- The real part, as a real-linear map from the continuous complex functions on $X$ to the
continuous real functions on $X$. -/
private noncomputable def reMap (X : Type*) [TopologicalSpace X] : C(X, ℂ) →ₗ[ℝ] C(X, ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ X).toLinearMap

/-- The imaginary part, as a real-linear map from the continuous complex functions on $X$ to the
continuous real functions on $X$. -/
private noncomputable def imMap (X : Type*) [TopologicalSpace X] : C(X, ℂ) →ₗ[ℝ] C(X, ℝ) :=
  (Complex.imCLM.compLeftContinuous ℝ X).toLinearMap

@[simp]
private theorem reMap_apply {X : Type*} [TopologicalSpace X] (P : C(X, ℂ)) (x : X) :
    reMap X P x = (P x).re :=
  rfl

@[simp]
private theorem imMap_apply {X : Type*} [TopologicalSpace X] (P : C(X, ℂ)) (x : X) :
    imMap X P x = (P x).im :=
  rfl

/-- The real and the imaginary parts of the exponential $e_n$ lie in the span of the real
trigonometric system. -/
private theorem reMap_imMap_fourier_mem (n : ℤ) :
    reMap (AddCircle T) (fourier n) ∈ span ℝ (range (trigFun T)) ∧
      imMap (AddCircle T) (fourier n) ∈ span ℝ (range (trigFun T)) := by
  have hgen : ∀ m : ℤ, trigFun T m ∈ span ℝ (range (trigFun T)) := fun m => subset_span ⟨m, rfl⟩
  have hre : ∀ m : ℤ, 0 < m →
      reMap (AddCircle T) (fourier m) = (√2 : ℝ)⁻¹ • trigFun T m := by
    intro m hm
    ext x
    rw [reMap_apply, ContinuousMap.smul_apply, trigFun_apply, trigWeight_of_pos hm, re_ofReal_mul,
      smul_eq_mul, inv_mul_cancel_left₀ (by positivity : (√2 : ℝ) ≠ 0)]
  have him : ∀ m : ℤ, 0 < m →
      imMap (AddCircle T) (fourier m) = (√2 : ℝ)⁻¹ • trigFun T (-m) := by
    intro m hm
    ext x
    rw [imMap_apply, ContinuousMap.smul_apply, trigFun_apply, trigWeight_of_neg (by omega),
      mul_assoc, re_ofReal_mul, fourier_neg, smul_eq_mul, Complex.I_mul_re, Complex.conj_im,
      neg_neg, inv_mul_cancel_left₀ (by positivity : (√2 : ℝ) ≠ 0)]
  have hconj : ∀ m : ℤ, reMap (AddCircle T) (fourier (-m)) = reMap (AddCircle T) (fourier m) ∧
      imMap (AddCircle T) (fourier (-m)) = -imMap (AddCircle T) (fourier m) := by
    refine fun m => ⟨?_, ?_⟩
    · ext x
      rw [reMap_apply, reMap_apply, fourier_neg, Complex.conj_re]
    · ext x
      rw [ContinuousMap.neg_apply, imMap_apply, imMap_apply, fourier_neg, Complex.conj_im]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨hr, hi⟩ := hconj (-n)
    rw [neg_neg] at hr hi
    refine ⟨?_, ?_⟩
    · rw [hr, hre (-n) (by omega)]
      exact smul_mem _ _ (hgen _)
    · rw [hi, him (-n) (by omega)]
      exact neg_mem (smul_mem _ _ (hgen _))
  · refine ⟨?_, ?_⟩
    · have : reMap (AddCircle T) (fourier (0 : ℤ)) = trigFun T 0 := by
        ext x; simp
      rw [this]; exact hgen 0
    · have : imMap (AddCircle T) (fourier (0 : ℤ)) = 0 := by
        ext x; simp
      rw [this]; exact zero_mem _
  · exact ⟨by rw [hre n hn]; exact smul_mem _ _ (hgen _),
      by rw [him n hn]; exact smul_mem _ _ (hgen _)⟩

/-- The real and the imaginary parts of a complex trigonometric polynomial are real trigonometric
polynomials; the two parts are proved together, because a complex scalar multiple mixes them. -/
private theorem reMap_imMap_mem_of_mem_span {P : C(AddCircle T, ℂ)}
    (hP : P ∈ span ℂ (range (fourier (T := T)))) :
    reMap (AddCircle T) P ∈ span ℝ (range (trigFun T)) ∧
      imMap (AddCircle T) P ∈ span ℝ (range (trigFun T)) := by
  induction hP using Submodule.span_induction with
  | mem P hP => obtain ⟨n, rfl⟩ := hP; exact reMap_imMap_fourier_mem n
  | zero => simp only [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
  | add P Q _ _ ihP ihQ =>
      rw [map_add, map_add]
      exact ⟨add_mem ihP.1 ihQ.1, add_mem ihP.2 ihQ.2⟩
  | smul c P _ ih =>
      have hre : reMap (AddCircle T) (c • P)
          = c.re • reMap (AddCircle T) P - c.im • imMap (AddCircle T) P := by
        ext x; simp [Complex.mul_re]
      have him : imMap (AddCircle T) (c • P)
          = c.re • imMap (AddCircle T) P + c.im • reMap (AddCircle T) P := by
        ext x; simp [Complex.mul_im]
      rw [hre, him]
      exact ⟨sub_mem (smul_mem _ _ ih.1) (smul_mem _ _ ih.2),
        add_mem (smul_mem _ _ ih.2) (smul_mem _ _ ih.1)⟩

variable [hT : Fact (0 < T)]

/-- **Uniform density of the real trigonometric polynomials**: let $T > 0$, let $f$ be a continuous
real function on $\mathbb{T}_T$, and let $\varepsilon > 0$. Then there is a function $p$ in the
span of the real trigonometric system $(t_n)_{n \in \mathbb{Z}}$ with
$\|p - f\|_\infty < \varepsilon$.

The proof takes real parts in the density of the complex exponentials,
`span_fourier_closure_eq_top`. The real part of a complex trigonometric polynomial is a real
trigonometric polynomial, and taking real parts does not increase the uniform norm. -/
theorem exists_mem_span_trigFun_norm_sub_lt (f : C(AddCircle T, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ span ℝ (range (trigFun T)), ‖p - f‖ < ε := by
  -- the complexification of `f`
  set F : C(AddCircle T, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    with hF
  have hFtop : F ∈ (span ℂ (range (fourier (T := T)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hFtop
  obtain ⟨P, hPmem, hPdist⟩ := hFtop ε hε
  refine ⟨reMap (AddCircle T) P, (reMap_imMap_mem_of_mem_span hPmem).1, ?_⟩
  have hle : ‖reMap (AddCircle T) P - f‖ ≤ ‖P - F‖ := by
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
    have h1 : (reMap (AddCircle T) P - f) x = (P x - F x).re := by
      simp [hF, Complex.sub_re]
    rw [h1, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (ContinuousMap.norm_coe_le_norm (P - F) x)
  rw [dist_eq_norm, norm_sub_rev] at hPdist
  exact lt_of_le_of_lt hle hPdist

/-- For $T > 0$, the span of the real trigonometric system is dense in the space of continuous real
functions on $\mathbb{T}_T$ with the uniform norm. This is the real form of Mathlib's
`span_fourier_closure_eq_top`. -/
theorem span_trigFun_closure_eq_top : (span ℝ (range (trigFun T))).topologicalClosure = ⊤ := by
  rw [← Submodule.dense_iff_topologicalClosure_eq_top]
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp, hpf⟩ := exists_mem_span_trigFun_norm_sub_lt f hε
  exact ⟨p, hp, by rwa [dist_eq_norm, norm_sub_rev]⟩

end Density
