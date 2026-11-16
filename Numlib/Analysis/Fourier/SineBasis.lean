/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier`, beside the cosine system of
`Numlib/Analysis/Fourier/CosineBasis.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Fourier.CosineBasis

/-!
# The half-range sine system as a Hilbert basis of $L^2(0, \pi)$ and of $L^2(0, 1)$

The functions $\sqrt{2/\pi} \sin((n + 1) x)$, $n \ge 0$, form an orthonormal and complete system in
$L^2(0, \pi)$, and their rescalings $\sqrt{2} \sin((n + 1) \pi x)$ form a Hilbert basis of
$L^2(0, 1)$. These functions are the eigenfunctions of $-d^2/dx^2$ on an interval with Dirichlet
boundary conditions; see [brezis2011functional], §8.6, the Example after Theorem 8.22. The module
also defines the sine polynomials $\sum_{j < n} c_j \sin((j + 1) x)$ on $[0, \pi]$ and proves that
the functions $\sin((k + 1) x)$ are linearly independent.

## Main definitions

* `sinLp`: the half-range sine system $\sqrt{2/\pi} \sin((k + 1) x)$ in $L^2(0, \pi)$.
* `sinBasis`: the half-range sine system as a Hilbert basis of $L^2(0, \pi)$.
* `sinUnitLp`: the sine system $\sqrt{2} \sin((k + 1) \pi x)$ in $L^2(0, 1)$.
* `sinBasisUnit`: the sine system as a Hilbert basis of $L^2(0, 1)$.
* `sinePolynomial`: the sine polynomial $\sum_{j < n} c_j \sin((j + 1) x)$ as a continuous function
  on $[0, \pi]$.

## Main results

* `orthonormal_sinLp`: the half-range sine system is orthonormal in $L^2(0, \pi)$.
* `orthogonal_span_sinLp_eq_bot`: the half-range sine system is complete in $L^2(0, \pi)$.
* `measurePreserving_div_pi`: the map $y \mapsto y / \pi$ carries Lebesgue measure on $[0, \pi]$ to
  $\pi$ times Lebesgue measure on $(0, 1)$.
* `orthonormal_sinUnitLp`: the sine system is orthonormal in $L^2(0, 1)$.
* `orthogonal_span_sinUnitLp_eq_bot`: the sine system is complete in $L^2(0, 1)$.
* `mem_span_sinMap_iff`: the span of the functions $\sin((k + 1) x)$ consists of the sine
  polynomials.
* `linearIndependent_sinMap`: the functions $\sin((k + 1) x)$ on $[0, \pi]$ are linearly
  independent.

## Proof outline

Completeness on $(0, \pi)$ follows from the completeness of the half-range cosine system of
`Numlib.Analysis.Fourier.CosineBasis` by a product-to-sum identity. If $f \perp \sin((n + 1) x)$ for
every $n$, then $g = f \sin$ satisfies
$$2 \langle g, \cos(m x) \rangle = \langle f, \sin((m + 1) x) \rangle + \langle f, \sin((1 - m) x)
  \rangle = 0$$
for every $m$. So $g = 0$ by the completeness of the cosines, and $f = 0$ because $\sin$ vanishes on
$[0, \pi]$ only at the endpoints. The basis on $(0, 1)$ comes from the basis on $(0, \pi)$ by the
change of variables $x \mapsto x / \pi$, which carries $L^2(0, \pi)$ to $L^2(0, 1)$ up to the factor
$\pi$.

## Implementation notes

* $L^2(0, \pi)$ is `Lp ℝ 2 halfRangeMeasure`, a space of classes of functions on the subtype
  `Icc 0 π`. The measure `halfRangeMeasure` is Lebesgue measure pulled back to this subtype.
* $L^2(0, 1)$ is `Lp ℝ 2 (volume.restrict (Ioo 0 1))`, a space of classes of functions on
  $\mathbb{R}$.
* The systems are indexed by $\mathbb{N}$, and the index $k$ gives the frequency $k + 1$.
-/

open MeasureTheory Set Submodule

open scoped ENNReal Real

noncomputable section

/-! ### The sine system on $[0, \pi]$ -/

/-- The **raw sine system**: for $k \in \mathbb{N}$, the continuous function
$x \mapsto \sin((k + 1) x)$ on $[0, \pi]$. -/
def sinMap (k : ℕ) : C(Icc (0 : ℝ) π, ℝ) :=
  ⟨fun x ↦ Real.sin ((k + 1) * x), by fun_prop⟩

/-- The **normalized sine system**: for $k \in \mathbb{N}$, the continuous function
$x \mapsto \sqrt{2/\pi} \sin((k + 1) x)$ on $[0, \pi]$. -/
def sinFun (k : ℕ) : C(Icc (0 : ℝ) π, ℝ) := √(2 / π) • sinMap k

/-- The **half-range sine system** in $L^2(0, \pi)$: for $k \in \mathbb{N}$, the class of the
function $x \mapsto \sqrt{2/\pi} \sin((k + 1) x)$ on $[0, \pi]$.

The space $L^2(0, \pi)$ is `Lp ℝ 2 halfRangeMeasure`. The element is the class of the continuous
function `sinFun k`. -/
def sinLp (k : ℕ) : Lp ℝ 2 halfRangeMeasure :=
  ContinuousMap.toLp 2 halfRangeMeasure ℝ (sinFun k)

/-- For $x \in [0, \pi]$, the value of `sinMap k` at $x$ is $\sin((k + 1) x)$. -/
theorem sinMap_apply (k : ℕ) (x : Icc (0 : ℝ) π) : sinMap k x = Real.sin ((k + 1) * (x : ℝ)) :=
  rfl

/-- For $x \in [0, \pi]$, the value of `sinFun k` at $x$ is $\sqrt{2/\pi} \sin((k + 1) x)$. -/
theorem sinFun_apply (k : ℕ) (x : Icc (0 : ℝ) π) :
    sinFun k x = √(2 / π) * Real.sin ((k + 1) * (x : ℝ)) :=
  rfl

/-- In $L^2(0, \pi)$, the element `sinLp k` equals the class of `sinMap k` multiplied by
$\sqrt{2/\pi}$. -/
theorem sinLp_eq_smul (k : ℕ) :
    sinLp k = √(2 / π) • ContinuousMap.toLp 2 halfRangeMeasure ℝ (sinMap k) := by
  rw [sinLp, sinFun, map_smul]

/-- The normalizing constant is nonzero: $\sqrt{2/\pi} \neq 0$. -/
theorem sqrt_two_div_pi_ne_zero : √(2 / π) ≠ 0 :=
  (Real.sqrt_pos.2 (by positivity)).ne'

/-- The function `sinFun k` represents the class `sinLp k`: the two agree almost everywhere on
$[0, \pi]$. -/
theorem coeFn_sinLp (k : ℕ) : (sinLp k : Icc (0 : ℝ) π → ℝ) =ᵐ[halfRangeMeasure] sinFun k :=
  ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (𝕜 := ℝ) halfRangeMeasure (sinFun k)

/-- For $j, k \in \mathbb{N}$, the inner product of `sinLp j` and `sinLp k` in $L^2(0, \pi)$ is $1$
if $j = k$ and $0$ otherwise. -/
theorem inner_sinLp (j k : ℕ) : inner ℝ (sinLp j) (sinLp k) = if j = k then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have key : ∫ x, inner ℝ ((sinLp j : Icc (0 : ℝ) π → ℝ) x) ((sinLp k : Icc (0 : ℝ) π → ℝ) x)
        ∂halfRangeMeasure
      = ∫ x : Icc (0 : ℝ) π, (√(2 / π) * √(2 / π)) *
          (Real.sin ((j + 1) * (x : ℝ)) * Real.sin ((k + 1) * (x : ℝ))) ∂halfRangeMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sinLp j, coeFn_sinLp k] with x hxj hxk
    rw [hxj, hxk, RCLike.inner_apply, sinFun_apply, sinFun_apply, conj_trivial]
    ring
  have hint := integral_sin_nat_mul_sin_nat_mul (j + 1) (k + 1)
  push_cast at hint
  rw [key, integral_const_mul,
    integral_halfRangeMeasure (fun t ↦ Real.sin ((j + 1) * t) * Real.sin ((k + 1) * t)), hint,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 / π)]
  by_cases hjk : j = k
  · subst hjk
    simp only [ite_true]
    field_simp
  · simp [hjk]

/-- The half-range sine system $(\sqrt{2/\pi} \sin((k + 1) x))_{k \ge 0}$ is **orthonormal** in
$L^2(0, \pi)$. -/
theorem orthonormal_sinLp : Orthonormal ℝ sinLp := orthonormal_iff_ite.2 inner_sinLp

/-- For almost every $x \in [0, \pi]$ with respect to Lebesgue measure, $\sin x \neq 0$.

The only zeros of $\sin$ on $[0, \pi]$ are the endpoints $0$ and $\pi$, and they form a null
set. -/
theorem ae_sin_ne_zero : ∀ᵐ x : Icc (0 : ℝ) π ∂halfRangeMeasure, Real.sin x ≠ 0 := by
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_Icc (a := (0 : ℝ)) (b := π))
  rw [ae_iff]
  refine measure_mono_null (t := ((↑) : Icc (0 : ℝ) π → ℝ) ⁻¹' {0, π}) (fun x hx ↦ ?_) ?_
  · simp only [mem_ofPred_eq, not_not] at hx
    rcases eq_or_lt_of_le x.2.1 with h0 | h0
    · exact Or.inl h0.symm
    rcases eq_or_lt_of_le x.2.2 with hπ | hπ
    · exact Or.inr hπ
    exact absurd hx (Real.sin_pos_of_pos_of_lt_pi h0 hπ).ne'
  · rw [halfRangeMeasure, hemb.comap_apply]
    exact measure_mono_null (image_preimage_subset _ _)
      (((finite_singleton π).insert 0).measure_zero volume)

/-- Let $f \in L^2(0, \pi)$ and let $h$ be a continuous function on $[0, \pi]$. Then the product
$f h$ is integrable on $[0, \pi]$. -/
theorem integrable_mul_continuousMap (f : Lp ℝ 2 halfRangeMeasure) (h : C(Icc (0 : ℝ) π, ℝ)) :
    Integrable (fun x ↦ (f : Icc (0 : ℝ) π → ℝ) x * h x) halfRangeMeasure := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Icc (0 : ℝ) π)).exists_bound_of_continuousOn
    h.continuous.continuousOn
  exact (Lp.memLp f).integrable (by norm_num) |>.mul_bdd (c := C)
    h.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ hC x (mem_univ x))

/-- **Completeness of the half-range sine system** in $L^2(0, \pi)$: the orthogonal complement of
the span of the functions $\sqrt{2/\pi} \sin((n + 1) x)$, $n \ge 0$, is $\{0\}$. Equivalently, a
function $f \in L^2(0, \pi)$ that is orthogonal to every $\sin((n + 1) x)$ is zero.

The proof multiplies $f$ by $\sin x$. By the identity
$$2 \sin x \cos(m x) = \sin((m + 1) x) + \sin((1 - m) x),$$
the product $f \sin x$ is orthogonal to every $\cos(m x)$ with $m \ge 0$. It is therefore zero
by the completeness of the half-range cosine system, and $f$ is zero because $\sin x \neq 0$ for
almost every $x$ (`ae_sin_ne_zero`). -/
theorem orthogonal_span_sinLp_eq_bot : (span ℝ (Set.range sinLp))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  -- the hypothesis, as integrals
  have hsin : ∀ n : ℕ,
      ∫ x : Icc (0 : ℝ) π, (f : Icc (0 : ℝ) π → ℝ) x * Real.sin ((n + 1) * x) ∂halfRangeMeasure
        = 0 := by
    intro n
    have h1 : inner ℝ f (sinLp n) = 0 :=
      (Submodule.mem_orthogonal' _ _).mp hf _ (subset_span ⟨n, rfl⟩)
    rw [MeasureTheory.L2.inner_def] at h1
    have h2 : ∫ x, inner ℝ ((f : Icc (0 : ℝ) π → ℝ) x) ((sinLp n : Icc (0 : ℝ) π → ℝ) x)
          ∂halfRangeMeasure
        = √(2 / π) * ∫ x : Icc (0 : ℝ) π, (f : Icc (0 : ℝ) π → ℝ) x * Real.sin ((n + 1) * x)
          ∂halfRangeMeasure := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_sinLp n] with x hx
      rw [hx, RCLike.inner_apply, sinFun_apply, conj_trivial]
      ring
    rw [h2] at h1
    exact (mul_eq_zero.1 h1).resolve_left sqrt_two_div_pi_ne_zero
  -- the auxiliary function `g = f · sin`
  let sinC : C(Icc (0 : ℝ) π, ℝ) := ⟨fun x ↦ Real.sin x, by fun_prop⟩
  have hg : MemLp (fun x ↦ sinC x * (f : Icc (0 : ℝ) π → ℝ) x) 2 halfRangeMeasure :=
    (MemLp.of_bound (p := ⊤) sinC.continuous.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x ↦ by
        simpa [sinC] using Real.abs_sin_le_one (x : ℝ))).fun_mul
      (Lp.memLp f)
  -- `g` is orthogonal to every cosine
  have hcos : ∀ m : ℕ, inner ℝ (hg.toLp _) (cosLp m) = 0 := by
    intro m
    rw [MeasureTheory.L2.inner_def]
    have hae : ∀ k : ℕ, (cosLp k : Icc (0 : ℝ) π → ℝ) =ᵐ[halfRangeMeasure] cosFun k :=
      fun k ↦ ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (𝕜 := ℝ) halfRangeMeasure (cosFun k)
    have h1 : ∫ x, inner ℝ ((hg.toLp _ : Icc (0 : ℝ) π → ℝ) x)
          ((cosLp m : Icc (0 : ℝ) π → ℝ) x) ∂halfRangeMeasure
        = (cosNorm m / 2) * ((∫ x : Icc (0 : ℝ) π, (f : Icc (0 : ℝ) π → ℝ) x *
            Real.sin ((m + 1) * x) ∂halfRangeMeasure) +
          ∫ x : Icc (0 : ℝ) π, (f : Icc (0 : ℝ) π → ℝ) x * Real.sin ((1 - m) * x)
            ∂halfRangeMeasure) := by
      have hi1 : Integrable (fun x : Icc (0 : ℝ) π ↦ (f : Icc (0 : ℝ) π → ℝ) x *
          Real.sin ((m + 1) * x)) halfRangeMeasure :=
        integrable_mul_continuousMap f ⟨fun x ↦ Real.sin ((m + 1) * x), by fun_prop⟩
      have hi2 : Integrable (fun x : Icc (0 : ℝ) π ↦ (f : Icc (0 : ℝ) π → ℝ) x *
          Real.sin ((1 - m) * x)) halfRangeMeasure :=
        integrable_mul_continuousMap f ⟨fun x ↦ Real.sin ((1 - m) * x), by fun_prop⟩
      rw [← integral_add hi1 hi2, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hg.coeFn_toLp, hae m] with x hx hxc
      rw [hx, hxc, RCLike.inner_apply, conj_trivial]
      simp only [cosFun, cosMap, ContinuousMap.smul_apply, ContinuousMap.coe_mk, smul_eq_mul,
        sinC]
      have hps : Real.sin (x : ℝ) * Real.cos (m * x) =
          (Real.sin ((m + 1) * x) + Real.sin ((1 - m) * x)) / 2 := by
        have e1 : ((m : ℝ) + 1) * x = x + m * x := by ring
        have e2 : (1 - (m : ℝ)) * x = x - m * x := by ring
        rw [e1, e2, Real.sin_add, Real.sin_sub]
        ring
      linear_combination (cosNorm m * (f : Icc (0 : ℝ) π → ℝ) x) * hps
    rw [h1, hsin m]
    -- the second integral: `m = 0`, `m = 1`, `m ≥ 2`
    rcases m with _ | _ | k
    · have h0 := hsin 0
      simp only [Nat.cast_zero, zero_add, one_mul] at h0
      simp [h0]
    · simp
    · have : ∀ x : Icc (0 : ℝ) π, Real.sin ((1 - ((k + 2 : ℕ) : ℝ)) * x)
          = -Real.sin ((k + 1) * x) := fun x ↦ by
        rw [← Real.sin_neg]
        congr 1
        push_cast
        ring
      simp only [this, mul_neg, integral_neg, hsin k, neg_zero, add_zero, mul_zero]
  -- hence `g = 0`
  have hg0 : hg.toLp _ = 0 := by
    have : hg.toLp _ ∈ (span ℝ (Set.range cosLp))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (fun v hv ↦ ?_) (by simp) (fun v w _ _ hv hw ↦ ?_)
        (fun c v _ hv ↦ ?_) hu
      · obtain ⟨m, rfl⟩ := hv
        exact hcos m
      · rw [inner_add_right, hv, hw, add_zero]
      · rw [inner_smul_right, hv, mul_zero]
    rwa [orthogonal_span_cosLp_eq_bot, Submodule.mem_bot] at this
  -- hence `f = 0` almost everywhere
  rw [Lp.eq_zero_iff_ae_eq_zero] at hg0 ⊢
  filter_upwards [hg0, hg.coeFn_toLp, ae_sin_ne_zero] with x hx hx' hs
  rw [hx'] at hx
  simpa [sinC, hs] using hx

/-- The half-range sine system $(\sqrt{2/\pi} \sin((n + 1) x))_{n \ge 0}$ as a **Hilbert basis** of
$L^2(0, \pi)$.

It is built from `orthonormal_sinLp` and `orthogonal_span_sinLp_eq_bot`. -/
def sinBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 halfRangeMeasure) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_sinLp orthogonal_span_sinLp_eq_bot

/-- The members of the Hilbert basis `sinBasis` are the elements `sinLp n`. -/
@[simp]
theorem coe_sinBasis : ⇑sinBasis = sinLp := HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The span of the half-range sine system is dense in $L^2(0, \pi)$. -/
theorem dense_span_sinLp : (span ℝ (Set.range sinLp)).topologicalClosure = ⊤ := by
  have h := sinBasis.dense_span
  rwa [coe_sinBasis] at h

/-! ### The change of variables from $[0, \pi]$ to $[0, 1]$ -/

/-- **Change of variables** $y \mapsto y / \pi$. The map $y \mapsto y / \pi$ from $[0, \pi]$ to
$\mathbb{R}$ is measure preserving from Lebesgue measure on $[0, \pi]$ to $\pi$ times Lebesgue
measure restricted to $(0, 1)$.

The measure on $[0, \pi]$ is `halfRangeMeasure`, on the subtype `Icc 0 π`. The measure on
$\mathbb{R}$ is `ENNReal.ofReal π • volume.restrict (Ioo 0 1)`. -/
theorem measurePreserving_div_pi :
    MeasurePreserving (fun y : Icc (0 : ℝ) π ↦ (y : ℝ) / π) halfRangeMeasure
      (ENNReal.ofReal π • volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 : MeasurePreserving ((↑) : Icc (0 : ℝ) π → ℝ) halfRangeMeasure
      (volume.restrict (Icc (0 : ℝ) π)) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_Icc volume⟩
  have h2 : MeasurePreserving (fun y : ℝ ↦ y / π) (volume.restrict (Icc (0 : ℝ) π))
      (ENNReal.ofReal π • volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine ⟨by fun_prop, ?_⟩
    have hfun : (fun y : ℝ ↦ y / π) = (π⁻¹ * ·) := funext fun y ↦ by rw [div_eq_inv_mul]
    have hpre : (fun y : ℝ ↦ π⁻¹ * y) ⁻¹' Icc 0 1 = Icc 0 π := by
      ext y
      simp only [mem_preimage, mem_Icc]
      constructor
      · rintro ⟨h0, h1⟩
        exact ⟨by nlinarith [inv_pos.2 hπ], by
          rwa [inv_mul_le_iff₀ hπ, mul_one] at h1⟩
      · rintro ⟨h0, h1⟩
        exact ⟨by positivity, by rwa [inv_mul_le_iff₀ hπ, mul_one]⟩
    have hIcc : volume.restrict (Ioo (0 : ℝ) 1) = volume.restrict (Icc 0 1) :=
      Measure.restrict_congr_set Ioo_ae_eq_Icc
    rw [hfun, hIcc, ← hpre, ← Measure.restrict_map (by fun_prop) measurableSet_Icc,
      Real.map_volume_mul_left (inv_ne_zero hπ.ne'), inv_inv, abs_of_pos hπ,
      Measure.restrict_smul]
  exact h2.comp h1

/-! ### The sine system on $(0, 1)$ -/

/-- The normalized sine $x \mapsto \sqrt{2} \sin((k + 1) \pi x)$, as a function on $\mathbb{R}$. -/
def sinUnitFun (k : ℕ) (x : ℝ) : ℝ := √2 * Real.sin ((k + 1) * π * x)

/-- The function `sinUnitFun k` is continuous on $\mathbb{R}$. -/
theorem continuous_sinUnitFun (k : ℕ) : Continuous (sinUnitFun k) := by
  unfold sinUnitFun; fun_prop

/-- For every exponent $p \in [0, \infty]$, the function `sinUnitFun k` is in $L^p(0, 1)$. -/
theorem memLp_sinUnitFun (k : ℕ) (p : ℝ≥0∞) :
    MemLp (sinUnitFun k) p (volume.restrict (Ioo (0 : ℝ) 1)) :=
  MemLp.of_bound (continuous_sinUnitFun k).aestronglyMeasurable √2
    (Filter.Eventually.of_forall fun x ↦ by
      rw [sinUnitFun, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
      exact mul_le_of_le_one_right (Real.sqrt_nonneg 2) (Real.abs_sin_le_one _))

/-- The **sine system on $(0, 1)$**: for $k \in \mathbb{N}$, the class in $L^2(0, 1)$ of the
function $x \mapsto \sqrt{2} \sin((k + 1) \pi x)$.

The space $L^2(0, 1)$ is `Lp ℝ 2 (volume.restrict (Ioo 0 1))`, a space of classes of functions
on $\mathbb{R}$. -/
def sinUnitLp (k : ℕ) : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (memLp_sinUnitFun k 2).toLp _

/-- The function `sinUnitFun k` represents the class `sinUnitLp k`: the two agree almost everywhere
on $(0, 1)$. -/
theorem coeFn_sinUnitLp (k : ℕ) :
    (sinUnitLp k : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] sinUnitFun k :=
  (memLp_sinUnitFun k 2).coeFn_toLp

/-- For $j, k \in \mathbb{N}$, the inner product of `sinUnitLp j` and `sinUnitLp k` in $L^2(0, 1)$
is $1$ if $j = k$ and $0$ otherwise. -/
theorem inner_sinUnitLp (j k : ℕ) :
    inner ℝ (sinUnitLp j) (sinUnitLp k) = if j = k then 1 else 0 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [MeasureTheory.L2.inner_def]
  have key : ∫ x, inner ℝ ((sinUnitLp j : ℝ → ℝ) x) ((sinUnitLp k : ℝ → ℝ) x)
        ∂(volume.restrict (Ioo (0 : ℝ) 1))
      = ∫ x in Ioo (0 : ℝ) 1, (√2 * √2) *
          (Real.sin ((j + 1) * (π * x)) * Real.sin ((k + 1) * (π * x))) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sinUnitLp j, coeFn_sinUnitLp k] with x hxj hxk
    rw [hxj, hxk, RCLike.inner_apply, conj_trivial, sinUnitFun, sinUnitFun]
    ring_nf
  have hint := integral_sin_nat_mul_sin_nat_mul (j + 1) (k + 1)
  push_cast at hint
  rw [key, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left
      (fun t ↦ Real.sin ((j + 1) * t) * Real.sin ((k + 1) * t)) hπ.ne', mul_zero, mul_one,
    hint, Real.mul_self_sqrt zero_le_two]
  by_cases hjk : j = k
  · subst hjk
    simp only [ite_true, smul_eq_mul]
    field_simp
  · simp [hjk]

/-- The sine system $(\sqrt{2} \sin((k + 1) \pi x))_{k \ge 0}$ is **orthonormal** in $L^2(0, 1)$. -/
theorem orthonormal_sinUnitLp : Orthonormal ℝ sinUnitLp := orthonormal_iff_ite.2 inner_sinUnitLp

/-- **Completeness of the sine system** in $L^2(0, 1)$: the orthogonal complement of the span of the
functions $\sqrt{2} \sin((n + 1) \pi x)$, $n \ge 0$, is $\{0\}$.

The change of variables $y \mapsto y / \pi$ (`measurePreserving_div_pi`) carries a function on
$(0, 1)$ that is orthogonal to every $\sin((n + 1) \pi x)$ to a function on $[0, \pi]$ that is
orthogonal to every $\sin((n + 1) y)$. That function is zero by `orthogonal_span_sinLp_eq_bot`. -/
theorem orthogonal_span_sinUnitLp_eq_bot : (span ℝ (Set.range sinUnitLp))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set S : Icc (0 : ℝ) π → ℝ := fun y ↦ (y : ℝ) / π with hS
  -- the hypothesis, as integrals over `(0, 1)`
  have hsin : ∀ n : ℕ, ∫ x in Ioo (0 : ℝ) 1, (f : ℝ → ℝ) x * Real.sin ((n + 1) * π * x) = 0 := by
    intro n
    have h1 : inner ℝ f (sinUnitLp n) = 0 :=
      (Submodule.mem_orthogonal' _ _).mp hf _ (subset_span ⟨n, rfl⟩)
    rw [MeasureTheory.L2.inner_def] at h1
    have h2 : ∫ x, inner ℝ ((f : ℝ → ℝ) x) ((sinUnitLp n : ℝ → ℝ) x)
          ∂(volume.restrict (Ioo (0 : ℝ) 1))
        = √2 * ∫ x in Ioo (0 : ℝ) 1, (f : ℝ → ℝ) x * Real.sin ((n + 1) * π * x) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_sinUnitLp n] with x hx
      rw [hx, RCLike.inner_apply, conj_trivial, sinUnitFun]
      ring
    rw [h2] at h1
    exact (mul_eq_zero.1 h1).resolve_left (Real.sqrt_pos.2 zero_lt_two).ne'
  -- the transported function `F = f ∘ S` lies in `L²(0, π)`
  have hF : MemLp ((f : ℝ → ℝ) ∘ S) 2 halfRangeMeasure :=
    ((Lp.memLp f).smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving
      measurePreserving_div_pi
  -- and is orthogonal to every `sin ((n + 1) y)`
  have hFsin : ∀ n : ℕ, inner ℝ (hF.toLp _) (sinLp n) = 0 := by
    intro n
    rw [MeasureTheory.L2.inner_def]
    have h1 : ∫ y, inner ℝ ((hF.toLp _ : Icc (0 : ℝ) π → ℝ) y)
          ((sinLp n : Icc (0 : ℝ) π → ℝ) y) ∂halfRangeMeasure
        = ∫ y : Icc (0 : ℝ) π, (fun t : ℝ ↦ (f : ℝ → ℝ) (t / π) * (√(2 / π) *
            Real.sin ((n + 1) * t))) y ∂halfRangeMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hF.coeFn_toLp, coeFn_sinLp n] with y hy hyn
      rw [hy, hyn, RCLike.inner_apply, conj_trivial, sinFun_apply]
      simp only [Function.comp, hS]
      ring
    have h3 : ∫ x in (0 : ℝ)..π, (f : ℝ → ℝ) (x / π) * (√(2 / π) * Real.sin ((n + 1) * x))
        = ∫ x in (0 : ℝ)..π, (fun t ↦ (f : ℝ → ℝ) t *
            (√(2 / π) * Real.sin ((n + 1) * (π * t)))) (x / π) := by
      refine intervalIntegral.integral_congr fun x _ ↦ ?_
      simp only
      rw [show π * (x / π) = x by field_simp]
    rw [h1, integral_halfRangeMeasure (fun t ↦ (f : ℝ → ℝ) (t / π) * (√(2 / π) *
      Real.sin ((n + 1) * t))), h3, intervalIntegral.integral_comp_div (fun t ↦ (f : ℝ → ℝ) t *
      (√(2 / π) * Real.sin ((n + 1) * (π * t)))) hπ.ne', zero_div, div_self hπ.ne',
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    have h2 : ∫ x in Ioo (0 : ℝ) 1, (f : ℝ → ℝ) x * (√(2 / π) * Real.sin ((n + 1) * (π * x)))
        = √(2 / π) * ∫ x in Ioo (0 : ℝ) 1, (f : ℝ → ℝ) x * Real.sin ((n + 1) * π * x) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring_nf
    rw [h2, hsin n, mul_zero, smul_zero]
  -- hence `F = 0`
  have hF0 : hF.toLp _ = 0 := by
    have : hF.toLp _ ∈ (span ℝ (Set.range sinLp))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (fun v hv ↦ ?_) (by simp) (fun v w _ _ hv hw ↦ ?_)
        (fun c v _ hv ↦ ?_) hu
      · obtain ⟨n, rfl⟩ := hv
        exact hFsin n
      · rw [inner_add_right, hv, hw, add_zero]
      · rw [inner_smul_right, hv, mul_zero]
    rwa [orthogonal_span_sinLp_eq_bot, Submodule.mem_bot] at this
  -- hence `f = 0` almost everywhere on `(0, 1)`
  rw [Lp.eq_zero_iff_ae_eq_zero] at hF0 ⊢
  have hae : ∀ᵐ y ∂halfRangeMeasure, (f : ℝ → ℝ) (S y) = 0 := by
    filter_upwards [hF0, hF.coeFn_toLp] with y hy hy'
    rw [hy'] at hy
    exact hy
  have hmap := (ae_map_iff measurePreserving_div_pi.aemeasurable
    ((Lp.stronglyMeasurable f).measurable (measurableSet_singleton 0))).2 hae
  have h0 : ENNReal.ofReal π ≠ 0 := (ENNReal.ofReal_pos.2 hπ).ne'
  rw [measurePreserving_div_pi.map_eq, ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero]
    at hmap
  rw [Filter.EventuallyEq, ae_iff]
  simpa using hmap.resolve_left h0

/-- The sine system $(\sqrt{2} \sin((n + 1) \pi x))_{n \ge 0}$ as a **Hilbert basis** of
$L^2(0, 1)$. Its members are the eigenfunctions of $-d^2/dx^2$ on $(0, 1)$ with Dirichlet
boundary conditions; see [brezis2011functional], §8.6, the Example after Theorem 8.22.

It is built from `orthonormal_sinUnitLp` and `orthogonal_span_sinUnitLp_eq_bot`. -/
def sinBasisUnit : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_sinUnitLp orthogonal_span_sinUnitLp_eq_bot

/-- The members of the Hilbert basis `sinBasisUnit` are the elements `sinUnitLp n`. -/
@[simp]
theorem coe_sinBasisUnit : ⇑sinBasisUnit = sinUnitLp := HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- For $n \in \mathbb{N}$, the member $n$ of the Hilbert basis `sinBasisUnit` agrees almost
everywhere on $(0, 1)$ with the function $x \mapsto \sqrt{2} \sin((n + 1) \pi x)$. -/
theorem coeFn_sinBasisUnit (n : ℕ) :
    (sinBasisUnit n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ √2 * Real.sin ((n + 1) * π * x) := by
  rw [coe_sinBasisUnit]
  exact coeFn_sinUnitLp n

/-! ### Sine polynomials on $[0, \pi]$ -/

section SinePolynomial

open Submodule

/-- The **sine polynomial** with $n$ terms and coefficients $c \colon \mathbb{N} \to \mathbb{R}$:
the continuous function
$$x \mapsto \sum_{j < n} c_j \sin((j + 1) x)$$
on $[0, \pi]$.

It is the initial value of the finite sine series `Heat.sineSeries`, which solves the heat
equation on $(0, \pi)$. -/
noncomputable def sinePolynomial (n : ℕ) (c : ℕ → ℝ) : C(Icc (0 : ℝ) π, ℝ) :=
  ∑ j ∈ Finset.range n, c j • sinMap j

/-- For $x \in [0, \pi]$, the value of `sinePolynomial n c` at $x$ is
$\sum_{j < n} c_j \sin((j + 1) x)$. -/
theorem sinePolynomial_apply (n : ℕ) (c : ℕ → ℝ) (x : Icc (0 : ℝ) π) :
    sinePolynomial n c x = ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * (x : ℝ)) := by
  simp [sinePolynomial, sinMap_apply]

/-- Every sine polynomial lies in the span of the functions $\sin((k + 1) x)$, $k \in \mathbb{N}$.
-/
theorem sinePolynomial_mem_span (n : ℕ) (c : ℕ → ℝ) :
    sinePolynomial n c ∈ span ℝ (Set.range sinMap) :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)

/-- A continuous function $v$ on $[0, \pi]$ lies in the span of the functions $\sin((k + 1) x)$,
$k \in \mathbb{N}$, if and only if there are $n \in \mathbb{N}$ and
$c \colon \mathbb{N} \to \mathbb{R}$ with $v = \sum_{j < n} c_j \sin((j + 1) x)$. -/
theorem mem_span_sinMap_iff {v : C(Icc (0 : ℝ) π, ℝ)} :
    v ∈ span ℝ (Set.range sinMap) ↔ ∃ (n : ℕ) (c : ℕ → ℝ), v = sinePolynomial n c := by
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
    refine ⟨c.support.sup id + 1, c, ?_⟩
    rw [← hc, sinePolynomial]
    exact Finsupp.sum_of_support_subset c (s := Finset.range (c.support.sup id + 1))
      (fun i hi => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)))
      _ (fun i _ => zero_smul ℝ _)
  · rintro ⟨n, c, rfl⟩
    exact sinePolynomial_mem_span n c

/-- The functions $x \mapsto \sin((k + 1) x)$, $k \in \mathbb{N}$, are **linearly independent** in
the space of continuous functions on $[0, \pi]$.

Their classes in $L^2(0, \pi)$, multiplied by $\sqrt{2/\pi}$, are orthonormal. -/
theorem linearIndependent_sinMap : LinearIndependent ℝ sinMap := by
  have h : LinearIndependent ℝ sinLp := orthonormal_sinLp.linearIndependent
  have e : sinLp = ⇑(√(2 / π) • (ContinuousMap.toLp (E := ℝ) 2 halfRangeMeasure ℝ :
      C(Icc (0 : ℝ) π, ℝ) →ₗ[ℝ] MeasureTheory.Lp ℝ 2 halfRangeMeasure)) ∘ sinMap := by
    funext k
    rw [Function.comp_apply, LinearMap.smul_apply, sinLp_eq_smul]
    rfl
  rw [e] at h
  exact LinearIndependent.of_comp _ h

end SinePolynomial

end
