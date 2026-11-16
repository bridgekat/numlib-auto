/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.AddCircle` or a file beside it.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The half-range cosine system as a Hilbert basis of $L^2(0, \pi)$

The half-range cosine system is
$$e_0(x) = \frac{1}{\sqrt{\pi}}, \qquad e_k(x) = \sqrt{\frac{2}{\pi}} \cos(kx) \quad (k \ge 1).$$
This file proves that it is orthonormal and complete in $L^2(0, \pi)$, so that it is a Hilbert basis
of $L^2(0, \pi)$. This is Example 1.3.14 of [han2009theoretical]. The system is the cosine half of
the trigonometric system of `Numlib.Analysis.Fourier.TrigonometricBasis`, and a cosine series on a
half period is an expansion in it. The file also proves the orthogonality relations of the sines on
$[0, \pi]$, and the orthogonality of the cosines $\cos(m\pi x)$ on $[0, 1]$.

## Main definitions

* `halfRangeMeasure`: the Lebesgue measure on $[0, \pi]$, as a measure on the subtype, which is the
  measure of $L^2(0, \pi)$.
* `cosMap`: the functions $x \mapsto \cos(kx)$ in $C([0, \pi], \mathbb{R})$.
* `cosNorm`: the normalizing constants $1/\sqrt{\pi}$ for $k = 0$ and $\sqrt{2/\pi}$ for $k \ge 1$.
* `cosFun`: the normalized system $e_k$, as continuous functions.
* `cosLp`: the normalized system $e_k$, as elements of $L^2(0, \pi)$.
* `cosSubalgebra`: the span of the functions $\cos(kx)$, as a subalgebra of
  $C([0, \pi], \mathbb{R})$.
* `cosBasis`: the Hilbert basis $(e_k)_{k \in \mathbb{N}}$ of $L^2(0, \pi)$.

## Main results

* `integral_cos_nat_mul_cos_nat_mul`: the orthogonality relations of the cosines on $[0, \pi]$.
* `integral_sin_nat_mul_sin_nat_mul`: the orthogonality relations of the sines on $[0, \pi]$.
* `orthonormal_cosLp`: the system $(e_k)$ is orthonormal in $L^2(0, \pi)$.
* `dense_span_cosMap`: the cosine polynomials are dense in $C([0, \pi], \mathbb{R})$.
* `orthogonal_span_cosLp_eq_bot`: the system $(e_k)$ is complete in $L^2(0, \pi)$.
* `integral_cos_mul_cos_unit`: $\int_0^1 \cos(m\pi x) \cos(n\pi x) \, dx = \delta_{mn}/2$ for
  $m, n \ge 1$.

## Proof outline

The classical proof extends a function of $L^2(0, \pi)$ to an even function in $L^2(-\pi, \pi)$, and
deduces the completeness from the completeness of the full trigonometric system. The proof here is
another classical one, and it is shorter in this setting. The span of the functions $\cos(kx)$ is a
subalgebra of $C([0, \pi], \mathbb{R})$, by the product-to-sum formula alone. It separates the
points of $[0, \pi]$, because $\cos$ is injective on $[0, \pi]$ (`Real.injOn_cos`). So the
Stone–Weierstrass theorem makes it dense in $C([0, \pi], \mathbb{R})$, and the continuous functions
are dense in $L^2(0, \pi)$. The proof needs no isometry of even extension and no expansion of
$\cos^k x$ in Chebyshev polynomials.

## Implementation notes

* The space $L^2(0, \pi)$ is `Lp ℝ 2 halfRangeMeasure`, on the subtype `Icc 0 π` of $\mathbb{R}$.
-/


open MeasureTheory Set Submodule

open scoped ENNReal Real

/-- The Lebesgue measure on $[0, \pi]$, as a measure on the subtype `Icc 0 π`: the pullback of the
Lebesgue measure along the inclusion. This is the measure of $L^2(0, \pi)$. -/
noncomputable def halfRangeMeasure : Measure (Icc (0 : ℝ) π) := Measure.comap Subtype.val volume

instance : IsFiniteMeasure halfRangeMeasure where
  measure_univ_lt_top := by
    have h : halfRangeMeasure univ = (volume.restrict (Icc (0 : ℝ) π)) univ := by
      rw [halfRangeMeasure, ← map_comap_subtype_coe (measurableSet_Icc (a := (0:ℝ)) (b := π))
        (volume : Measure ℝ), Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
        Set.preimage_univ]
    rw [h, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

/-- An integral over the subtype $[0, \pi]$ is an interval integral: for
$f : \mathbb{R} \to \mathbb{R}$,
$$\int_{[0, \pi]} f(x) \, d\mu(x) = \int_0^\pi f(x) \, dx,$$
where $\mu$ is `halfRangeMeasure`. -/
theorem integral_halfRangeMeasure (f : ℝ → ℝ) :
    ∫ x : Icc (0 : ℝ) π, f x ∂halfRangeMeasure = ∫ x in (0 : ℝ)..π, f x := by
  rw [halfRangeMeasure, integral_subtype_comap measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]

/-- For an integer $m$,
$$\int_0^\pi \cos(mx) \, dx = \begin{cases} \pi & \text{if } m = 0, \\ 0 & \text{otherwise.}
  \end{cases}$$
-/
theorem integral_cos_int_mul (m : ℤ) :
    ∫ x in (0 : ℝ)..π, Real.cos (m * x) = if m = 0 then π else 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hm0 : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm0, integral_cos]
    simp [Real.sin_int_mul_pi, hm]

/-- For natural numbers $j, k$, $\int_0^\pi \cos((j + k)x) \, dx$ is $\pi$ if $j = k = 0$ and $0$
otherwise. -/
private theorem integral_cos_nat_add_nat_mul (j k : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.cos (((j : ℤ) + k : ℤ) * x) = if j = 0 ∧ k = 0 then π else 0 := by
  rw [integral_cos_int_mul]
  exact if_congr (by omega) rfl rfl

/-- For natural numbers $j, k$, $\int_0^\pi \cos((j - k)x) \, dx$ is $\pi$ if $j = k$ and $0$
otherwise. -/
private theorem integral_cos_nat_sub_nat_mul (j k : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.cos (((j : ℤ) - k : ℤ) * x) = if j = k then π else 0 := by
  rw [integral_cos_int_mul]
  exact if_congr (by omega) rfl rfl

/-- **The half-range cosine system is orthogonal on $[0, \pi]$.** For natural numbers $j, k$,
$$\int_0^\pi \cos(jx) \cos(kx) \, dx = \begin{cases} \pi & \text{if } j = k = 0, \\ \pi/2 &
  \text{if } j = k \ne 0, \\ 0 & \text{if } j \ne k. \end{cases}$$
-/
theorem integral_cos_nat_mul_cos_nat_mul (j k : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.cos (j * x) * Real.cos (k * x)
      = if j = k then (if j = 0 then π else π / 2) else 0 := by
  have hprod : ∀ x ∈ uIcc (0 : ℝ) π, Real.cos (j * x) * Real.cos (k * x)
      = (Real.cos (((j : ℤ) + k : ℤ) * x) + Real.cos (((j : ℤ) - k : ℤ) * x)) / 2 := by
    intro x _
    have h1 := Real.cos_add (j * x) (k * x)
    have h2 := Real.cos_sub (j * x) (k * x)
    have e1 : (((j : ℤ) + k : ℤ) : ℝ) * x = j * x + k * x := by push_cast; ring
    have e2 : (((j : ℤ) - k : ℤ) : ℝ) * x = j * x - k * x := by push_cast; ring
    rw [e1, e2, h1, h2]
    ring
  rw [intervalIntegral.integral_congr hprod]
  have hi1 : IntervalIntegrable (fun x => Real.cos (((j : ℤ) + k : ℤ) * x)) volume 0 π :=
    (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => Real.cos (((j : ℤ) - k : ℤ) * x)) volume 0 π :=
    (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2,
    integral_cos_nat_add_nat_mul, integral_cos_nat_sub_nat_mul]
  by_cases hjk : j = k
  · subst hjk
    by_cases hj : j = 0
    · subst hj; norm_num
    · simp [hj]
  · simp [hjk, show ¬(j = 0 ∧ k = 0) by omega]

/-- **The half-range sine system is orthogonal on $[0, \pi]$.** For natural numbers $j, k$,
$$\int_0^\pi \sin(jx) \sin(kx) \, dx = \begin{cases} \pi/2 & \text{if } j = k \ne 0, \\ 0 &
  \text{otherwise.} \end{cases}$$
The case $j = k = 0$ gives $0$, because $\sin(0x)$ is the zero function.

The proof uses `integral_cos_int_mul`, as for the cosines, through
$\sin A \sin B = (\cos(A - B) - \cos(A + B))/2$. -/
theorem integral_sin_nat_mul_sin_nat_mul (j k : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.sin (j * x) * Real.sin (k * x)
      = if j = k then (if j = 0 then 0 else π / 2) else 0 := by
  have hprod : ∀ x ∈ uIcc (0 : ℝ) π, Real.sin (j * x) * Real.sin (k * x)
      = (Real.cos (((j : ℤ) - k : ℤ) * x) - Real.cos (((j : ℤ) + k : ℤ) * x)) / 2 := by
    intro x _
    have h1 := Real.cos_sub (j * x) (k * x)
    have h2 := Real.cos_add (j * x) (k * x)
    have e1 : (((j : ℤ) - k : ℤ) : ℝ) * x = j * x - k * x := by push_cast; ring
    have e2 : (((j : ℤ) + k : ℤ) : ℝ) * x = j * x + k * x := by push_cast; ring
    rw [e1, e2, h1, h2]
    ring
  rw [intervalIntegral.integral_congr hprod]
  have hi1 : IntervalIntegrable (fun x => Real.cos (((j : ℤ) - k : ℤ) * x)) volume 0 π :=
    (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => Real.cos (((j : ℤ) + k : ℤ) * x)) volume 0 π :=
    (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hi1 hi2,
    integral_cos_nat_sub_nat_mul, integral_cos_nat_add_nat_mul]
  by_cases hjk : j = k
  · subst hjk
    by_cases hj : j = 0
    · subst hj; norm_num
    · simp [hj]
  · simp [hjk, show ¬(j = 0 ∧ k = 0) by omega]

/-- The cosine function $x \mapsto \cos(kx)$ of frequency $k \in \mathbb{N}$, as an element of
$C([0, \pi], \mathbb{R})$. These functions are the system before normalization. -/
noncomputable def cosMap (k : ℕ) : C(Icc (0 : ℝ) π, ℝ) := ⟨fun x => Real.cos (k * x), by fun_prop⟩

/-- The normalizing constants of the half-range cosine system: $1/\sqrt{\pi}$ for $k = 0$, and
$\sqrt{2/\pi}$ for $k \ge 1$. -/
noncomputable def cosNorm (k : ℕ) : ℝ := if k = 0 then 1 / √π else √(2 / π)

/-- The normalizing constant of the constant function is $1/\sqrt{\pi}$. -/
theorem cosNorm_zero : cosNorm 0 = 1 / √π := by simp [cosNorm]

/-- For $k \ne 0$, the normalizing constant is $\sqrt{2/\pi}$. -/
theorem cosNorm_of_ne_zero {k : ℕ} (hk : k ≠ 0) : cosNorm k = √(2 / π) := by simp [cosNorm, hk]

/-- The normalizing constants are nonzero. So `cosFun` and `cosMap` span the same space. -/
theorem cosNorm_ne_zero (k : ℕ) : cosNorm k ≠ 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; rw [cosNorm_zero]; positivity
  · rw [cosNorm_of_ne_zero hk]; positivity

/-- The half-range cosine system $e_k = c_k \cos(kx)$, as continuous functions on $[0, \pi]$, where
$c_k$ is the normalizing constant `cosNorm k`. -/
noncomputable def cosFun (k : ℕ) : C(Icc (0 : ℝ) π, ℝ) := cosNorm k • cosMap k

/-- The half-range cosine system $e_k$, as elements of $L^2(0, \pi)$. -/
noncomputable def cosLp (k : ℕ) : Lp ℝ 2 halfRangeMeasure :=
  ContinuousMap.toLp 2 halfRangeMeasure ℝ (cosFun k)

/-- In $L^2(0, \pi)$, $e_k$ is the normalizing constant `cosNorm k` times the class of $\cos(kx)$.
-/
theorem cosLp_eq_smul (k : ℕ) :
    cosLp k = cosNorm k • ContinuousMap.toLp 2 halfRangeMeasure ℝ (cosMap k) := by
  rw [cosLp, cosFun, map_smul]

/-- The inner products of the half-range cosine system in $L^2(0, \pi)$:
$\langle e_j, e_k \rangle = 1$ if $j = k$, and $0$ otherwise. -/
theorem inner_cosLp (j k : ℕ) : inner ℝ (cosLp j) (cosLp k) = if j = k then 1 else 0 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hae : ∀ m : ℕ, (cosLp m : Icc (0 : ℝ) π → ℝ) =ᵐ[halfRangeMeasure] cosFun m :=
    fun m => ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (𝕜 := ℝ) halfRangeMeasure (cosFun m)
  rw [MeasureTheory.L2.inner_def]
  have key : ∫ x, inner ℝ ((cosLp j : Icc (0 : ℝ) π → ℝ) x) ((cosLp k : Icc (0 : ℝ) π → ℝ) x)
        ∂halfRangeMeasure
      = ∫ x : Icc (0 : ℝ) π, (cosNorm j * cosNorm k) *
          (Real.cos (j * (x : ℝ)) * Real.cos (k * (x : ℝ))) ∂halfRangeMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [hae j, hae k] with x hxj hxk
    rw [hxj, hxk, RCLike.inner_apply]
    simp only [cosFun, cosMap, ContinuousMap.smul_apply, ContinuousMap.coe_mk, smul_eq_mul,
      conj_trivial]
    ring
  rw [key, integral_const_mul,
    integral_halfRangeMeasure (fun t => Real.cos (j * t) * Real.cos (k * t)),
    integral_cos_nat_mul_cos_nat_mul]
  rcases eq_or_ne j k with hjk | hjk
  · subst hjk
    have hite : (if j = j then (if j = 0 then π else π / 2) else 0)
        = if j = 0 then π else π / 2 := by simp
    have hgoal : (if j = j then (1 : ℝ) else 0) = 1 := by simp
    rw [hite, hgoal]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj
      have h2 : (if (0 : ℕ) = 0 then π else π / 2) = π := by simp
      rw [cosNorm_zero, h2,
        show (1 : ℝ) / √π * (1 / √π) * π = π / (√π * √π) by ring,
        Real.mul_self_sqrt hπ.le, div_self hπ.ne']
    · have h2 : (if j = 0 then π else π / 2) = π / 2 := by simp [hj]
      rw [cosNorm_of_ne_zero hj, h2,
        show √(2 / π) * √(2 / π) * (π / 2) = (√(2 / π) * √(2 / π)) * (π / 2) by ring,
        Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 / π)]
      field_simp
  · simp [hjk]

/-- **The half-range cosine system $(e_k)_{k \in \mathbb{N}}$ is orthonormal in $L^2(0, \pi)$.** -/
theorem orthonormal_cosLp : Orthonormal ℝ cosLp := orthonormal_iff_ite.2 inner_cosLp

/-- **The product-to-sum formula.** For natural numbers $m, n$, as functions on $[0, \pi]$,
$$\cos(mx) \cos(nx) = \frac{1}{2} \bigl(\cos((m + n)x) + \cos(|m - n| x)\bigr).$$
So the span of the functions $\cos(kx)$ is closed under multiplication.

The frequency $|m - n|$ is written `max m n - min m n`, a difference of natural numbers. -/
theorem cosMap_mul (m n : ℕ) :
    cosMap m * cosMap n = (2 : ℝ)⁻¹ • (cosMap (m + n) + cosMap (max m n - min m n)) := by
  ext x
  simp only [cosMap, ContinuousMap.mul_apply, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
    ContinuousMap.add_apply, smul_eq_mul]
  have hadd : ((m + n : ℕ) : ℝ) * (x : ℝ) = m * (x : ℝ) + n * (x : ℝ) := by push_cast; ring
  rcases le_total n m with h | h
  · have hsub : ((max m n - min m n : ℕ) : ℝ) * (x : ℝ) = m * (x : ℝ) - n * (x : ℝ) := by
      rw [max_eq_left h, min_eq_right h, Nat.cast_sub h]; ring
    rw [hadd, hsub, Real.cos_add, Real.cos_sub]
    ring
  · have hsub : ((max m n - min m n : ℕ) : ℝ) * (x : ℝ) = n * (x : ℝ) - m * (x : ℝ) := by
      rw [max_eq_right h, min_eq_left h, Nat.cast_sub h]; ring
    rw [hadd, hsub, Real.cos_add, Real.cos_sub]
    ring

/-- The constant function $1$ is the function $\cos(0x)$, so it lies in the span of the functions
$\cos(kx)$. -/
theorem one_mem_span_cosMap : (1 : C(Icc (0 : ℝ) π, ℝ)) ∈ span ℝ (Set.range cosMap) := by
  have h : cosMap 0 = 1 := by ext x; simp [cosMap]
  rw [← h]
  exact subset_span ⟨0, rfl⟩

/-- The span of the functions $\cos(kx)$ in $C([0, \pi], \mathbb{R})$ is closed under
multiplication. -/
theorem mul_mem_span_cosMap {f g : C(Icc (0 : ℝ) π, ℝ)} (hf : f ∈ span ℝ (Set.range cosMap))
    (hg : g ∈ span ℝ (Set.range cosMap)) : f * g ∈ span ℝ (Set.range cosMap) := by
  have hgen : ∀ m : ℕ, ∀ y ∈ span ℝ (Set.range cosMap),
      cosMap m * y ∈ span ℝ (Set.range cosMap) := by
    intro m y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨n, rfl⟩ := hz
        rw [cosMap_mul]
        exact Submodule.smul_mem _ _
          (Submodule.add_mem _ (subset_span ⟨_, rfl⟩) (subset_span ⟨_, rfl⟩))
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
  induction hf using Submodule.span_induction with
  | mem z hz => obtain ⟨m, rfl⟩ := hz; exact hgen m g hg
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

/-- The span of the functions $\cos(kx)$, $k \in \mathbb{N}$, as a subalgebra of
$C([0, \pi], \mathbb{R})$: the algebra of the cosine polynomials. -/
noncomputable def cosSubalgebra : Subalgebra ℝ C(Icc (0 : ℝ) π, ℝ) :=
  (span ℝ (Set.range cosMap)).toSubalgebra one_mem_span_cosMap
    fun _ _ hx hy => mul_mem_span_cosMap hx hy

/-- The cosine polynomials separate the points of $[0, \pi]$, because $\cos$ is injective on
$[0, \pi]$. -/
theorem separatesPoints_cosSubalgebra : cosSubalgebra.SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨cosMap 1, subset_span ⟨1, rfl⟩, rfl⟩, ?_⟩
  simp only [cosMap, ContinuousMap.coe_mk, Nat.cast_one, one_mul]
  intro h
  exact hxy (Subtype.ext (Real.injOn_cos x.2 y.2 h))

/-- **The Stone–Weierstrass theorem on $[0, \pi]$** for cosine polynomials: the span of the
functions $\cos(kx)$, $k \in \mathbb{N}$, is dense in $C([0, \pi], \mathbb{R})$ for the uniform
norm.

The span is a subalgebra that contains the constants, and it separates points because $\cos$ is
injective on $[0, \pi]$. -/
theorem dense_span_cosMap :
    Dense ((span ℝ (Set.range cosMap) : Submodule ℝ C(Icc (0 : ℝ) π, ℝ)) :
      Set C(Icc (0 : ℝ) π, ℝ)) := by
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints cosSubalgebra
    separatesPoints_cosSubalgebra
  have h2 : closure ((cosSubalgebra : Subalgebra ℝ C(Icc (0 : ℝ) π, ℝ)) :
      Set C(Icc (0 : ℝ) π, ℝ)) = Set.univ := by
    rw [← Subalgebra.topologicalClosure_coe, h]
    rfl
  rw [dense_iff_closure_eq]
  exact h2

/-- **The half-range cosine system is complete in $L^2(0, \pi)$**: the orthogonal complement of the
span of $(e_k)_{k \in \mathbb{N}}$ is $\{0\}$.

The idea of the proof: a function orthogonal to every $e_k$ is orthogonal to every continuous
function by `dense_span_cosMap`, hence to every element of $L^2(0, \pi)$, hence it is zero. -/
theorem orthogonal_span_cosLp_eq_bot : (span ℝ (Set.range cosLp))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  set T : C(Icc (0 : ℝ) π, ℝ) →L[ℝ] Lp ℝ 2 halfRangeMeasure :=
    ContinuousMap.toLp 2 halfRangeMeasure ℝ with hT
  set L : C(Icc (0 : ℝ) π, ℝ) →L[ℝ] ℝ := (innerSL ℝ f).comp T with hLdef
  have hgen : ∀ k : ℕ, L (cosMap k) = 0 := by
    intro k
    have h1 : inner ℝ f (cosLp k) = 0 :=
      (Submodule.mem_orthogonal' _ _).mp hf _ (subset_span ⟨k, rfl⟩)
    rw [cosLp_eq_smul, real_inner_smul_right] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (cosNorm_ne_zero k)
    · exact h
  have hspan : Set.EqOn (L : C(Icc (0 : ℝ) π, ℝ) → ℝ) (fun _ => 0)
      ((span ℝ (Set.range cosMap) : Submodule ℝ C(Icc (0 : ℝ) π, ℝ)) :
        Set C(Icc (0 : ℝ) π, ℝ)) := by
    intro y hy
    have hle : span ℝ (Set.range cosMap) ≤ LinearMap.ker (L : C(Icc (0 : ℝ) π, ℝ) →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hgen k
    exact hle hy
  have hL0 : ∀ y, L y = 0 :=
    congrFun (Continuous.ext_on dense_span_cosMap L.continuous continuous_const hspan)
  have hdense : DenseRange (T : C(Icc (0 : ℝ) π, ℝ) → Lp ℝ 2 halfRangeMeasure) :=
    ContinuousMap.toLp_denseRange ℝ halfRangeMeasure ℝ (by norm_num)
  have hall : ∀ z : Lp ℝ 2 halfRangeMeasure, inner ℝ f z = 0 := by
    refine congrFun (Continuous.ext_on hdense (innerSL ℝ f).continuous continuous_const ?_)
    rintro _ ⟨y, rfl⟩
    exact hL0 y
  exact inner_self_eq_zero.mp (hall f)

/-- **The half-range cosine system is a Hilbert basis of $L^2(0, \pi)$** ([han2009theoretical],
Example 1.3.14): the Hilbert basis indexed by $\mathbb{N}$ whose members are the functions
$e_k$. -/
noncomputable def cosBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 halfRangeMeasure) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_cosLp orthogonal_span_cosLp_eq_bot

/-- The members of the Hilbert basis `cosBasis` are the functions $e_k$ of `cosLp`. -/
@[simp]
theorem coe_cosBasis : ⇑cosBasis = cosLp := HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The span of the half-range cosine system is dense in $L^2(0, \pi)$: its closure is the whole
space. -/
theorem dense_span_cosLp : (span ℝ (Set.range cosLp)).topologicalClosure = ⊤ := by
  have h := cosBasis.dense_span
  rwa [coe_cosBasis] at h

/-- The constant member of the system is $e_0(x) = 1/\sqrt{\pi}$. -/
theorem cosFun_zero_apply (x : Icc (0 : ℝ) π) : cosFun 0 x = 1 / √π := by
  simp [cosFun, cosMap, cosNorm]

/-- For $k \ge 1$, the member of frequency $k$ is $e_k(x) = \sqrt{2/\pi} \cos(kx)$. -/
theorem cosFun_apply_of_ne_zero {k : ℕ} (hk : k ≠ 0) (x : Icc (0 : ℝ) π) :
    cosFun k x = √(2 / π) * Real.cos (k * (x : ℝ)) := by
  simp [cosFun, cosMap, cosNorm_of_ne_zero hk]

/-! ### Cosine integrals on the unit interval -/

section UnitInterval

/-- For a real $c \ne 0$,
$$\int_0^1 \cos(cx) \, dx = \frac{\sin c}{c}.$$
-/
theorem integral_cos_mul_unit {c : ℝ} (hc : c ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (c * x) = Real.sin c / c := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => Real.sin (c * y) / c) (Real.cos (c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h2 : HasDerivAt (fun y : ℝ => Real.sin (c * y)) (Real.cos (c * x) * c) x :=
      (Real.hasDerivAt_sin (c * x)).comp x h1
    simpa [mul_div_assoc, mul_div_cancel_right₀ _ hc] using h2.div_const c
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  simp

/-- For an integer $k$,
$$\int_0^1 \cos(k\pi x) \, dx = \begin{cases} 1 & \text{if } k = 0, \\ 0 & \text{otherwise.}
  \end{cases}$$
-/
theorem integral_cos_intMul_pi_unit (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * π * x) = if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hc : ((k : ℝ) * π) ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hk) Real.pi_ne_zero
    rw [ite_eq_right hk, integral_cos_mul_unit hc, Real.sin_int_mul_pi k, zero_div]

/-- **Orthogonality of the cosines on $(0, 1)$.** For positive integers $m$ and $n$,
$$\int_0^1 \cos(m\pi x) \cos(n\pi x) \, dx = \begin{cases} 1/2 & \text{if } m = n, \\ 0 &
  \text{otherwise.} \end{cases}$$
-/
theorem integral_cos_mul_cos_unit {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..1, Real.cos ((m : ℝ) * π * x) * Real.cos ((n : ℝ) * π * x)
      = if m = n then 1 / 2 else 0 := by
  have hprod : ∀ x : ℝ, Real.cos ((m : ℝ) * π * x) * Real.cos ((n : ℝ) * π * x)
      = (Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * π * x)
          + Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * π * x)) / 2 := by
    intro x
    have h1 : ((((m : ℤ) - n : ℤ) : ℝ) * π * x) = (m : ℝ) * π * x - (n : ℝ) * π * x := by
      push_cast; ring
    have h2 : ((((m : ℤ) + n : ℤ) : ℝ) * π * x) = (m : ℝ) * π * x + (n : ℝ) * π * x := by
      push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp only [hprod]
  have hint : ∀ k : ℤ, IntervalIntegrable (fun x : ℝ => Real.cos ((k : ℝ) * π * x)) volume 0 1 :=
    fun k => (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint _) (hint _),
    integral_cos_intMul_pi_unit, integral_cos_intMul_pi_unit]
  have hne : ((m : ℤ) + n) ≠ 0 := by positivity
  rw [ite_eq_right hne]
  rcases eq_or_ne m n with rfl | hmn
  · simp
  · rw [ite_eq_right hmn,
      ite_eq_right (by simpa [sub_eq_zero] using fun h => hmn (by exact_mod_cast h))]
    norm_num

end UnitInterval
