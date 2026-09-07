import Numlib.Approximation.Interpolation
import Numlib.IntegralEquations.WeaklySingular
import NumlibSurface.AtkinsonHan.Chapter12.Section01
import NumlibSurface.AtkinsonHan.Chapter12.Section04

/-!
# Atkinson–Han §12.5: product integration

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §12.5.

The equation is `λ u - K u = f` with the *weakly singular* kernel `k (x, y) = l (x, y) g (x, y)`,
`l` continuous and `g` singular but satisfying the two conditions (12.5.15)–(12.5.16) — the
conditions (A₂) and (A₁) of `IntegralOperator.IsAdmissibleKernel`.  The product integration method
replaces the smooth factor `y ↦ l (x, y) u (y)` of the integrand by its piecewise polynomial
interpolant and integrates the singular factor exactly:

`K_n u (x) = ∫ [l (x, ·) u (·)]_n (y) g (x, y) dy`.

`productCLM` is that operator, for an arbitrary bounded projection `P` in place of the
interpolation, and the content of §12.5.1 is that the family `{K_n}` is collectively compact and
pointwise convergent, so that the framework of §12.4.3 applies verbatim.

## Main results

* `productCLM` — the product integration operator, with `productCLM_apply` its defining formula,
  `norm_productCLM_le` the bound `‖K_n‖ ≤ c_g ‖P‖ c_l`, and `productCLM_one` the identification of
  the case `P = I` with the integral operator of the kernel `l g` itself.
* `tendsto_productCLM` — assumption A2, Exercise 12.5.1: `K_n u → K u` for every continuous `u`.
  Uniformity in `x` comes from Lemma 12.1.3 applied to the compact set `{l (x, ·) u (·) : x}`.
* `isCollectivelyCompactFamily_productCLM` — assumptions A1–A3.
* `theorem_12_5_1` — for all large `n` the approximating equations are uniquely solvable with
  uniformly bounded inverses and `‖u - u_n‖_∞ ≤ c ‖K u - K_n u‖_∞`, which is (12.5.17).
* `example_12_5_2` — the product trapezoidal rate (12.5.18),
  `‖u - u_n‖_∞ ≤ (c h²/8) max |∂²(l u)/∂y²|`.

## Not formalized here

* Theorem 12.5.4, the regularity of the solution of a weakly singular equation, and Lemma 12.5.5,
  graded-mesh interpolation, together with Theorem 12.5.6 which combines them.  Both need
  piecewise polynomial interpolation of degree `m`, of which `Numlib/Approximation/Interpolation`
  has only the linear case, and 12.5.4 needs in addition a differentiation theory under a weakly
  singular integral sign that the library does not have.
* §12.5.2, the generalizations to kernels not of the form `l g`, and the numerical examples.

## Conventions

As in §12.1 the book's scalar `λ` is written `μ`, and the measure is therefore written `ν`.  The
book's domain is `[a, b]`; the general statements below are for a compact metric space carrying a
Borel measure, which is the generality of `Numlib/IntegralEquations/WeaklySingular`, and the
interval case is `IntegralOperator.iccMeasure`.  The interpolation `[·]_n` is any sequence of
bounded operators converging pointwise to the identity with uniformly bounded norms; the book's
piecewise linear interpolation is `piecewiseLinearInterpCLM`, whose norm is one.

`productCLM` is defined here rather than in the backbone because `Numlib/IntegralEquations` was
held by another worktree; it belongs beside `IntegralOperator.admissibleKernelCLM`.
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

/-! ### The product integration operator -/

section ProductIntegration

open IntegralOperator MeasureTheory Metric Set

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **The factor of the integrand that a product rule interpolates**: the continuous function
`y ↦ l (x, y) u (y)`.  The product rule replaces it by its interpolant and integrates the result
against the singular factor `g (x, ·)`. -/
noncomputable def prodFactor (l : C(X × X, ℝ)) (x : X) (u : C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun y => l (x, y) * u y, (l.continuous.comp (by fun_prop)).mul u.continuous⟩

omit [CompactSpace X] in
@[simp]
theorem prodFactor_apply (l : C(X × X, ℝ)) (x : X) (u : C(X, ℝ)) (y : X) :
    prodFactor l x u y = l (x, y) * u y := rfl

omit [CompactSpace X] in
theorem prodFactor_add (l : C(X × X, ℝ)) (x : X) (u v : C(X, ℝ)) :
    prodFactor l x (u + v) = prodFactor l x u + prodFactor l x v := by
  ext y
  simp only [prodFactor_apply, ContinuousMap.add_apply]
  ring

omit [CompactSpace X] in
theorem prodFactor_smul (l : C(X × X, ℝ)) (x : X) (r : ℝ) (u : C(X, ℝ)) :
    prodFactor l x (r • u) = r • prodFactor l x u := by
  ext y
  simp only [prodFactor_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

/-- `‖l (x, ·) u (·)‖_∞ ≤ c_l ‖u‖_∞`. -/
theorem norm_prodFactor_le (l : C(X × X, ℝ)) (x : X) (u : C(X, ℝ)) :
    ‖prodFactor l x u‖ ≤ ‖l‖ * ‖u‖ := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro y
  rw [prodFactor_apply, norm_mul]
  exact mul_le_mul (l.norm_coe_le_norm _) (u.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)

/-- The oscillation of `l (x, ·) u (·)` in the base point `x` is controlled by that of `l`. -/
theorem norm_prodFactor_sub_le (l : C(X × X, ℝ)) {x z : X} {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ y : X, |l (x, y) - l (z, y)| ≤ η) (u : C(X, ℝ)) :
    ‖prodFactor l x u - prodFactor l z u‖ ≤ η * ‖u‖ := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro y
  have hrw : (prodFactor l x u - prodFactor l z u) y = (l (x, y) - l (z, y)) * u y := by
    simp only [ContinuousMap.sub_apply, prodFactor_apply]
    ring
  rw [hrw, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (hη y) (u.norm_coe_le_norm _) (norm_nonneg _) hη0

/-- `x ↦ l (x, ·) u (·)` is continuous into `C(X, ℝ)`, by uniform continuity of `l`. -/
theorem continuous_prodFactor (l : C(X × X, ℝ)) (u : C(X, ℝ)) :
    Continuous fun x => prodFactor l x u := by
  refine Metric.continuous_iff.2 fun x₀ ε hε => ?_
  obtain ⟨δ, hδ, hl⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous l.continuous) (ε / (‖u‖ + 1)) (by positivity)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hη : ∀ y : X, |l (x, y) - l (x₀, y)| ≤ ε / (‖u‖ + 1) := by
    intro y
    have hd : dist ((x, y) : X × X) (x₀, y) < δ := by
      rw [Prod.dist_eq]
      simpa using hx
    have h := hl hd
    rw [Real.dist_eq] at h
    exact h.le
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_prodFactor_sub_le l (by positivity) hη u) ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith [norm_nonneg u, hε]

section Kernel

variable [MeasurableSpace X] [BorelSpace X] {ν : Measure X} {g : X × X → ℝ}

/-- **The oscillation estimate of the proof of Theorem 12.5.1**: the difference of two values of
`K_n u` splits into the contribution of the oscillation of `l` and that of the singular factor. -/
theorem abs_product_sub_le (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (u : C(X, ℝ)) {x z : X} {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ y : X, |l (x, y) - l (z, y)| ≤ η) :
    |(∫ y, g (x, y) * (P (prodFactor l x u)) y ∂ν)
        - ∫ y, g (z, y) * (P (prodFactor l z u)) y ∂ν|
      ≤ rowBound ν g * (‖P‖ * (η * ‖u‖))
        + (∫ y, |g (x, y) - g (z, y)| ∂ν) * (‖P‖ * (‖l‖ * ‖u‖)) := by
  have hAB : (∫ y, g (x, y) * (P (prodFactor l x u)) y ∂ν)
      - ∫ y, g (x, y) * (P (prodFactor l z u)) y ∂ν
      = ∫ y, g (x, y) * (P (prodFactor l x u) - P (prodFactor l z u)) y ∂ν := by
    rw [← integral_sub (hg.integrable_mul _ x) (hg.integrable_mul _ x)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [ContinuousMap.sub_apply]
    ring
  have h1 : |∫ y, g (x, y) * (P (prodFactor l x u) - P (prodFactor l z u)) y ∂ν|
      ≤ rowBound ν g * (‖P‖ * (η * ‖u‖)) := by
    refine (hg.abs_integral_mul_le _ x).trans ?_
    have hn : ‖P (prodFactor l x u) - P (prodFactor l z u)‖ ≤ ‖P‖ * (η * ‖u‖) := by
      rw [← map_sub]
      exact (P.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_prodFactor_sub_le l hη0 hη u) (norm_nonneg P))
    exact mul_le_mul (hg.le_rowBound x) hn (norm_nonneg _) hg.rowBound_nonneg
  have h2 : |(∫ y, g (x, y) * (P (prodFactor l z u)) y ∂ν)
      - ∫ y, g (z, y) * (P (prodFactor l z u)) y ∂ν|
      ≤ (∫ y, |g (x, y) - g (z, y)| ∂ν) * (‖P‖ * (‖l‖ * ‖u‖)) := by
    refine (hg.abs_integral_mul_sub_le _ x z).trans ?_
    have hn : ‖P (prodFactor l z u)‖ ≤ ‖P‖ * (‖l‖ * ‖u‖) :=
      (P.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_prodFactor_le l z u) (norm_nonneg P))
    exact mul_le_mul_of_nonneg_left hn (integral_nonneg fun _ => abs_nonneg _)
  have hsplit : (∫ y, g (x, y) * (P (prodFactor l x u)) y ∂ν)
      - ∫ y, g (z, y) * (P (prodFactor l z u)) y ∂ν
      = (∫ y, g (x, y) * (P (prodFactor l x u) - P (prodFactor l z u)) y ∂ν)
        + ((∫ y, g (x, y) * (P (prodFactor l z u)) y ∂ν)
          - ∫ y, g (z, y) * (P (prodFactor l z u)) y ∂ν) := by
    rw [← hAB]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The uniform modulus of continuity of the product operators: a single `δ` serves every
projection of norm at most `Cp` and every `u` of norm at most `Cu`.  Continuity of one `K_n u` and
equicontinuity of the whole family `{K_n u : n, ‖u‖ ≤ 1}` are both read off it. -/
theorem exists_delta_product (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ)) {Cp Cu ε : ℝ}
    (hCp0 : 0 ≤ Cp) (hCu0 : 0 ≤ Cu) (hε : 0 < ε) :
    ∃ δ > 0, ∀ P : C(X, ℝ) →L[ℝ] C(X, ℝ), ‖P‖ ≤ Cp → ∀ u : C(X, ℝ), ‖u‖ ≤ Cu →
      ∀ x z : X, dist x z < δ →
        |(∫ y, g (x, y) * (P (prodFactor l x u)) y ∂ν)
          - ∫ y, g (z, y) * (P (prodFactor l z u)) y ∂ν| < ε := by
  have hc0 : (0 : ℝ) ≤ rowBound ν g := hg.rowBound_nonneg
  have hl0 : (0 : ℝ) ≤ ‖l‖ := norm_nonneg l
  set η : ℝ := ε / (2 * ((rowBound ν g + 1) * ((Cp + 1) * (Cu + 1)))) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; positivity
  obtain ⟨δ₁, hδ₁, hl⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous l.continuous) η hη0
  obtain ⟨δ₂, hδ₂, hgd⟩ := hg.exists_delta (ε / (2 * ((Cp + 1) * ((‖l‖ + 1) * (Cu + 1)))))
    (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun P hP u hu x z hxz => ?_⟩
  have hP0 : (0 : ℝ) ≤ ‖P‖ := norm_nonneg P
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hx1 : dist x z < δ₁ := lt_of_lt_of_le hxz (min_le_left _ _)
  have hx2 : dist x z < δ₂ := lt_of_lt_of_le hxz (min_le_right _ _)
  have hη : ∀ y : X, |l (x, y) - l (z, y)| ≤ η := by
    intro y
    have hd : dist ((x, y) : X × X) (z, y) < δ₁ := by
      rw [Prod.dist_eq]
      simpa using hx1
    have h := hl hd
    rw [Real.dist_eq] at h
    exact h.le
  refine lt_of_le_of_lt (abs_product_sub_le hg l P u hη0.le hη) ?_
  have hterm1 : rowBound ν g * (‖P‖ * (η * ‖u‖)) ≤ ε / 2 := by
    have hmono : rowBound ν g * (‖P‖ * (η * ‖u‖))
        ≤ (rowBound ν g + 1) * ((Cp + 1) * (Cu + 1)) * η := by
      have hPu : ‖P‖ * ‖u‖ ≤ (Cp + 1) * (Cu + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hP) hu0, mul_nonneg hCp0 (sub_nonneg.2 hu)]
      have h1 : rowBound ν g * (‖P‖ * ‖u‖) ≤ (rowBound ν g + 1) * ((Cp + 1) * (Cu + 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hPu hc0, mul_nonneg hP0 hu0,
          mul_nonneg (add_nonneg hCp0 zero_le_one) (add_nonneg hCu0 zero_le_one)]
      calc rowBound ν g * (‖P‖ * (η * ‖u‖)) = rowBound ν g * (‖P‖ * ‖u‖) * η := by ring
        _ ≤ (rowBound ν g + 1) * ((Cp + 1) * (Cu + 1)) * η :=
            mul_le_mul_of_nonneg_right h1 hη0.le
    refine hmono.trans (le_of_eq ?_)
    rw [hηdef]
    field_simp
  have hterm2 : (∫ y, |g (x, y) - g (z, y)| ∂ν) * (‖P‖ * (‖l‖ * ‖u‖)) < ε / 2 := by
    have hI := hgd x z hx2
    have hI0 : (0 : ℝ) ≤ ∫ y, |g (x, y) - g (z, y)| ∂ν := integral_nonneg fun _ => abs_nonneg _
    have hlu : ‖l‖ * ‖u‖ ≤ (‖l‖ + 1) * (Cu + 1) := by
      nlinarith [mul_nonneg hl0 (sub_nonneg.2 hu), hu0, hCu0]
    have hb : ‖P‖ * (‖l‖ * ‖u‖) ≤ (Cp + 1) * ((‖l‖ + 1) * (Cu + 1)) := by
      nlinarith [mul_le_mul_of_nonneg_left hlu hP0, mul_nonneg hl0 hu0,
        mul_nonneg (add_nonneg hl0 zero_le_one) (add_nonneg hCu0 zero_le_one)]
    have hb0 : (0 : ℝ) < (Cp + 1) * ((‖l‖ + 1) * (Cu + 1)) := by positivity
    calc (∫ y, |g (x, y) - g (z, y)| ∂ν) * (‖P‖ * (‖l‖ * ‖u‖))
        ≤ (∫ y, |g (x, y) - g (z, y)| ∂ν) * ((Cp + 1) * ((‖l‖ + 1) * (Cu + 1))) :=
          mul_le_mul_of_nonneg_left hb hI0
      _ < ε / (2 * ((Cp + 1) * ((‖l‖ + 1) * (Cu + 1)))) *
            ((Cp + 1) * ((‖l‖ + 1) * (Cu + 1))) :=
          mul_lt_mul_of_pos_right hI hb0
      _ = ε / 2 := by field_simp
  linarith

/-- The value `K_n u (x)` depends continuously on `x`. -/
theorem continuous_product (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (u : C(X, ℝ)) :
    Continuous fun x => ∫ y, g (x, y) * (P (prodFactor l x u)) y ∂ν := by
  refine Metric.continuous_iff.2 fun x₀ ε hε => ?_
  obtain ⟨δ, hδ, hbound⟩ :=
    exists_delta_product hg l (Cp := ‖P‖) (Cu := ‖u‖) (norm_nonneg P) (norm_nonneg u) hε
  refine ⟨δ, hδ, fun x hx => ?_⟩
  rw [Real.dist_eq]
  exact hbound P le_rfl u le_rfl x x₀ hx

/-- **The product integration operator** `K_n u (x) = ∫ [l (x, ·) u (·)]_n (y) g (x, y) dy` of
(12.5.14), with an arbitrary bounded `P` in place of the interpolation `[·]_n`.

It is *not* an instance of the Nyström operator `IntegralOperator.nystromCLM`: the weights
`∫ g (x, y) φ_j (y) dy` depend on the evaluation point `x`. -/
noncomputable def productCLM (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun x => ∫ y, g (x, y) * (P (prodFactor l x u)) y ∂ν,
        continuous_product hg l P u⟩
      map_add' := fun u v => by
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
        rw [prodFactor_add, map_add,
          ← integral_add (hg.integrable_mul _ x) (hg.integrable_mul _ x)]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [ContinuousMap.add_apply]
        ring
      map_smul' := fun r u => by
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [prodFactor_smul, map_smul, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring }
    (rowBound ν g * (‖P‖ * ‖l‖)) fun u => by
      have hnn : (0 : ℝ) ≤ rowBound ν g * (‖P‖ * ‖l‖) * ‖u‖ := by
        have := hg.rowBound_nonneg (μ := ν) (k := g)
        positivity
      rw [ContinuousMap.norm_le _ hnn]
      intro x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk, Real.norm_eq_abs]
      refine (hg.abs_integral_mul_le _ x).trans ?_
      have hn : ‖P (prodFactor l x u)‖ ≤ ‖P‖ * (‖l‖ * ‖u‖) :=
        (P.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (norm_prodFactor_le l x u) (norm_nonneg P))
      calc (∫ y, |g (x, y)| ∂ν) * ‖P (prodFactor l x u)‖
          ≤ rowBound ν g * (‖P‖ * (‖l‖ * ‖u‖)) :=
            mul_le_mul (hg.le_rowBound x) hn (norm_nonneg _) hg.rowBound_nonneg
        _ = rowBound ν g * (‖P‖ * ‖l‖) * ‖u‖ := by ring

/-- The defining formula of `productCLM`. -/
@[simp]
theorem productCLM_apply (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (u : C(X, ℝ)) (x : X) :
    productCLM hg l P u x = ∫ y, g (x, y) * (P (prodFactor l x u)) y ∂ν := rfl

/-- `‖K_n‖ ≤ c_g ‖P‖ c_l`, the uniform bound of the proof of Theorem 12.5.1. -/
theorem norm_productCLM_le (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) :
    ‖productCLM hg l P‖ ≤ rowBound ν g * (‖P‖ * ‖l‖) := by
  refine LinearMap.mkContinuous_norm_le _ ?_ _
  have := hg.rowBound_nonneg (μ := ν) (k := g)
  positivity

/-- **The exact operator is the product operator of the identity**: with no interpolation the
product rule is the integral operator of the kernel `l g` itself, which by the splitting rule
`IntegralOperator.IsAdmissibleKernel.mul_continuousMap` is admissible. -/
theorem productCLM_one (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ)) :
    productCLM hg l 1 = admissibleKernelCLM (hg.mul_continuousMap l) := by
  ext u x
  rw [productCLM_apply, admissibleKernelCLM_apply]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [one_apply_eq_self, prodFactor_apply]
  ring

/-- **Assumption A2, Exercise 12.5.1**: the product operators converge pointwise to the exact
operator.  The estimate `|K_n u (x) - K u (x)| ≤ c_g ‖P_n w_x - w_x‖` is uniform in `x` because
`{w_x = l (x, ·) u (·) : x ∈ X}` is a compact subset of `C(X, ℝ)`, on which the projections
converge uniformly by Lemma 12.1.3. -/
theorem tendsto_productCLM (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    {P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)} (hP : ∀ v : C(X, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v))
    (u : C(X, ℝ)) :
    Tendsto (fun n => productCLM hg l (P n) u) atTop (𝓝 (productCLM hg l 1 u)) := by
  have hc0 : (0 : ℝ) ≤ rowBound ν g := hg.rowBound_nonneg
  have hS : IsCompact (Set.range fun x : X => prodFactor l x u) :=
    isCompact_range (continuous_prodFactor l u)
  have huni : TendstoUniformlyOn (fun n => ((P n : C(X, ℝ) → C(X, ℝ))))
      ((1 : C(X, ℝ) →L[ℝ] C(X, ℝ)) : C(X, ℝ) → C(X, ℝ)) atTop
      (Set.range fun x : X => prodFactor l x u) :=
    lemma_12_1_3 (fun v => by simpa using hP v) hS
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (Metric.tendstoUniformlyOn_iff.1 huni (ε / (rowBound ν g + 1)) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  have hbound : ∀ x : X, ‖P n (prodFactor l x u) - prodFactor l x u‖
      < ε / (rowBound ν g + 1) := by
    intro x
    have h := hN n hn (prodFactor l x u) ⟨x, rfl⟩
    rw [dist_comm, dist_eq_norm] at h
    simpa using h
  rw [dist_eq_norm]
  have hle : ‖productCLM hg l (P n) u - productCLM hg l 1 u‖
      ≤ rowBound ν g * (ε / (rowBound ν g + 1)) := by
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro x
    have hdiff : (productCLM hg l (P n) u - productCLM hg l 1 u) x
        = ∫ y, g (x, y) * (P n (prodFactor l x u) - prodFactor l x u) y ∂ν := by
      rw [ContinuousMap.sub_apply, productCLM_apply, productCLM_apply,
        ← integral_sub (hg.integrable_mul _ x) (hg.integrable_mul _ x)]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [ContinuousMap.sub_apply, one_apply_eq_self]
      ring
    rw [hdiff, Real.norm_eq_abs]
    refine (hg.abs_integral_mul_le _ x).trans ?_
    have hn' : ‖P n (prodFactor l x u) - prodFactor l x u‖ ≤ ε / (rowBound ν g + 1) :=
      (hbound x).le
    exact mul_le_mul (hg.le_rowBound x) hn' (norm_nonneg _) hc0
  refine lt_of_le_of_lt hle ?_
  rw [mul_div_assoc'] at *
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hε.le]

/-- **Assumptions A1–A3 for the product integration family** (the proof of Theorem 12.5.1): the
operators `K_n` are collectively compact and converge pointwise to `K`.

Uniform boundedness is `norm_productCLM_le`, equicontinuity is `exists_delta_product`, and
pointwise convergence is `tendsto_productCLM`. -/
theorem isCollectivelyCompactFamily_productCLM (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    {P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)} {Cp : ℝ} (hCp : ∀ n, ‖P n‖ ≤ Cp)
    (hP : ∀ v : C(X, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v)) :
    IsCollectivelyCompactFamily (fun n => productCLM hg l (P n)) (productCLM hg l 1) := by
  have hc0 : (0 : ℝ) ≤ rowBound ν g := hg.rowBound_nonneg
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (norm_nonneg _) (hCp 0)
  refine ⟨fun v => tendsto_productCLM hg l hP v, ?_⟩
  refine ContinuousMap.isCompact_closure_of_forall_norm_le
    (M := rowBound ν g * (Cp * ‖l‖)) ?_ ?_
  · rintro f hf x
    obtain ⟨n, hfn⟩ := Set.mem_iUnion.1 hf
    obtain ⟨u, hu, rfl⟩ := hfn
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    calc ‖productCLM hg l (P n) u x‖ ≤ ‖productCLM hg l (P n) u‖ :=
          (productCLM hg l (P n) u).norm_coe_le_norm x
      _ ≤ rowBound ν g * (‖P n‖ * ‖l‖) * ‖u‖ :=
          ((productCLM hg l (P n)).le_opNorm u).trans
            (mul_le_mul_of_nonneg_right (norm_productCLM_le hg l (P n)) (norm_nonneg u))
      _ ≤ rowBound ν g * (Cp * ‖l‖) := by
          have h1 : rowBound ν g * (‖P n‖ * ‖l‖) ≤ rowBound ν g * (Cp * ‖l‖) := by
            gcongr
            exact hCp n
          nlinarith [norm_nonneg u, norm_nonneg l, norm_nonneg (P n),
            mul_nonneg hc0 (mul_nonneg hCp0 (norm_nonneg l))]
  · intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ :=
      exists_delta_product hg l (Cp := Cp) (Cu := 1) hCp0 zero_le_one hε
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
    rintro ⟨f, hf⟩
    obtain ⟨n, hfn⟩ := Set.mem_iUnion.1 hf
    obtain ⟨u, hu, rfl⟩ := hfn
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    rw [Real.dist_eq]
    exact hbound (P n) (hCp n) u hu1 x₀ x (by rw [dist_comm]; exact mem_ball.1 hx)

end Kernel

end ProductIntegration

/-! ### Theorem 12.5.1 -/

section Theorem1

open IntegralOperator MeasureTheory

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {ν : Measure X} {g : X × X → ℝ}

/-- **Theorem 12.5.1, the convergence of product integration.**  Let `g` satisfy the two
weak-singularity conditions (12.5.15)–(12.5.16) — that is, let `g` be an admissible kernel — let
`l` be continuous, and let `K` be the integral operator of `k = l g`.  Let `λ ≠ 0` be such that
`λ - K` is invertible, and let `K_n` be the product rule obtained by replacing `l (x, ·) u (·)` by
`P_n (l (x, ·) u (·))` for a sequence of operators of uniformly bounded norm converging pointwise
to the identity — the piecewise linear interpolants of (12.5.4), for instance.

Then there is a constant `c` such that for all large `n` the operator `λ - K_n` is invertible with
`‖(λ - K_n)⁻¹‖ ≤ c`, so the approximating equations are uniquely solvable, and

`‖u - u_n‖_∞ ≤ c ‖K u - K_n u‖_∞`,   (12.5.17)

the consistency error at the exact solution.

The proof is the book's: `isCollectivelyCompactFamily_productCLM` verifies A1–A3, and the abstract
`exists_norm_inverse_le_of_isCollectivelyCompactFamily` of §12.4.3 — Lemma 12.4.7 followed by
Theorem 12.4.4 — does the rest. -/
theorem theorem_12_5_1 (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    {P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)} {Cp : ℝ} (hCp : ∀ n, ‖P n‖ ≤ Cp)
    (hP : ∀ v : C(X, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v))
    {μ : ℝ} (hμ : μ ≠ 0) {e : C(X, ℝ) ≃L[ℝ] C(X, ℝ)}
    (he : (e : C(X, ℝ) →L[ℝ] C(X, ℝ))
      = μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l)) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : C(X, ℝ) ≃L[ℝ] C(X, ℝ),
      (en : C(X, ℝ) →L[ℝ] C(X, ℝ)) = μ • 1 - productCLM hg l (P n) ∧
        ‖(en.symm : C(X, ℝ) →L[ℝ] C(X, ℝ))‖ ≤ c ∧
        ∀ f u un : C(X, ℝ),
          (μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l) :
            C(X, ℝ) →L[ℝ] C(X, ℝ)) u = f →
          (μ • 1 - productCLM hg l (P n) : C(X, ℝ) →L[ℝ] C(X, ℝ)) un = f →
          ‖u - un‖ ≤ c * ‖admissibleKernelCLM (hg.mul_continuousMap l) u
            - productCLM hg l (P n) u‖ := by
  have hone := productCLM_one hg l
  have hfam := isCollectivelyCompactFamily_productCLM hg l hCp hP
  rw [hone] at hfam
  exact exists_norm_inverse_le_of_isCollectivelyCompactFamily hμ hfam he

end Theorem1

/-! ### Example 12.5.2: the product trapezoidal rule -/

section Trapezoidal

open IntegralOperator MeasureTheory

variable {a b : ℝ}

/-- **Example 12.5.2, the rate of the product trapezoidal rule (12.5.18).**  Take for `P_n` the
piecewise linear interpolation at the breakpoints of a partition of `[a, b]` whose mesh `h_n` tends
to zero.  Then Theorem 12.5.1 applies — the interpolation operators have norm one and converge
pointwise — and, whenever `y ↦ l (x, y) u (y)` is `C²` with second derivative bounded by `M₂`
uniformly in `x`,

`‖u - u_n‖_∞ ≤ c (h_n²/8) M₂`.

The interpolation error `‖z - P_n z‖ ≤ h² ‖z''‖/8` is `norm_sub_piecewiseLinearInterpCLM_le`, and
the constant `c` absorbs the uniform bound on `‖(λ - K_n)⁻¹‖` and the row bound `c_g` of the
singular factor. -/
theorem example_12_5_2 {g : Set.Icc a b × Set.Icc a b → ℝ}
    (hg : IsAdmissibleKernel (iccMeasure a b) g) (l : C(Set.Icc a b × Set.Icc a b, ℝ))
    {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) {μ : ℝ} (hμ : μ ≠ 0)
    {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l)) :
    ∃ c : ℝ, ∀ᶠ n in atTop,
      (∀ f : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
        (μ • 1 - productCLM hg l (piecewiseLinearInterpCLM (N n) (y n)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f) ∧
      ∀ (G : Set.Icc a b → ℝ → ℝ) (M₂ : ℝ) (f u un : C(Set.Icc a b, ℝ)),
        (∀ x, ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (G x)) →
        (∀ x, ∀ t : Set.Icc a b, l (x, t) * u t = G x (t : ℝ)) →
        (∀ x, ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 (G x) t| ≤ M₂) →
        (μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f →
        (μ • 1 - productCLM hg l (piecewiseLinearInterpCLM (N n) (y n)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f →
        ‖u - un‖ ≤ c * (h n ^ 2 / 8 * M₂) := by
  classical
  have hc0 : (0 : ℝ) ≤ rowBound (iccMeasure a b) g := hg.rowBound_nonneg
  set P : ℕ → C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
    fun n => piecewiseLinearInterpCLM (N n) (y n) with hPdef
  have hnormP : ∀ n, ‖P n‖ = 1 := fun n =>
    norm_piecewiseLinearInterpCLM (hstep n) (hfirst n) (hlast n)
  have hCp : ∀ n, ‖P n‖ ≤ 1 := fun n => le_of_eq (hnormP n)
  have hPconv : ∀ v : C(Set.Icc a b, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v) :=
    tendsto_piecewiseLinearInterpCLM hstep hfirst hlast hmesh hh
  obtain ⟨c, hc⟩ := theorem_12_5_1 hg l hCp hPconv hμ he
  refine ⟨c * rowBound (iccMeasure a b) g, ?_⟩
  filter_upwards [hc] with n hn
  obtain ⟨en, hencoe, hennorm, herr⟩ := hn
  have hsolve : ∀ f : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
      (μ • 1 - productCLM hg l (P n) :
        C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f := by
    intro f
    have hiff : ∀ z : C(Set.Icc a b, ℝ), (en z = f)
        ↔ ((μ • 1 - productCLM hg l (P n) :
            C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) z = f) := by
      intro z
      rw [← hencoe, ContinuousLinearEquiv.coe_coe]
    have huniq : ∃! z : C(Set.Icc a b, ℝ), en z = f :=
      ⟨en.symm f, en.apply_symm_apply f, fun z hz => by rw [← hz, en.symm_apply_apply]⟩
    simpa only [hiff] using huniq
  refine ⟨hsolve, fun G M₂ f u un hG hGval hM₂ hu hun => ?_⟩
  -- the consistency error is the interpolation error of `l (x, ·) u (·)`, uniformly in `x`
  have hcons : ‖admissibleKernelCLM (hg.mul_continuousMap l) u - productCLM hg l (P n) u‖
      ≤ rowBound (iccMeasure a b) g * (h n ^ 2 / 8 * M₂) := by
    have hM0 : (0 : ℝ) ≤ h n ^ 2 / 8 * M₂ := by
      have h1 : (0 : ℝ) ≤ M₂ :=
        le_trans (abs_nonneg _) (hM₂ (y n 0) ((y n 0 : ℝ)) (y n 0).2)
      positivity
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro x
    have hdiff : (admissibleKernelCLM (hg.mul_continuousMap l) u - productCLM hg l (P n) u) x
        = ∫ z, g (x, z) * (prodFactor l x u - P n (prodFactor l x u)) z ∂iccMeasure a b := by
      rw [ContinuousMap.sub_apply, ← productCLM_one hg l, productCLM_apply, productCLM_apply,
        ← integral_sub (hg.integrable_mul _ x) (hg.integrable_mul _ x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [ContinuousMap.sub_apply, one_apply_eq_self]
      ring
    rw [hdiff, Real.norm_eq_abs]
    refine (hg.abs_integral_mul_le _ x).trans ?_
    have hinterp : ‖prodFactor l x u - P n (prodFactor l x u)‖ ≤ h n ^ 2 / 8 * M₂ :=
      norm_sub_piecewiseLinearInterpCLM_le (hstep n) (hfirst n) (hlast n) (hG x)
        (f := prodFactor l x u) (fun t => hGval x t) (hmesh n) (hM₂ x)
    exact mul_le_mul (hg.le_rowBound x) hinterp (norm_nonneg _) hc0
  calc ‖u - un‖
      ≤ c * ‖admissibleKernelCLM (hg.mul_continuousMap l) u - productCLM hg l (P n) u‖ :=
        herr f u un hu hun
    _ ≤ c * (rowBound (iccMeasure a b) g * (h n ^ 2 / 8 * M₂)) :=
        mul_le_mul_of_nonneg_left hcons (le_trans (norm_nonneg _) hennorm)
    _ = c * rowBound (iccMeasure a b) g * (h n ^ 2 / 8 * M₂) := by ring

end Trapezoidal

end AtkinsonHan.Chapter12
