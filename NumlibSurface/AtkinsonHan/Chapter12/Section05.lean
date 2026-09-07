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
* `isPanelNodes_graded` and `lemma_12_5_5` — Rice's graded mesh `x_j = (j/n)^q` of (12.5.30) and
  the interpolation error (12.5.35) `‖u - P_n u‖_∞ ≤ c n^{-(m+1)}` for a function of type
  `(γ, m + 1)`, once `q ≥ (m + 1)/γ`.  The book states the lemma without proof.
* `isPanelNodes_gradedSym` and `norm_sub_gradedSym_le` — the same on the mesh of the paragraph
  preceding Theorem 12.5.6, graded towards *both* endpoints of `[a, b]`, with an explicit constant
  so that it applies uniformly to the row functions `y ↦ l (x, y) u (y)`.
* `theorem_12_5_6` — the convergence (12.5.41) `‖u - u_n‖_∞ ≤ c n^{-(m+1)}` of graded-mesh
  product integration, with the regularity of Theorem 12.5.4 taken as a hypothesis, which is what
  the book's own use of it amounts to.

## Not formalized here

* Theorem 12.5.4, the regularity of the solution of a weakly singular equation.  It is the one
  item of the chapter whose *mathematics*, and not merely whose supporting API, is missing: the
  book proves it by differentiating `u = (f + K u)/λ` under the singular integral sign and
  bootstrapping, and nothing in `Numlib/IntegralEquations/WeaklySingular` touches
  differentiability.  `theorem_12_5_6` therefore takes its conclusion as a hypothesis.
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

/-! ### Graded meshes and Lemma 12.5.5 -/

section GradedMesh

/-- **The mean value bound for a real power.** For `q ≥ 1` and `0 < B < A`,
`A^q - B^q ≤ q A^{q-1} (A - B)`. -/
private theorem rpow_sub_rpow_le {A B q : ℝ} (hq : 1 ≤ q) (hB : 0 < B) (hBA : B < A) :
    A ^ q - B ^ q ≤ q * A ^ (q - 1) * (A - B) := by
  have hderiv : ∀ s ∈ Set.Icc B A, HasDerivAt (fun y : ℝ => y ^ q) (q * s ^ (q - 1)) s :=
    fun s _ => Real.hasDerivAt_rpow_const (Or.inr hq)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => y ^ q)
    (fun s => q * s ^ (q - 1)) hBA
    (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs => hderiv s (Set.Ioo_subset_Icc_self hs))
  have hsub : (0 : ℝ) < A - B := by linarith
  have hξA : ξ ^ (q - 1) ≤ A ^ (q - 1) :=
    Real.rpow_le_rpow (hB.trans hξ.1).le hξ.2.le (by linarith)
  rw [eq_div_iff (ne_of_gt hsub)] at hξeq
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hkey : 0 ≤ q * (A ^ (q - 1) - ξ ^ (q - 1)) * (A - B) :=
    mul_nonneg (mul_nonneg hq0 (by linarith)) hsub.le
  linarith [hkey, hξeq]

/-- **The graded-mesh panel estimate.**  On the mesh `x_j = (j/n)^q`, if `q γ ≥ m + 1` then
`(x_{j+1} - x_j)^{m+1} x_j^{γ - (m+1)} ≤ (q 2^{q-1})^{m+1} n^{-(m+1)}` for every panel that does
not touch the origin.

This is where the grading pays for the singularity: the panel length is `𝒪(j^{q-1} n^{-q})` by the
mean value theorem, and the singular factor `x_j^{γ-(m+1)}` is `(j/n)^{q(γ-m-1)}`, so the powers of
`j` combine into `(j/n)^{qγ-(m+1)} ≤ 1` exactly when `q ≥ (m+1)/γ`. -/
private theorem graded_panel_le {m : ℕ} {γ q n A B : ℝ} (hq1 : 1 ≤ q)
    (hqγ : ((m : ℝ) + 1) ≤ q * γ) (hn0 : 0 < n) (hB0 : 0 < B) (hBA : B < A) (hA1 : A ≤ 1)
    (hAB : A - B = 1 / n) (hA2B : A ≤ 2 * B) :
    (A ^ q - B ^ q) ^ (m + 1) * ((B ^ q) ^ (γ - ((m : ℝ) + 1)))
      ≤ (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hA0 : (0 : ℝ) < A := hB0.trans hBA
  have hB1 : B ≤ 1 := (hBA.le).trans hA1
  have hh0 : 0 ≤ A ^ q - B ^ q := by
    have := Real.rpow_le_rpow hB0.le hBA.le hq0.le
    linarith
  have hstep : A ^ q - B ^ q ≤ q * 2 ^ (q - 1) * B ^ (q - 1) / n := by
    have h2 : A ^ (q - 1) ≤ 2 ^ (q - 1) * B ^ (q - 1) := by
      rw [← Real.mul_rpow (by norm_num) hB0.le]
      exact Real.rpow_le_rpow hA0.le hA2B (by linarith)
    calc A ^ q - B ^ q ≤ q * A ^ (q - 1) * (A - B) := rpow_sub_rpow_le hq1 hB0 hBA
      _ = q * A ^ (q - 1) / n := by rw [hAB]; ring
      _ ≤ q * (2 ^ (q - 1) * B ^ (q - 1)) / n := by gcongr
      _ = q * 2 ^ (q - 1) * B ^ (q - 1) / n := by ring
  have hpow : (A ^ q - B ^ q) ^ (m + 1)
      ≤ (q * 2 ^ (q - 1)) ^ (m + 1) * (B ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := by
    calc (A ^ q - B ^ q) ^ (m + 1) ≤ (q * 2 ^ (q - 1) * B ^ (q - 1) / n) ^ (m + 1) := by
          gcongr
      _ = (q * 2 ^ (q - 1)) ^ (m + 1) * (B ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := by
          rw [div_pow, mul_pow]
  have hBrpow : (B ^ (q - 1)) ^ (m + 1) * ((B ^ q) ^ (γ - ((m : ℝ) + 1)))
      = B ^ (q * γ - ((m : ℝ) + 1)) := by
    rw [← Real.rpow_natCast (B ^ (q - 1)) (m + 1), ← Real.rpow_mul hB0.le,
      ← Real.rpow_mul hB0.le, ← Real.rpow_add hB0]
    congr 1
    push_cast
    ring
  have hBle : B ^ (q * γ - ((m : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one hB0.le hB1 (by linarith)
  have hfac0 : (0 : ℝ) ≤ (B ^ q) ^ (γ - ((m : ℝ) + 1)) := Real.rpow_nonneg (by positivity) _
  have hc0 : (0 : ℝ) ≤ (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := by positivity
  calc (A ^ q - B ^ q) ^ (m + 1) * ((B ^ q) ^ (γ - ((m : ℝ) + 1)))
      ≤ ((q * 2 ^ (q - 1)) ^ (m + 1) * (B ^ (q - 1)) ^ (m + 1) / n ^ (m + 1))
          * ((B ^ q) ^ (γ - ((m : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_right hpow hfac0
    _ = (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) * B ^ (q * γ - ((m : ℝ) + 1)) := by
        rw [← hBrpow]
        ring
    _ ≤ (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) * 1 :=
        mul_le_mul_of_nonneg_left hBle hc0
    _ = (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := mul_one _

/-- **The graded mesh and its nodes form a panel node system.**  The mesh is Rice's
`x_j = (j/n)^q` of (12.5.30) with `n = N + 1` panels, and the nodes of the panel
`[x_j, x_{j+1}]` are the images `x_{ji} = x_{j-1} + μ_i h_j` of a fixed partition
`0 = μ_0 < ⋯ < μ_m = 1` of the unit interval, as in (12.5.31)–(12.5.32). -/
theorem isPanelNodes_graded {m N : ℕ} {q : ℝ} (hq1 : 1 ≤ q) {μ : Fin (m + 1) → ℝ}
    (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {x : ℕ → Set.Icc (0 : ℝ) 1} {node : ℕ → Fin (m + 1) → Set.Icc (0 : ℝ) 1}
    (hx : ∀ j ≤ N + 1, (x j : ℝ) = ((j : ℝ) / ((N : ℝ) + 1)) ^ q)
    (hnode : ∀ j ≤ N, ∀ i, (node j i : ℝ)
      = (x j : ℝ) + μ i * ((x (j + 1) : ℝ) - (x j : ℝ))) :
    IsPanelNodes N m x node := by
  have hn0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hstep : ∀ j ≤ N, (x j : ℝ) < (x (j + 1) : ℝ) := by
    intro j hj
    rw [hx j (by omega), hx (j + 1) (by omega)]
    refine Real.rpow_lt_rpow (by positivity) ?_ hq0
    push_cast
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    gcongr
    linarith
  have hμmem : ∀ i : Fin (m + 1), μ i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    constructor
    · rw [← hμ0]
      exact hμmono.monotone (Fin.zero_le i)
    · rw [← hμ1]
      exact hμmono.monotone (Fin.le_last i)
  refine ⟨hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx 0 (by omega), Nat.cast_zero, zero_div, Real.zero_rpow (ne_of_gt hq0)]
  · rw [hx (N + 1) (by omega)]
    push_cast
    rw [div_self (ne_of_gt hn0), Real.one_rpow]
  · intro j hj i
    have hd : (0 : ℝ) ≤ (x (j + 1) : ℝ) - (x j : ℝ) := sub_nonneg.mpr (hstep j hj).le
    rw [hnode j hj i]
    constructor <;> nlinarith [(hμmem i).1, (hμmem i).2]
  · intro j hj i i' hii
    simp only at hii
    have hd : (0 : ℝ) < (x (j + 1) : ℝ) - (x j : ℝ) := sub_pos.mpr (hstep j hj)
    rw [hnode j hj i, hnode j hj i'] at hii
    refine hμmono.injective (mul_right_cancel₀ (ne_of_gt hd) ?_)
    linarith
  · intro j hj
    refine Subtype.ext ?_
    rw [hnode j hj 0, hμ0]
    ring
  · intro j hj
    refine Subtype.ext ?_
    rw [hnode j hj (Fin.last m), hμ1]
    ring

/-- **Lemma 12.5.5**, Rice's graded-mesh interpolation error.  For `0 < γ < 1` let `u` be of Rice's
type `(γ, m + 1)` on `[0, 1]` — Hölder continuous with exponent `γ`, of class `C^{m+1}` on `(0, 1]`
and with `|u^{(m+1)}(s)| ≤ c s^{γ - (m+1)}` — and let `P_n` be piecewise polynomial interpolation
of degree `m` on the graded mesh `x_j = (j/n)^q` of (12.5.30), at nodes placed at fixed fractions
`0 = μ_0 < ⋯ < μ_m = 1` of each panel.  Then for `q ≥ (m + 1)/γ`,

`‖u - P_n u‖_∞ ≤ C n^{-(m+1)}`   (12.5.35)

with `C` independent of `n`.

The book states the lemma without proof, citing Rice and Atkinson.  The proof here is the standard
one: on the first panel `[0, x_1]` only the Hölder bound is available, and `x_1^γ = n^{-qγ} ≤
n^{-(m+1)}` is exactly what `q γ ≥ m + 1` buys; on every later panel the Lagrange error formula
applies — `u` is smooth there — and `graded_panel_le` says that the grading makes
`h_j^{m+1} x_j^{γ-(m+1)}` uniformly `𝒪(n^{-(m+1)})`.  The Lebesgue constants of the panels are
bounded uniformly because the nodes sit at fixed fractions of every panel. -/
theorem lemma_12_5_5 {m : ℕ} {γ q H c : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hq : ((m : ℝ) + 1) / γ ≤ q) {μ : Fin (m + 1) → ℝ}
    (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {U : ℝ → ℝ} {u : C(Set.Icc (0 : ℝ) 1, ℝ)} (hu : ∀ t : Set.Icc (0 : ℝ) 1, u t = U ((t : ℝ)))
    (hH : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |U s - U t| ≤ H * |s - t| ^ γ)
    (hUC : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) U (Set.Ioi 0))
    (hUd : ∀ s ∈ Set.Ioc (0 : ℝ) 1, |iteratedDeriv (m + 1) U s| ≤ c * s ^ (γ - ((m : ℝ) + 1)))
    {x : ℕ → ℕ → Set.Icc (0 : ℝ) 1} {node : ℕ → ℕ → Fin (m + 1) → Set.Icc (0 : ℝ) 1}
    (hx : ∀ N, ∀ j ≤ N + 1, (x N j : ℝ) = ((j : ℝ) / ((N : ℝ) + 1)) ^ q)
    (hnode : ∀ N, ∀ j ≤ N, ∀ i, (node N j i : ℝ)
      = (x N j : ℝ) + μ i * ((x N (j + 1) : ℝ) - (x N j : ℝ))) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖u - piecewisePolyInterpCLM N m (x N) (node N) u‖ ≤ C / ((N : ℝ) + 1) ^ (m + 1) := by
  classical
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hq1 : (1 : ℝ) ≤ q := by
    have h2 : (1 : ℝ) < ((m : ℝ) + 1) / γ := by
      rw [lt_div_iff₀ hγ0]
      linarith
    linarith
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hqγ : ((m : ℝ) + 1) ≤ q * γ := by
    rw [div_le_iff₀ hγ0] at hq
    linarith
  have hH0 : 0 ≤ H := by
    have h := hH 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    rw [show |(0 : ℝ) - 1| = 1 by norm_num, Real.one_rpow, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hc0 : 0 ≤ c := by
    have h := hUd 1 ⟨zero_lt_one, le_rfl⟩
    rw [Real.one_rpow, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hfact0 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  -- a uniform separation of the reference nodes
  obtain ⟨dμ, hdμ0, hdμ⟩ :
      ∃ d : ℝ, 0 < d ∧ ∀ i i' : Fin (m + 1), i ≠ i' → d ≤ |μ i - μ i'| := by
    by_cases hS : (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) => p.1 ≠ p.2).Nonempty
    · refine ⟨(Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) => p.1 ≠ p.2).inf' hS
        (fun p => |μ p.1 - μ p.2|), ?_, fun i i' hii => ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro p hp
        exact abs_pos.mpr (sub_ne_zero.mpr fun hcon =>
          (Finset.mem_filter.mp hp).2 (hμmono.injective hcon))
      · exact Finset.inf'_le (fun p : Fin (m + 1) × Fin (m + 1) => |μ p.1 - μ p.2|)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, i'), hii⟩)
    · exact ⟨1, one_pos, fun i i' hii =>
        absurd ⟨(i, i'), Finset.mem_filter.mpr ⟨Finset.mem_univ (i, i'), hii⟩⟩ hS⟩
  set Λ : ℝ := ((m : ℝ) + 1) * (1 / dμ) ^ m with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  set Cst : ℝ := (1 + Λ) * H + c * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial with hCstdef
  have hCst2 : (0 : ℝ) ≤ c * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial :=
    div_nonneg (mul_nonneg hc0 (pow_nonneg (by positivity) _)) hfact0.le
  have hCst0 : 0 ≤ Cst := by
    rw [hCstdef]
    have h1 : (0 : ℝ) ≤ (1 + Λ) * H := mul_nonneg (by linarith) hH0
    linarith
  refine ⟨Cst, fun N => ?_⟩
  have hn0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hnN : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hnodes := isPanelNodes_graded hq1 hμ0 hμ1 hμmono (hx N) (hnode N)
  have hΛb : IsPanelLebesgueBound N m (x N) (node N) Λ := by
    refine isPanelLebesgueBound_of_sep hnodes
      (d := fun j => dμ * ((x N (j + 1) : ℝ) - (x N j : ℝ))) (ρ := 1 / dμ)
      (fun j hj => mul_pos hdμ0 (sub_pos.mpr (hnodes.step j hj))) (fun j hj => ?_)
      (fun j hj i i' hii => ?_)
    · rw [← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hdμ0), one_mul]
    · have hd : (0 : ℝ) < (x N (j + 1) : ℝ) - (x N j : ℝ) := sub_pos.mpr (hnodes.step j hj)
      rw [hnode N j hj i, hnode N j hj i']
      have hrw : ((x N j : ℝ) + μ i * ((x N (j + 1) : ℝ) - (x N j : ℝ)))
          - ((x N j : ℝ) + μ i' * ((x N (j + 1) : ℝ) - (x N j : ℝ)))
          = (μ i - μ i') * ((x N (j + 1) : ℝ) - (x N j : ℝ)) := by ring
      rw [hrw, abs_mul, abs_of_pos hd]
      exact mul_le_mul_of_nonneg_right (hdμ i i' hii) hd.le
  rw [ContinuousMap.norm_le _ (div_nonneg hCst0 (by positivity))]
  intro t
  obtain ⟨k, hk, h1, h2⟩ := exists_mem_subinterval hnodes.first hnodes.last t
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- the first panel, where only the Hölder bound is available
    have hx0 : (x N 0 : ℝ) = 0 := hnodes.first
    have hx1 : (x N 1 : ℝ) = (1 / ((N : ℝ) + 1)) ^ q := by
      rw [hx N 1 (by omega)]
      norm_num
    have hosc : ∀ s : Set.Icc (0 : ℝ) 1, (x N 0 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (x N 1 : ℝ) →
        |u s - u (x N 0)| ≤ H * ((x N 1 : ℝ)) ^ γ := by
      intro s hs1 hs2
      rw [hx0] at hs1
      rw [hu s, hu (x N 0)]
      refine le_trans (hH ((s : ℝ)) s.2 ((x N 0 : ℝ)) (x N 0).2) ?_
      rw [hx0, sub_zero, abs_of_nonneg hs1]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs1 hs2 hγ0.le) hH0
    have hxγ : ((x N 1 : ℝ)) ^ γ ≤ 1 / ((N : ℝ) + 1) ^ (m + 1) := by
      have h1n : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      have h1n1 : (1 : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hn0]
        exact hnN
      rw [hx1, ← Real.rpow_mul h1n.le]
      calc (1 / ((N : ℝ) + 1)) ^ (q * γ)
          ≤ (1 / ((N : ℝ) + 1)) ^ (((m + 1 : ℕ) : ℝ)) := by
            refine Real.rpow_le_rpow_of_exponent_ge h1n h1n1 ?_
            push_cast
            linarith
        _ = 1 / ((N : ℝ) + 1) ^ (m + 1) := by rw [Real.rpow_natCast, div_pow, one_pow]
    refine (abs_sub_piecewisePolyInterpCLM_apply_le_of_osc hnodes hΛb u hk h1 h2 hosc).trans ?_
    have hxγ0 : (0 : ℝ) ≤ ((x N 1 : ℝ)) ^ γ := Real.rpow_nonneg (x N 1).2.1 γ
    calc (1 + Λ) * (H * ((x N 1 : ℝ)) ^ γ)
        ≤ (1 + Λ) * (H * (1 / ((N : ℝ) + 1) ^ (m + 1))) := by gcongr
      _ = (1 + Λ) * H / ((N : ℝ) + 1) ^ (m + 1) := by ring
      _ ≤ Cst / ((N : ℝ) + 1) ^ (m + 1) := by
          gcongr
          rw [hCstdef]
          linarith
  · -- a panel that stays away from the origin, where the Lagrange error formula applies
    have hkN : k ≤ N := hk
    have hB0 : (0 : ℝ) < (k : ℝ) / ((N : ℝ) + 1) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      positivity
    have hxk : (x N k : ℝ) = (((k : ℝ)) / ((N : ℝ) + 1)) ^ q := hx N k (by omega)
    have hxk1 : (x N (k + 1) : ℝ) = ((((k : ℝ)) + 1) / ((N : ℝ) + 1)) ^ q := by
      rw [hx N (k + 1) (by omega)]
      norm_cast
    have hxk0 : 0 < (x N k : ℝ) := by
      rw [hxk]
      exact Real.rpow_pos_of_pos hB0 q
    have hsubset : Set.Icc ((x N k : ℝ)) ((x N (k + 1) : ℝ)) ⊆ Set.Ioi 0 :=
      fun s hs => lt_of_lt_of_le hxk0 hs.1
    obtain ⟨ξ, hξ, hξeq⟩ := exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn hnodes
      isOpen_Ioi hk hsubset hUC hu h1 h2
    have hξ01 : ξ ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_trans hxk0 hξ.1, le_trans hξ.2.le (x N (k + 1)).2.2⟩
    have hdneg : γ - ((m : ℝ) + 1) ≤ 0 := by linarith
    have hderiv : |iteratedDeriv (m + 1) U ξ| ≤ c * ((x N k : ℝ)) ^ (γ - ((m : ℝ) + 1)) := by
      refine (hUd ξ hξ01).trans (mul_le_mul_of_nonneg_left ?_ hc0)
      exact Real.rpow_le_rpow_of_nonpos hxk0 hξ.1.le hdneg
    have hprod : |∏ i, ((t : ℝ) - ((node N k i : ℝ)))|
        ≤ ((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1) := by
      rw [Finset.abs_prod]
      calc ∏ i, |(t : ℝ) - ((node N k i : ℝ))|
          ≤ ∏ _i : Fin (m + 1), ((x N (k + 1) : ℝ) - (x N k : ℝ)) := by
            refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
            have hmi := hnodes.mem k hk i
            rw [abs_sub_le_iff]
            exact ⟨by linarith [hmi.1], by linarith [hmi.2]⟩
        _ = ((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkN' : (k : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hkN
    have hABeq : ((k : ℝ) + 1) / ((N : ℝ) + 1) - (k : ℝ) / ((N : ℝ) + 1)
        = 1 / ((N : ℝ) + 1) := by
      rw [div_sub_div_same]
      norm_num
    have hBA' : (k : ℝ) / ((N : ℝ) + 1) < ((k : ℝ) + 1) / ((N : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      linarith
    have hA1' : ((k : ℝ) + 1) / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn0]
      exact hkN'
    have hA2B' : ((k : ℝ) + 1) / ((N : ℝ) + 1) ≤ 2 * ((k : ℝ) / ((N : ℝ) + 1)) := by
      have hdiff : 2 * ((k : ℝ) / ((N : ℝ) + 1)) - ((k : ℝ) + 1) / ((N : ℝ) + 1)
          = ((k : ℝ) - 1) / ((N : ℝ) + 1) := by
        rw [← mul_div_assoc, div_sub_div_same]
        congr 1
        ring
      have hnn : (0 : ℝ) ≤ ((k : ℝ) - 1) / ((N : ℝ) + 1) := div_nonneg (by linarith) hn0.le
      linarith
    have hgraded := graded_panel_le (m := m) (γ := γ) (q := q) (n := (N : ℝ) + 1)
      (A := ((k : ℝ) + 1) / ((N : ℝ) + 1)) (B := (k : ℝ) / ((N : ℝ) + 1)) hq1 hqγ hn0 hB0
      hBA' hA1' hABeq hA2B'
    rw [← hxk, ← hxk1] at hgraded
    have hpanel0 : (0 : ℝ) ≤ ((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1) :=
      pow_nonneg (by linarith [hnodes.step k hk]) _
    rw [hξeq, abs_mul, abs_div, abs_of_pos hfact0]
    calc |iteratedDeriv (m + 1) U ξ| / ((m + 1).factorial : ℝ)
          * |∏ i, ((t : ℝ) - ((node N k i : ℝ)))|
        ≤ (c * ((x N k : ℝ)) ^ (γ - ((m : ℝ) + 1))) / ((m + 1).factorial : ℝ)
            * ((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1) := by gcongr
      _ = c / ((m + 1).factorial : ℝ) * (((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1)
            * ((x N k : ℝ)) ^ (γ - ((m : ℝ) + 1))) := by ring
      _ ≤ c / ((m + 1).factorial : ℝ)
            * ((q * 2 ^ (q - 1)) ^ (m + 1) / ((N : ℝ) + 1) ^ (m + 1)) := by gcongr
      _ = c * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial / ((N : ℝ) + 1) ^ (m + 1) := by
          ring
      _ ≤ Cst / ((N : ℝ) + 1) ^ (m + 1) := by
          gcongr
          rw [hCstdef]
          have h1 : (0 : ℝ) ≤ (1 + Λ) * H := mul_nonneg (by linarith) hH0
          linarith


end GradedMesh


/-! ### The symmetric graded mesh of §12.5.4 -/

section SymmetricGradedMesh

/-- The scaled form of `graded_panel_le`: the panel of the mesh `a + (j/r)^q S` obeys the same
bound, with an extra factor `S^γ`. -/
private theorem graded_panel_le' {m : ℕ} {γ q n A B S : ℝ} (hq1 : 1 ≤ q)
    (hqγ : ((m : ℝ) + 1) ≤ q * γ) (hn0 : 0 < n) (hS0 : 0 < S) (hB0 : 0 < B) (hBA : B < A)
    (hA1 : A ≤ 1) (hAB : A - B = 1 / n) (hA2B : A ≤ 2 * B) :
    (S * A ^ q - S * B ^ q) ^ (m + 1) * ((S * B ^ q) ^ (γ - ((m : ℝ) + 1)))
      ≤ S ^ γ * ((q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1)) := by
  have hSγ : S ^ (m + 1) * (S : ℝ) ^ (γ - ((m : ℝ) + 1)) = S ^ γ := by
    rw [← Real.rpow_natCast S (m + 1), ← Real.rpow_add hS0]
    congr 1
    push_cast
    ring
  have hS0' : (0 : ℝ) ≤ S ^ γ := Real.rpow_nonneg hS0.le γ
  have hfac : (S * A ^ q - S * B ^ q) ^ (m + 1) = S ^ (m + 1) * (A ^ q - B ^ q) ^ (m + 1) := by
    rw [← mul_sub, mul_pow]
  have hfac2 : (S * B ^ q) ^ (γ - ((m : ℝ) + 1))
      = S ^ (γ - ((m : ℝ) + 1)) * (B ^ q) ^ (γ - ((m : ℝ) + 1)) :=
    Real.mul_rpow hS0.le (Real.rpow_nonneg hB0.le q)
  rw [hfac, hfac2]
  calc S ^ (m + 1) * (A ^ q - B ^ q) ^ (m + 1)
        * (S ^ (γ - ((m : ℝ) + 1)) * (B ^ q) ^ (γ - ((m : ℝ) + 1)))
      = (S ^ (m + 1) * S ^ (γ - ((m : ℝ) + 1)))
          * ((A ^ q - B ^ q) ^ (m + 1) * (B ^ q) ^ (γ - ((m : ℝ) + 1))) := by ring
    _ = S ^ γ * ((A ^ q - B ^ q) ^ (m + 1) * (B ^ q) ^ (γ - ((m : ℝ) + 1))) := by rw [hSγ]
    _ ≤ S ^ γ * ((q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left
          (graded_panel_le hq1 hqγ hn0 hB0 hBA hA1 hAB hA2B) hS0'

variable {a b : ℝ} {m r N : ℕ} {q : ℝ}

/-- **The symmetric graded mesh and its nodes form a panel node system.**  The `n = 2 r` panels of
`[a, b]` are graded towards both endpoints — `x_j = a + (2j/n)^q (b-a)/2` for `j ≤ n/2` and
`x_{n-j} = a + b - x_j` — and the nodes of a panel are the images of the partition `μ` on the left
half and of its reflection `1 - μ_{m-i}` on the right, as in the paragraph preceding Theorem
12.5.6. -/
theorem isPanelNodes_gradedSym (hab : a < b) (hr : 0 < r) (hN : N + 1 = 2 * r) (hq1 : 1 ≤ q)
    {μ : Fin (m + 1) → ℝ} (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {x : ℕ → Set.Icc a b} {node : ℕ → Fin (m + 1) → Set.Icc a b}
    (hxL : ∀ j ≤ r, (x j : ℝ) = a + ((j : ℝ) / r) ^ q * ((b - a) / 2))
    (hxR : ∀ j ≤ r, (x (2 * r - j) : ℝ) = a + b - (x j : ℝ))
    (hnodeL : ∀ j < r, ∀ i, (node j i : ℝ)
      = (x j : ℝ) + μ i * ((x (j + 1) : ℝ) - (x j : ℝ)))
    (hnodeR : ∀ j, r ≤ j → j ≤ N → ∀ i, (node j i : ℝ)
      = (x j : ℝ) + (1 - μ i.rev) * ((x (j + 1) : ℝ) - (x j : ℝ))) :
    IsPanelNodes N m x node := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hS0 : (0 : ℝ) < (b - a) / 2 := by linarith
  -- the left half increases
  have hstepL : ∀ j < r, (x j : ℝ) < (x (j + 1) : ℝ) := by
    intro j hj
    rw [hxL j (by omega), hxL (j + 1) (by omega)]
    have hlt : ((j : ℝ) / r) ^ q < (((j : ℝ) + 1) / r) ^ q := by
      refine Real.rpow_lt_rpow (by positivity) ?_ hq0
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      gcongr
      linarith
    push_cast
    nlinarith [hlt, hS0]
  -- the reflection identities for a panel of the right half
  have hrefl : ∀ j, r ≤ j → j ≤ N →
      (x j : ℝ) = a + b - (x (2 * r - 1 - j + 1) : ℝ) ∧
        (x (j + 1) : ℝ) = a + b - (x (2 * r - 1 - j) : ℝ) := by
    intro j hj1 hj2
    have hi : 2 * r - 1 - j < r := by omega
    constructor
    · have h := hxR (2 * r - 1 - j + 1) (by omega)
      rwa [show 2 * r - (2 * r - 1 - j + 1) = j by omega] at h
    · have h := hxR (2 * r - 1 - j) (by omega)
      rwa [show 2 * r - (2 * r - 1 - j) = j + 1 by omega] at h
  have hstep : ∀ j ≤ N, (x j : ℝ) < (x (j + 1) : ℝ) := by
    intro j hj
    rcases Nat.lt_or_ge j r with hjr | hjr
    · exact hstepL j hjr
    · obtain ⟨h1, h2⟩ := hrefl j hjr hj
      have h3 := hstepL (2 * r - 1 - j) (by omega)
      rw [h1, h2]
      linarith
  -- the two partitions of the unit interval
  have hμmem : ∀ i : Fin (m + 1), μ i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    exact ⟨by rw [← hμ0]; exact hμmono.monotone (Fin.zero_le i),
      by rw [← hμ1]; exact hμmono.monotone (Fin.le_last i)⟩
  refine ⟨hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxL 0 (by omega), Nat.cast_zero, zero_div, Real.zero_rpow (ne_of_gt hq0)]
    ring
  · have h := hxR 0 (by omega)
    rw [Nat.sub_zero, hxL 0 (by omega), Nat.cast_zero, zero_div,
      Real.zero_rpow (ne_of_gt hq0)] at h
    rw [show N + 1 = 2 * r from hN, h]
    ring
  · intro j hj i
    have hd : (0 : ℝ) ≤ (x (j + 1) : ℝ) - (x j : ℝ) := sub_nonneg.mpr (hstep j hj).le
    rcases Nat.lt_or_ge j r with hjr | hjr
    · rw [hnodeL j hjr i]
      constructor <;> nlinarith [(hμmem i).1, (hμmem i).2]
    · rw [hnodeR j hjr hj i]
      constructor <;> nlinarith [(hμmem i.rev).1, (hμmem i.rev).2]
  · intro j hj i i' hii
    simp only at hii
    have hd : (0 : ℝ) < (x (j + 1) : ℝ) - (x j : ℝ) := sub_pos.mpr (hstep j hj)
    rcases Nat.lt_or_ge j r with hjr | hjr
    · rw [hnodeL j hjr i, hnodeL j hjr i'] at hii
      exact hμmono.injective (mul_right_cancel₀ (ne_of_gt hd) (by linarith))
    · rw [hnodeR j hjr hj i, hnodeR j hjr hj i'] at hii
      have hrev : μ i.rev = μ i'.rev := by
        have := mul_right_cancel₀ (ne_of_gt hd)
          (show (1 - μ i.rev) * ((x (j + 1) : ℝ) - (x j : ℝ))
            = (1 - μ i'.rev) * ((x (j + 1) : ℝ) - (x j : ℝ)) by linarith)
        linarith
      have := hμmono.injective hrev
      exact Fin.rev_injective this
  · intro j hj
    refine Subtype.ext ?_
    rcases Nat.lt_or_ge j r with hjr | hjr
    · rw [hnodeL j hjr 0, hμ0]
      ring
    · rw [hnodeR j hjr hj 0, Fin.rev_zero, hμ1]
      ring
  · intro j hj
    refine Subtype.ext ?_
    rcases Nat.lt_or_ge j r with hjr | hjr
    · rw [hnodeL j hjr (Fin.last m), hμ1]
      ring
    · rw [hnodeR j hjr hj (Fin.last m), Fin.rev_last, hμ0]
      ring

/-- **The interpolation error on one panel from a bound on the `(m+1)`-st derivative there.**  Only
the smoothness of `G` on an open set containing the panel is used. -/
private theorem abs_sub_panel_le {a b : ℝ} {n m : ℕ} {x : ℕ → Set.Icc a b}
    {node : ℕ → Fin (m + 1) → Set.Icc a b} (h : IsPanelNodes n m x node)
    {V : Set ℝ} (hV : IsOpen V) {k : ℕ} (hk : k ≤ n)
    (hVsub : Set.Icc ((x k : ℝ)) ((x (k + 1) : ℝ)) ⊆ V)
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) G V) {f : C(Set.Icc a b, ℝ)}
    (hf : ∀ t : Set.Icc a b, f t = G ((t : ℝ))) {M : ℝ}
    (hM : ∀ s ∈ Set.Ioo ((x k : ℝ)) ((x (k + 1) : ℝ)), |iteratedDeriv (m + 1) G s| ≤ M)
    {t : Set.Icc a b} (h1 : (x k : ℝ) ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ (x (k + 1) : ℝ)) :
    |f t - piecewisePolyInterpCLM n m x node f t|
      ≤ M * ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) / (m + 1).factorial := by
  have hfact0 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn h hV hk hVsub
    hG hf h1 h2
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ξ hξ)
  have hprod : |∏ i, ((t : ℝ) - ((node k i : ℝ)))|
      ≤ ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) := by
    rw [Finset.abs_prod]
    calc ∏ i, |(t : ℝ) - ((node k i : ℝ))|
        ≤ ∏ _i : Fin (m + 1), ((x (k + 1) : ℝ) - (x k : ℝ)) := by
          refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
          have hmi := h.mem k hk i
          rw [abs_sub_le_iff]
          exact ⟨by linarith [hmi.1], by linarith [hmi.2]⟩
      _ = ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hξeq, abs_mul, abs_div, abs_of_pos hfact0]
  calc |iteratedDeriv (m + 1) G ξ| / ((m + 1).factorial : ℝ)
        * |∏ i, ((t : ℝ) - ((node k i : ℝ)))|
      ≤ M / ((m + 1).factorial : ℝ) * ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) := by
        gcongr
        exact hM ξ hξ
    _ = M * ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) / (m + 1).factorial := by ring

/-- **The graded-mesh interpolation error on `[a, b]`, graded towards both endpoints.**  This is
Lemma 12.5.5 in the form Theorem 12.5.6 uses it: the function is Hölder of exponent `γ` on the
whole interval, of class `C^{m+1}` inside, and its `(m+1)`-st derivative grows no faster than
`(x - a)^{γ-(m+1)}` towards `a` and `(b - x)^{γ-(m+1)}` towards `b` — which is what Theorem 12.5.4
gives for the solution of a weakly singular equation.

The two extreme panels are handled by the Hölder bound, the inner panels of the left half by the
derivative bound towards `a` and those of the right half by the one towards `b`, the latter being
the mirror image of the former through `x ↦ a + b - x`.  The constant is explicit, so that the
bound may be applied uniformly over a family of functions with common `H` and `c` — which is what
the row functions `y ↦ l (x, y) u (y)` of a product integration method are. -/
theorem norm_sub_gradedSym_le {a b : ℝ} {m r N : ℕ} {γ q H c Λ : ℝ} (hab : a < b) (hr : 0 < r)
    (hN : N + 1 = 2 * r) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hq : ((m : ℝ) + 1) / γ ≤ q)
    {μ : Fin (m + 1) → ℝ} (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {x : ℕ → Set.Icc a b} {node : ℕ → Fin (m + 1) → Set.Icc a b}
    (hxL : ∀ j ≤ r, (x j : ℝ) = a + ((j : ℝ) / r) ^ q * ((b - a) / 2))
    (hxR : ∀ j ≤ r, (x (2 * r - j) : ℝ) = a + b - (x j : ℝ))
    (hnodeL : ∀ j < r, ∀ i, (node j i : ℝ)
      = (x j : ℝ) + μ i * ((x (j + 1) : ℝ) - (x j : ℝ)))
    (hnodeR : ∀ j, r ≤ j → j ≤ N → ∀ i, (node j i : ℝ)
      = (x j : ℝ) + (1 - μ i.rev) * ((x (j + 1) : ℝ) - (x j : ℝ)))
    (hΛ : IsPanelLebesgueBound N m x node Λ)
    {W : ℝ → ℝ} {w : C(Set.Icc a b, ℝ)} (hw : ∀ t : Set.Icc a b, w t = W ((t : ℝ)))
    (hH : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, |W s - W t| ≤ H * |s - t| ^ γ)
    (hWC : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) W (Set.Ioo a b))
    (hWL : ∀ s ∈ Set.Ioc a ((a + b) / 2),
      |iteratedDeriv (m + 1) W s| ≤ c * (s - a) ^ (γ - ((m : ℝ) + 1)))
    (hWR : ∀ s ∈ Set.Ico ((a + b) / 2) b,
      |iteratedDeriv (m + 1) W s| ≤ c * (b - s) ^ (γ - ((m : ℝ) + 1))) :
    ‖w - piecewisePolyInterpCLM N m x node w‖
      ≤ ((1 + Λ) * H * ((b - a) / 2) ^ γ
          + c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial)
        / (r : ℝ) ^ (m + 1) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hS0 : (0 : ℝ) < (b - a) / 2 := by linarith
  have hSγ0 : (0 : ℝ) ≤ ((b - a) / 2) ^ γ := Real.rpow_nonneg hS0.le γ
  have hq1 : (1 : ℝ) ≤ q := by
    have h2 : (1 : ℝ) < ((m : ℝ) + 1) / γ := by
      rw [lt_div_iff₀ hγ0]
      linarith
    linarith
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hqγ : ((m : ℝ) + 1) ≤ q * γ := by
    rw [div_le_iff₀ hγ0] at hq
    linarith
  have hfact0 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  have hnodes := isPanelNodes_gradedSym hab hr hN hq1 hμ0 hμ1 hμmono hxL hxR hnodeL hnodeR
  have hΛ0 : (0 : ℝ) ≤ Λ := hΛ.nonneg hnodes
  have hH0 : 0 ≤ H := by
    have h := hH a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
    rw [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at h
    have h2 : (0 : ℝ) < (b - a) ^ γ := Real.rpow_pos_of_pos (by linarith) γ
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (W a - W b)]
  have hc0 : 0 ≤ c := by
    have h := hWL ((a + b) / 2) ⟨by linarith, le_rfl⟩
    have h2 : (0 : ℝ) < ((a + b) / 2 - a) ^ (γ - ((m : ℝ) + 1)) :=
      Real.rpow_pos_of_pos (by linarith) _
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (iteratedDeriv (m + 1) W ((a + b) / 2))]
  -- the mesh: monotonicity, the midpoint, and the first panel
  have hmono : ∀ i j, i ≤ j → j ≤ N + 1 → (x i : ℝ) ≤ (x j : ℝ) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ k hk ih => exact fun hk1 => (ih (by omega)).trans (hnodes.step k (by omega)).le
  have hxr : (x r : ℝ) = (a + b) / 2 := by
    rw [hxL r le_rfl, div_self (ne_of_gt hr0), Real.one_rpow]
    ring
  have hx1 : (x 1 : ℝ) = a + (1 / (r : ℝ)) ^ q * ((b - a) / 2) := by
    rw [hxL 1 hr]
    norm_num
  have hx1a : (0 : ℝ) < (x 1 : ℝ) - a := by
    have hpos : (0 : ℝ) < (1 / (r : ℝ)) ^ q := Real.rpow_pos_of_pos (by positivity) q
    rw [hx1]
    nlinarith
  have hxN : (x N : ℝ) = a + b - (x 1 : ℝ) := by
    have h := hxR 1 hr
    rwa [show 2 * r - 1 = N by omega] at h
  have hpanel1 : ((x 1 : ℝ) - a) ^ γ ≤ ((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1) := by
    have hone : (0 : ℝ) < 1 / (r : ℝ) := by positivity
    have hone1 : (1 : ℝ) / (r : ℝ) ≤ 1 := by
      rw [div_le_one hr0]
      exact hr1
    have heq : (x 1 : ℝ) - a = (1 / (r : ℝ)) ^ q * ((b - a) / 2) := by
      rw [hx1]
      ring
    rw [heq, Real.mul_rpow (Real.rpow_nonneg hone.le q) hS0.le, ← Real.rpow_mul hone.le]
    have hle : (1 / (r : ℝ)) ^ (q * γ) ≤ 1 / (r : ℝ) ^ (m + 1) := by
      calc (1 / (r : ℝ)) ^ (q * γ) ≤ (1 / (r : ℝ)) ^ (((m + 1 : ℕ) : ℝ)) := by
            refine Real.rpow_le_rpow_of_exponent_ge hone hone1 ?_
            push_cast
            linarith
        _ = 1 / (r : ℝ) ^ (m + 1) := by rw [Real.rpow_natCast, div_pow, one_pow]
    calc (1 / (r : ℝ)) ^ (q * γ) * ((b - a) / 2) ^ γ
        ≤ (1 / (r : ℝ) ^ (m + 1)) * ((b - a) / 2) ^ γ := by gcongr
      _ = ((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1) := by ring
  -- the graded estimate for an inner panel of the left half
  have hinner : ∀ i, 1 ≤ i → i < r →
      ((x (i + 1) : ℝ) - (x i : ℝ)) ^ (m + 1) * ((x i : ℝ) - a) ^ (γ - ((m : ℝ) + 1))
        ≤ ((b - a) / 2) ^ γ * ((q * 2 ^ (q - 1)) ^ (m + 1) / (r : ℝ) ^ (m + 1)) := by
    intro i hi1 hir
    have hi1' : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hir' : (i : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hir
    have hB0 : (0 : ℝ) < (i : ℝ) / r := by positivity
    have hABeq : ((i : ℝ) + 1) / r - (i : ℝ) / r = 1 / (r : ℝ) := by
      rw [div_sub_div_same]
      norm_num
    have hBA : (i : ℝ) / r < ((i : ℝ) + 1) / r := by
      have hpos : (0 : ℝ) < 1 / (r : ℝ) := by positivity
      linarith
    have hA1 : ((i : ℝ) + 1) / r ≤ 1 := by
      rw [div_le_one hr0]
      exact hir'
    have hA2B : ((i : ℝ) + 1) / r ≤ 2 * ((i : ℝ) / r) := by
      have hdiff : 2 * ((i : ℝ) / r) - ((i : ℝ) + 1) / r = ((i : ℝ) - 1) / r := by
        rw [← mul_div_assoc, div_sub_div_same]
        congr 1
        ring
      have hnn : (0 : ℝ) ≤ ((i : ℝ) - 1) / r := div_nonneg (by linarith) hr0.le
      linarith
    have hgr := graded_panel_le' (m := m) (γ := γ) (q := q) (n := (r : ℝ))
      (A := ((i : ℝ) + 1) / r) (B := (i : ℝ) / r) (S := (b - a) / 2) hq1 hqγ hr0 hS0 hB0 hBA
      hA1 hABeq hA2B
    have he1 : (x i : ℝ) - a = ((b - a) / 2) * ((i : ℝ) / r) ^ q := by
      rw [hxL i (by omega)]
      ring
    have he2 : (x (i + 1) : ℝ) - a = ((b - a) / 2) * (((i : ℝ) + 1) / r) ^ q := by
      rw [hxL (i + 1) (by omega)]
      push_cast
      ring
    have he3 : (x (i + 1) : ℝ) - (x i : ℝ)
        = ((b - a) / 2) * (((i : ℝ) + 1) / r) ^ q - ((b - a) / 2) * ((i : ℝ) / r) ^ q := by
      linarith
    rw [he3, he1]
    exact hgr
  -- the constant
  set Cst : ℝ := (1 + Λ) * H * ((b - a) / 2) ^ γ
    + c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial with hCstdef
  have hCst1 : (0 : ℝ) ≤ (1 + Λ) * H * ((b - a) / 2) ^ γ :=
    mul_nonneg (mul_nonneg (by linarith) hH0) hSγ0
  have hCst2 : (0 : ℝ)
      ≤ c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial :=
    div_nonneg (mul_nonneg (mul_nonneg hc0 hSγ0) (pow_nonneg (by positivity) _)) hfact0.le
  have hCst0 : 0 ≤ Cst := by
    rw [hCstdef]
    linarith
  rw [ContinuousMap.norm_le _ (div_nonneg hCst0 (by positivity))]
  intro t
  obtain ⟨k, hk, h1, h2⟩ := exists_mem_subinterval hnodes.first hnodes.last t
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
  rcases Nat.lt_or_ge k r with hkr | hkr
  · rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- the first panel, where only the Hölder bound is available
      have hx0 : (x 0 : ℝ) = a := hnodes.first
      have hosc : ∀ s : Set.Icc a b, (x 0 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (x (0 + 1) : ℝ) →
          |w s - w (x 0)| ≤ H * ((x 1 : ℝ) - a) ^ γ := by
        intro s hs1 hs2
        rw [hx0] at hs1
        have hs2' : (s : ℝ) ≤ (x 1 : ℝ) := hs2
        rw [hw s, hw (x 0)]
        refine le_trans (hH ((s : ℝ)) s.2 ((x 0 : ℝ)) (x 0).2) ?_
        rw [hx0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (s : ℝ) - a)]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) (by linarith) hγ0.le) hH0
      refine (abs_sub_piecewisePolyInterpCLM_apply_le_of_osc hnodes hΛ w hk h1 h2 hosc).trans ?_
      calc (1 + Λ) * (H * ((x 1 : ℝ) - a) ^ γ)
          ≤ (1 + Λ) * (H * (((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1))) := by gcongr
        _ = (1 + Λ) * H * ((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1) := by ring
        _ ≤ Cst / (r : ℝ) ^ (m + 1) := by
            gcongr
            rw [hCstdef]
            linarith
    · -- an inner panel of the left half
      have hxk1r : (x (k + 1) : ℝ) ≤ (a + b) / 2 := by
        rw [← hxr]
        exact hmono (k + 1) r (by omega) (by omega)
      have hxka : a < (x k : ℝ) := by
        have := hmono 1 k hk1 (by omega)
        linarith
      have hVsub : Set.Icc ((x k : ℝ)) ((x (k + 1) : ℝ)) ⊆ Set.Ioo a b := fun s hs =>
        ⟨lt_of_lt_of_le hxka hs.1, by linarith [hs.2]⟩
      have hM : ∀ s ∈ Set.Ioo ((x k : ℝ)) ((x (k + 1) : ℝ)),
          |iteratedDeriv (m + 1) W s| ≤ c * ((x k : ℝ) - a) ^ (γ - ((m : ℝ) + 1)) := by
        intro s hs
        refine le_trans (hWL s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
          (mul_le_mul_of_nonneg_left ?_ hc0)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hs.1]) (by linarith)
      refine (abs_sub_panel_le hnodes isOpen_Ioo hk hVsub hWC hw hM h1 h2).trans ?_
      calc c * ((x k : ℝ) - a) ^ (γ - ((m : ℝ) + 1))
              * ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) / (m + 1).factorial
          = c / ((m + 1).factorial : ℝ) * (((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1)
              * ((x k : ℝ) - a) ^ (γ - ((m : ℝ) + 1))) := by ring
        _ ≤ c / ((m + 1).factorial : ℝ) * (((b - a) / 2) ^ γ
              * ((q * 2 ^ (q - 1)) ^ (m + 1) / (r : ℝ) ^ (m + 1))) :=
            mul_le_mul_of_nonneg_left (hinner k hk1 hkr) (div_nonneg hc0 hfact0.le)
        _ = c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial
              / (r : ℝ) ^ (m + 1) := by ring
        _ ≤ Cst / (r : ℝ) ^ (m + 1) := by
            gcongr
            rw [hCstdef]
            linarith
  · have hxkr : (a + b) / 2 ≤ (x k : ℝ) := by
      rw [← hxr]
      exact hmono r k hkr (by omega)
    rcases eq_or_lt_of_le hk with rfl | hkN
    · -- the last panel, where only the Hölder bound is available
      have hxN1 : (x (k + 1) : ℝ) = b := hnodes.last
      have hosc : ∀ s : Set.Icc a b, (x k : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (x (k + 1) : ℝ) →
          |w s - w (x k)| ≤ H * ((x 1 : ℝ) - a) ^ γ := by
        intro s hs1 hs2
        rw [hw s, hw (x k)]
        refine le_trans (hH ((s : ℝ)) s.2 ((x k : ℝ)) (x k).2) ?_
        rw [abs_of_nonneg (by linarith)]
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) ?_ hγ0.le) hH0
        rw [hxN1] at hs2
        rw [hxN]
        linarith
      refine (abs_sub_piecewisePolyInterpCLM_apply_le_of_osc hnodes hΛ w hk h1 h2 hosc).trans ?_
      calc (1 + Λ) * (H * ((x 1 : ℝ) - a) ^ γ)
          ≤ (1 + Λ) * (H * (((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1))) := by gcongr
        _ = (1 + Λ) * H * ((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1) := by ring
        _ ≤ Cst / (r : ℝ) ^ (m + 1) := by
            gcongr
            rw [hCstdef]
            linarith
    · -- an inner panel of the right half, the mirror image of one of the left half
      have hi1 : 1 ≤ 2 * r - 1 - k := by omega
      have hir : 2 * r - 1 - k < r := by omega
      have hxk : (x k : ℝ) = a + b - (x (2 * r - 1 - k + 1) : ℝ) := by
        have h := hxR (2 * r - 1 - k + 1) (by omega)
        rwa [show 2 * r - (2 * r - 1 - k + 1) = k by omega] at h
      have hxk1 : (x (k + 1) : ℝ) = a + b - (x (2 * r - 1 - k) : ℝ) := by
        have h := hxR (2 * r - 1 - k) (by omega)
        rwa [show 2 * r - (2 * r - 1 - k) = k + 1 by omega] at h
      have hia : (0 : ℝ) < (x (2 * r - 1 - k) : ℝ) - a := by
        have := hmono 1 (2 * r - 1 - k) hi1 (by omega)
        linarith
      have hxk1b : (x (k + 1) : ℝ) < b := by
        rw [hxk1]
        linarith
      have hVsub : Set.Icc ((x k : ℝ)) ((x (k + 1) : ℝ)) ⊆ Set.Ioo a b := fun s hs =>
        ⟨by linarith [hs.1], lt_of_le_of_lt hs.2 hxk1b⟩
      have hM : ∀ s ∈ Set.Ioo ((x k : ℝ)) ((x (k + 1) : ℝ)),
          |iteratedDeriv (m + 1) W s|
            ≤ c * ((x (2 * r - 1 - k) : ℝ) - a) ^ (γ - ((m : ℝ) + 1)) := by
        intro s hs
        refine le_trans (hWR s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
          (mul_le_mul_of_nonneg_left ?_ hc0)
        refine Real.rpow_le_rpow_of_nonpos hia ?_ (by linarith)
        have := hs.2
        rw [hxk1] at this
        linarith
      have hlen : (x (k + 1) : ℝ) - (x k : ℝ)
          = (x (2 * r - 1 - k + 1) : ℝ) - (x (2 * r - 1 - k) : ℝ) := by
        rw [hxk, hxk1]
        ring
      refine (abs_sub_panel_le hnodes isOpen_Ioo hk hVsub hWC hw hM h1 h2).trans ?_
      rw [hlen]
      calc c * ((x (2 * r - 1 - k) : ℝ) - a) ^ (γ - ((m : ℝ) + 1))
              * ((x (2 * r - 1 - k + 1) : ℝ) - (x (2 * r - 1 - k) : ℝ)) ^ (m + 1)
              / (m + 1).factorial
          = c / ((m + 1).factorial : ℝ)
              * (((x (2 * r - 1 - k + 1) : ℝ) - (x (2 * r - 1 - k) : ℝ)) ^ (m + 1)
              * ((x (2 * r - 1 - k) : ℝ) - a) ^ (γ - ((m : ℝ) + 1))) := by ring
        _ ≤ c / ((m + 1).factorial : ℝ) * (((b - a) / 2) ^ γ
              * ((q * 2 ^ (q - 1)) ^ (m + 1) / (r : ℝ) ^ (m + 1))) :=
            mul_le_mul_of_nonneg_left (hinner (2 * r - 1 - k) hi1 hir)
              (div_nonneg hc0 hfact0.le)
        _ = c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial
              / (r : ℝ) ^ (m + 1) := by ring
        _ ≤ Cst / (r : ℝ) ^ (m + 1) := by
            gcongr
            rw [hCstdef]
            linarith


end SymmetricGradedMesh


/-! ### Theorem 12.5.6 -/

section Theorem6

open IntegralOperator MeasureTheory

/-- A panel length bound that also covers the panel touching the singularity, where the mean value
theorem is not available: for `0 ≤ B < A ≤ 1` and `q ≥ 1`, `A^q - B^q ≤ q (A - B)`. -/
private theorem rpow_sub_rpow_le' {A B q : ℝ} (hq : 1 ≤ q) (hB : 0 ≤ B) (hBA : B < A)
    (hA1 : A ≤ 1) : A ^ q - B ^ q ≤ q * (A - B) := by
  have hA0 : 0 < A := lt_of_le_of_lt hB hBA
  rcases eq_or_lt_of_le hB with hB0 | hB0
  · have hzero : B ^ q = 0 := by rw [← hB0, Real.zero_rpow (by linarith)]
    have h1 : A ^ q ≤ A := by
      calc A ^ q ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hA0 hA1 hq
        _ = A := Real.rpow_one A
    rw [hzero, ← hB0]
    nlinarith
  · have h1 := rpow_sub_rpow_le hq hB0 hBA
    have h2 : A ^ (q - 1) ≤ 1 := Real.rpow_le_one hA0.le hA1 (by linarith)
    have h3 : 0 ≤ q * (A - B) * (1 - A ^ (q - 1)) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith [h1, h3]

/-- **Theorem 12.5.6**, the convergence of graded-mesh product integration for a weakly singular
equation.  Let `g` be an admissible (weakly singular) factor, `l` continuous, `λ ≠ 0` with
`λ - K` invertible, and let `K_n` be the product rule (12.5.38) obtained by replacing
`l (x, ·) u (·)` by its piecewise polynomial interpolant of degree `m` on the mesh of the
paragraph preceding the theorem — graded towards both endpoints with exponent `q ≥ (m + 1)/γ`,
`n = 2 (p + 1)` panels.  Assume, as Theorem 12.5.4 gives, that every row function
`y ↦ l (x, y) u (y)` of the exact solution is of Rice's type `(γ, m + 1)` at both endpoints, with
constants independent of `x`.  Then for all large `n` the approximating equations are uniquely
solvable and

`‖u - u_n‖_∞ ≤ c n^{-(m+1)}`   (12.5.41).

The proof is the book's: `theorem_12_5_1` gives `‖u - u_n‖ ≤ c ‖K u - K_n u‖`, the consistency
error is the interpolation error of the row functions integrated against `g`, and
`norm_sub_gradedSym_le` — Lemma 12.5.5 on the two-sided mesh — bounds that by `c n^{-(m+1)}`
uniformly in the row. -/
theorem theorem_12_5_6 {a b : ℝ} (hab : a < b) {m : ℕ} {γ q : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hq : ((m : ℝ) + 1) / γ ≤ q)
    {ν : Fin (m + 1) → ℝ} (hν0 : ν 0 = 0) (hν1 : ν (Fin.last m) = 1) (hνmono : StrictMono ν)
    {x : ℕ → ℕ → Set.Icc a b} {node : ℕ → ℕ → Fin (m + 1) → Set.Icc a b}
    (hxL : ∀ p, ∀ j ≤ p + 1,
      (x p j : ℝ) = a + ((j : ℝ) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2))
    (hxR : ∀ p, ∀ j ≤ p + 1, (x p (2 * (p + 1) - j) : ℝ) = a + b - (x p j : ℝ))
    (hnodeL : ∀ p, ∀ j < p + 1, ∀ i, (node p j i : ℝ)
      = (x p j : ℝ) + ν i * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
    (hnodeR : ∀ p, ∀ j, p + 1 ≤ j → j ≤ 2 * p + 1 → ∀ i, (node p j i : ℝ)
      = (x p j : ℝ) + (1 - ν i.rev) * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
    {g : Set.Icc a b × Set.Icc a b → ℝ} (hg : IsAdmissibleKernel (iccMeasure a b) g)
    (l : C(Set.Icc a b × Set.Icc a b, ℝ)) {lam : ℝ} (hlam : lam ≠ 0)
    {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = lam • 1 - admissibleKernelCLM (hg.mul_continuousMap l))
    {f u : C(Set.Icc a b, ℝ)}
    (hu : (lam • 1 - admissibleKernelCLM (hg.mul_continuousMap l) :
      C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f)
    {W : Set.Icc a b → ℝ → ℝ} {H cR : ℝ}
    (hW : ∀ z : Set.Icc a b, ∀ t : Set.Icc a b, prodFactor l z u t = W z ((t : ℝ)))
    (hWH : ∀ z : Set.Icc a b, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      |W z s - W z t| ≤ H * |s - t| ^ γ)
    (hWC : ∀ z : Set.Icc a b, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (W z) (Set.Ioo a b))
    (hWL : ∀ z : Set.Icc a b, ∀ s ∈ Set.Ioc a ((a + b) / 2),
      |iteratedDeriv (m + 1) (W z) s| ≤ cR * (s - a) ^ (γ - ((m : ℝ) + 1)))
    (hWR : ∀ z : Set.Icc a b, ∀ s ∈ Set.Ico ((a + b) / 2) b,
      |iteratedDeriv (m + 1) (W z) s| ≤ cR * (b - s) ^ (γ - ((m : ℝ) + 1))) :
    ∃ C : ℝ, ∀ᶠ p in atTop,
      (∀ h : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
        (lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = h) ∧
      ∀ un : C(Set.Icc a b, ℝ),
        (lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f →
        ‖u - un‖ ≤ C / (2 * ((p : ℝ) + 1)) ^ (m + 1) := by
  classical
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hq1 : (1 : ℝ) ≤ q := by
    have h2 : (1 : ℝ) < ((m : ℝ) + 1) / γ := by
      rw [lt_div_iff₀ hγ0]
      linarith
    linarith
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hS0 : (0 : ℝ) < (b - a) / 2 := by linarith
  have hfact0 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  have hc0 : (0 : ℝ) ≤ rowBound (iccMeasure a b) g := hg.rowBound_nonneg
  -- the separation of the reference nodes and the uniform Lebesgue bound
  obtain ⟨dν, hdν0, hdν⟩ :
      ∃ d : ℝ, 0 < d ∧ ∀ i i' : Fin (m + 1), i ≠ i' → d ≤ |ν i - ν i'| := by
    by_cases hS : (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) => p.1 ≠ p.2).Nonempty
    · refine ⟨(Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) => p.1 ≠ p.2).inf' hS
        (fun p => |ν p.1 - ν p.2|), ?_, fun i i' hii => ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro p hp
        exact abs_pos.mpr (sub_ne_zero.mpr fun hcon =>
          (Finset.mem_filter.mp hp).2 (hνmono.injective hcon))
      · exact Finset.inf'_le (fun p : Fin (m + 1) × Fin (m + 1) => |ν p.1 - ν p.2|)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, i'), hii⟩)
    · exact ⟨1, one_pos, fun i i' hii =>
        absurd ⟨(i, i'), Finset.mem_filter.mpr ⟨Finset.mem_univ (i, i'), hii⟩⟩ hS⟩
  set Λ : ℝ := ((m : ℝ) + 1) * (1 / dν) ^ m with hΛdef
  have hnodes : ∀ p : ℕ, IsPanelNodes (2 * p + 1) m (x p) (node p) := fun p =>
    isPanelNodes_gradedSym hab (Nat.succ_pos p) (by omega) hq1 hν0 hν1 hνmono (hxL p) (hxR p)
      (hnodeL p) (hnodeR p)
  have hΛb : ∀ p : ℕ, IsPanelLebesgueBound (2 * p + 1) m (x p) (node p) Λ := by
    intro p
    refine isPanelLebesgueBound_of_sep (hnodes p)
      (d := fun j => dν * ((x p (j + 1) : ℝ) - (x p j : ℝ))) (ρ := 1 / dν)
      (fun j hj => mul_pos hdν0 (sub_pos.mpr ((hnodes p).step j hj))) (fun j hj => ?_)
      (fun j hj i i' hii => ?_)
    · rw [← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hdν0), one_mul]
    · have hd : (0 : ℝ) < (x p (j + 1) : ℝ) - (x p j : ℝ) := sub_pos.mpr ((hnodes p).step j hj)
      rcases Nat.lt_or_ge j (p + 1) with hjr | hjr
      · rw [hnodeL p j hjr i, hnodeL p j hjr i']
        have hrw : ((x p j : ℝ) + ν i * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
            - ((x p j : ℝ) + ν i' * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
            = (ν i - ν i') * ((x p (j + 1) : ℝ) - (x p j : ℝ)) := by ring
        rw [hrw, abs_mul, abs_of_pos hd]
        exact mul_le_mul_of_nonneg_right (hdν i i' hii) hd.le
      · rw [hnodeR p j hjr hj i, hnodeR p j hjr hj i']
        have hrw : ((x p j : ℝ) + (1 - ν i.rev) * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
            - ((x p j : ℝ) + (1 - ν i'.rev) * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
            = (ν i'.rev - ν i.rev) * ((x p (j + 1) : ℝ) - (x p j : ℝ)) := by ring
        rw [hrw, abs_mul, abs_of_pos hd]
        refine mul_le_mul_of_nonneg_right (hdν i'.rev i.rev ?_) hd.le
        exact fun hcon => hii (Fin.rev_injective hcon).symm
  -- the mesh tends to zero, so the projections converge pointwise
  have hmesh : ∀ p : ℕ, ∀ j ≤ 2 * p + 1,
      (x p (j + 1) : ℝ) - (x p j : ℝ) ≤ (b - a) / 2 * q / ((p : ℝ) + 1) := by
    have hleft : ∀ p : ℕ, ∀ i < p + 1,
        (x p (i + 1) : ℝ) - (x p i : ℝ) ≤ (b - a) / 2 * q / ((p : ℝ) + 1) := by
      intro p i hi
      have hr0 : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
      have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
      have hB0 : (0 : ℝ) ≤ (i : ℝ) / ((p + 1 : ℕ) : ℝ) := by positivity
      have hABeq : ((i : ℝ) + 1) / ((p + 1 : ℕ) : ℝ) - (i : ℝ) / ((p + 1 : ℕ) : ℝ)
          = 1 / ((p + 1 : ℕ) : ℝ) := by
        rw [div_sub_div_same]
        norm_num
      have hBA : (i : ℝ) / ((p + 1 : ℕ) : ℝ) < ((i : ℝ) + 1) / ((p + 1 : ℕ) : ℝ) := by
        have hpos : (0 : ℝ) < 1 / ((p + 1 : ℕ) : ℝ) := by positivity
        linarith
      have hA1 : ((i : ℝ) + 1) / ((p + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one hr0, hcast]
        have : (i : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : i ≤ p)
        linarith
      have hstep := rpow_sub_rpow_le' hq1 hB0 hBA hA1
      rw [hABeq] at hstep
      have he1 : (x p i : ℝ) = a + ((i : ℝ) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2) :=
        hxL p i (by omega)
      have he2 : (x p (i + 1) : ℝ)
          = a + (((i : ℝ) + 1) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2) := by
        rw [hxL p (i + 1) (by omega)]
        push_cast
        ring
      rw [he1, he2, ← hcast]
      have hkey : (((i : ℝ) + 1) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2)
          - ((i : ℝ) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2)
          ≤ q * (1 / ((p + 1 : ℕ) : ℝ)) * ((b - a) / 2) := by
        nlinarith [hstep, hS0]
      calc a + (((i : ℝ) + 1) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2)
            - (a + ((i : ℝ) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2))
          = (((i : ℝ) + 1) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2)
            - ((i : ℝ) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2) := by ring
        _ ≤ q * (1 / ((p + 1 : ℕ) : ℝ)) * ((b - a) / 2) := hkey
        _ = (b - a) / 2 * q / ((p + 1 : ℕ) : ℝ) := by ring
    intro p j hj
    rcases Nat.lt_or_ge j (p + 1) with hjr | hjr
    · exact hleft p j hjr
    · have hi : 2 * (p + 1) - 1 - j < p + 1 := by omega
      have hxj : (x p j : ℝ) = a + b - (x p (2 * (p + 1) - 1 - j + 1) : ℝ) := by
        have h := hxR p (2 * (p + 1) - 1 - j + 1) (by omega)
        rwa [show 2 * (p + 1) - (2 * (p + 1) - 1 - j + 1) = j by omega] at h
      have hxj1 : (x p (j + 1) : ℝ) = a + b - (x p (2 * (p + 1) - 1 - j) : ℝ) := by
        have h := hxR p (2 * (p + 1) - 1 - j) (by omega)
        rwa [show 2 * (p + 1) - (2 * (p + 1) - 1 - j) = j + 1 by omega] at h
      have := hleft p (2 * (p + 1) - 1 - j) hi
      rw [hxj, hxj1]
      linarith
  have htend : Tendsto (fun p : ℕ => (b - a) / 2 * q / ((p : ℝ) + 1)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hPconv : ∀ v : C(Set.Icc a b, ℝ),
      Tendsto (fun p => piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p) v) atTop (𝓝 v) :=
    fun v => tendsto_piecewisePolyInterpCLM (N := fun p => 2 * p + 1) hnodes hΛb hmesh htend v
  have hnormP : ∀ p : ℕ, ‖piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)‖ ≤ Λ := fun p =>
    norm_piecewisePolyInterpCLM_le (hnodes p) (hΛb p)
  -- Theorem 12.5.1
  obtain ⟨c₀, hc₀⟩ := theorem_12_5_1 hg l hnormP hPconv hlam he
  set Cst : ℝ := (1 + Λ) * H * ((b - a) / 2) ^ γ
    + cR * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial with hCstdef
  have hΛ0 : (0 : ℝ) ≤ Λ := by
    rw [hΛdef]
    exact mul_nonneg (by positivity) (pow_nonneg (div_nonneg zero_le_one hdν0.le) m)
  have hSγ0 : (0 : ℝ) ≤ ((b - a) / 2) ^ γ := Real.rpow_nonneg hS0.le γ
  have hH0 : 0 ≤ H := by
    have h := hWH (x 0 0) a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
    rw [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at h
    have h2 : (0 : ℝ) < (b - a) ^ γ := Real.rpow_pos_of_pos (by linarith) γ
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (W (x 0 0) a - W (x 0 0) b)]
  have hcR0 : 0 ≤ cR := by
    have h := hWL (x 0 0) ((a + b) / 2) ⟨by linarith, le_rfl⟩
    have h2 : (0 : ℝ) < ((a + b) / 2 - a) ^ (γ - ((m : ℝ) + 1)) :=
      Real.rpow_pos_of_pos (by linarith) _
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (iteratedDeriv (m + 1) (W (x 0 0)) ((a + b) / 2))]
  have hCst0 : 0 ≤ Cst := by
    rw [hCstdef]
    have h1 : (0 : ℝ) ≤ (1 + Λ) * H * ((b - a) / 2) ^ γ :=
      mul_nonneg (mul_nonneg (by linarith) hH0) hSγ0
    have h2 : (0 : ℝ)
        ≤ cR * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial :=
      div_nonneg (mul_nonneg (mul_nonneg hcR0 hSγ0) (pow_nonneg (by positivity) _)) hfact0.le
    linarith
  refine ⟨c₀ * rowBound (iccMeasure a b) g * Cst * 2 ^ (m + 1), ?_⟩
  filter_upwards [hc₀] with p hp
  obtain ⟨en, hencoe, hennorm, herr⟩ := hp
  have hsolve : ∀ h : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
      (lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
        C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = h := by
    intro h
    have hiff : ∀ z : C(Set.Icc a b, ℝ), (en z = h)
        ↔ ((lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
            C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) z = h) := by
      intro z
      rw [← hencoe, ContinuousLinearEquiv.coe_coe]
    have huniq : ∃! z : C(Set.Icc a b, ℝ), en z = h :=
      ⟨en.symm h, en.apply_symm_apply h, fun z hz => by rw [← hz, en.symm_apply_apply]⟩
    simpa only [hiff] using huniq
  refine ⟨hsolve, fun un hun => ?_⟩
  -- the consistency error is the interpolation error of the rows, uniformly in the row
  have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
  have hcons : ‖admissibleKernelCLM (hg.mul_continuousMap l) u
        - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) u‖
      ≤ rowBound (iccMeasure a b) g * (Cst / ((p : ℝ) + 1) ^ (m + 1)) := by
    have hpos : (0 : ℝ) < ((p : ℝ) + 1) ^ (m + 1) := by positivity
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro z
    have hdiff : (admissibleKernelCLM (hg.mul_continuousMap l) u
        - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) u) z
        = ∫ y, g (z, y) * (prodFactor l z u
            - piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p) (prodFactor l z u)) y
          ∂iccMeasure a b := by
      rw [ContinuousMap.sub_apply, ← productCLM_one hg l, productCLM_apply, productCLM_apply,
        ← integral_sub (hg.integrable_mul _ z) (hg.integrable_mul _ z)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [ContinuousMap.sub_apply, one_apply_eq_self]
      ring
    rw [hdiff, Real.norm_eq_abs]
    refine (hg.abs_integral_mul_le _ z).trans ?_
    have hint := norm_sub_gradedSym_le (r := p + 1) hab (Nat.succ_pos p) (by omega) hγ0 hγ1 hq
      hν0 hν1 hνmono (hxL p) (hxR p) (hnodeL p) (hnodeR p) (hΛb p) (hW z) (hWH z) (hWC z)
      (hWL z) (hWR z)
    rw [hcast] at hint
    exact mul_le_mul (hg.le_rowBound z) hint (norm_nonneg _) hc0
  -- assemble
  have hfinal := herr f u un hu hun
  have hpos : (0 : ℝ) < ((p : ℝ) + 1) ^ (m + 1) := by positivity
  have hc₀0 : (0 : ℝ) ≤ c₀ := le_trans (norm_nonneg _) hennorm
  calc ‖u - un‖
      ≤ c₀ * ‖admissibleKernelCLM (hg.mul_continuousMap l) u
          - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) u‖ := hfinal
    _ ≤ c₀ * (rowBound (iccMeasure a b) g * (Cst / ((p : ℝ) + 1) ^ (m + 1))) :=
        mul_le_mul_of_nonneg_left hcons hc₀0
    _ = c₀ * rowBound (iccMeasure a b) g * Cst * 2 ^ (m + 1)
          / (2 * ((p : ℝ) + 1)) ^ (m + 1) := by
        rw [mul_pow]
        field_simp

end Theorem6


end AtkinsonHan.Chapter12
