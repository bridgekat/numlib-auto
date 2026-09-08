import Numlib.Analysis.Normed.Operator.CollectivelyCompact
import Numlib.IntegralEquations.WeaklySingular

/-!
# Product integration for a weakly singular kernel

A kernel that splits as `k (x, y) = l (x, y) g (x, y)`, with `l` continuous and `g` merely
*admissible* in the sense of `Numlib/IntegralEquations/WeaklySingular` — integrable in `y`,
uniformly in the mean, and with bounded rows — is integrated by a **product rule**: the smooth
factor of the integrand, `y ↦ l (x, y) u (y)`, is replaced by an approximation and the singular
factor is integrated exactly,

`Kₙ u (x) = ∫ P (l (x, ·) u (·)) (y) * g (x, y) dy`.

`IntegralOperator.productCLM` is that operator, for an arbitrary bounded `P` on `C(X, ℝ)`; taking
for `P` a piecewise polynomial interpolation operator gives the classical product trapezoidal and
product Simpson rules.  It is *not* a Nyström operator: the weights `∫ g (x, y) φⱼ (y) dy` depend on
the evaluation point `x`, which is exactly what makes the singular factor harmless.

The content of the module is that the family `{Kₙ}` obtained from a sequence of `P` of uniformly
bounded norm converging pointwise to the identity is **collectively compact and pointwise
convergent** to the operator of the kernel `l g`, so that the perturbation theory of
`Numlib/IntegralEquations/SecondKind` applies to `μ - Kₙ` verbatim.

## Main definitions

* `IntegralOperator.prodFactor l x u` — the row function `y ↦ l (x, y) u (y)` that the rule
  approximates, with `IntegralOperator.continuous_prodFactor` its continuity in the base point `x`,
  which is what makes the set of row functions compact in `C(X, ℝ)`.
* `IntegralOperator.productCLM hg l P` — the product integration operator, with
  `IntegralOperator.productCLM_apply` its defining formula.

## Main statements

* `IntegralOperator.norm_productCLM_le` — the bound `‖Kₙ‖ ≤ c_g ‖P‖ ‖l‖`, where `c_g` is the row
  bound `IntegralOperator.rowBound` of the singular factor.
* `IntegralOperator.productCLM_one` — with no approximation the rule is the operator of the kernel
  `l g` itself, which is admissible by `IntegralOperator.IsAdmissibleKernel.mul_continuousMap`.
* `IntegralOperator.tendsto_productCLM` — the family converges pointwise to that operator.  The
  estimate `|Kₙ u (x) - K u (x)| ≤ c_g ‖P (l (x, ·) u (·)) - l (x, ·) u (·)‖` is uniform in `x`
  because the row functions form a *compact* subset of `C(X, ℝ)`, on which a pointwise convergent
  sequence of operators converges uniformly
  (`tendstoUniformlyOn_of_tendsto_of_isCompact`).
* `IntegralOperator.isCollectivelyCompact_productCLM` — the family is collectively compact.
  Uniform boundedness is `IntegralOperator.norm_productCLM_le` and equicontinuity is
  `IntegralOperator.exists_delta_product`, so Arzelà–Ascoli in the form
  `ContinuousMap.isCompact_closure_of_forall_norm_le` applies.

## References

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
3rd edition, Springer, 2009 ([han2009theoretical]), §12.5, equations (12.5.14)–(12.5.17); the
convergence theorem there is Theorem 12.5.1 and the pointwise convergence is its Exercise 12.5.1.
-/

open Filter Topology

namespace IntegralOperator

open MeasureTheory Metric Set

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-! ### The row functions of a product rule -/


/-- **The factor of the integrand that a product rule interpolates**: the continuous function
`y ↦ l (x, y) u (y)`.  The product rule replaces it by its interpolant and integrates the result
against the singular factor `g (x, ·)`. -/
noncomputable def prodFactor (l : C(X × X, ℝ)) (x : X) (u : C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun y => l (x, y) * u y, (l.continuous.comp (by fun_prop)).mul u.continuous⟩

omit [CompactSpace X] in
/-- The defining formula of `IntegralOperator.prodFactor`. -/
@[simp]
theorem prodFactor_apply (l : C(X × X, ℝ)) (x : X) (u : C(X, ℝ)) (y : X) :
    prodFactor l x u y = l (x, y) * u y := rfl

omit [CompactSpace X] in
/-- The row function of a product rule is additive in the function it multiplies, which is half of
the linearity of `IntegralOperator.productCLM`. -/
theorem prodFactor_add (l : C(X × X, ℝ)) (x : X) (u v : C(X, ℝ)) :
    prodFactor l x (u + v) = prodFactor l x u + prodFactor l x v := by
  ext y
  simp only [prodFactor_apply, ContinuousMap.add_apply]
  ring

omit [CompactSpace X] in
/-- The row function of a product rule is homogeneous in the function it multiplies, which is the
other half of the linearity of `IntegralOperator.productCLM`. -/
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

/-! ### The product integration operator -/

section Kernel

variable [MeasurableSpace X] [BorelSpace X] {ν : Measure X} {g : X × X → ℝ}

/-- **The oscillation estimate for a product rule**: the difference of two values of `K_n u`
splits into the contribution of the oscillation of the smooth factor `l` and that of the singular
factor `g`.  It is the estimate behind the equicontinuity half of
[han2009theoretical], §12.5, Theorem 12.5.1. -/
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

/-- **The product integration operator** `K_n u (x) = ∫ P (l (x, ·) u (·)) (y) * g (x, y) dy`,
with an arbitrary bounded `P` on `C(X, ℝ)` in place of the interpolation of a concrete rule.  This
is equation (12.5.14) of [han2009theoretical], §12.5.

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

/-- `‖K_n‖ ≤ c_g ‖P‖ ‖l‖`: the product operators of a family of uniformly bounded `P` are
uniformly bounded.  This is the bound of the proof of [han2009theoretical], §12.5,
Theorem 12.5.1. -/
theorem norm_productCLM_le (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) :
    ‖productCLM hg l P‖ ≤ rowBound ν g * (‖P‖ * ‖l‖) := by
  refine LinearMap.mkContinuous_norm_le _ ?_ _
  have := hg.rowBound_nonneg (μ := ν) (k := g)
  positivity

/-- **The exact operator is the product operator of the identity**: with no approximation the
product rule is the integral operator of the kernel `l g` itself, which by the splitting rule
`IntegralOperator.IsAdmissibleKernel.mul_continuousMap` is admissible. -/
theorem productCLM_one (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ)) :
    productCLM hg l 1 = admissibleKernelCLM (hg.mul_continuousMap l) := by
  ext u x
  rw [productCLM_apply, admissibleKernelCLM_apply]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [one_apply_eq_self, prodFactor_apply]
  ring

/-- **The product operators converge pointwise to the exact operator** whenever the approximations
`P n` do.  The estimate `|K_n u (x) - K u (x)| ≤ c_g ‖P_n w_x - w_x‖` is uniform in `x` because
`{w_x = l (x, ·) u (·) : x ∈ X}` is a *compact* subset of `C(X, ℝ)`, on which a pointwise
convergent sequence of bounded operators converges uniformly
(`tendstoUniformlyOn_of_tendsto_of_isCompact`).

This is assumption A2 of the collectively compact framework; [han2009theoretical], §12.5,
Exercise 12.5.1. -/
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
    tendstoUniformlyOn_of_tendsto_of_isCompact (fun v => by simpa using hP v) hS
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

/-- **The product integration operators of a uniformly bounded family of approximations are
collectively compact.**

Uniform boundedness of the images of the unit ball is `norm_productCLM_le` and their
equicontinuity is `exists_delta_product`, so Arzelà–Ascoli in the form
`ContinuousMap.isCompact_closure_of_forall_norm_le` applies.  Together with the pointwise
convergence `tendsto_productCLM` this is assumption A3 of the collectively compact framework, and
the two are what the proof of [han2009theoretical], §12.5, Theorem 12.5.1 verifies. -/
theorem isCollectivelyCompact_productCLM (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    {P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)} {Cp : ℝ} (hCp : ∀ n, ‖P n‖ ≤ Cp) :
    IsCollectivelyCompact (fun n => productCLM hg l (P n)) := by
  have hc0 : (0 : ℝ) ≤ rowBound ν g := hg.rowBound_nonneg
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (norm_nonneg _) (hCp 0)
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos, ?_⟩
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

end IntegralOperator
