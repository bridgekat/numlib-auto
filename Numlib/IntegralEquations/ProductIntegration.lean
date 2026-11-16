/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Operator.CollectivelyCompact
import Numlib.IntegralEquations.WeaklySingular

/-!
# Product integration for a weakly singular kernel

Let $X$ be a compact metric space with a Borel measure $\nu$. Consider a kernel of the form
$k(x, y) = l(x, y) \, g(x, y)$, where $l$ is continuous and $g$ is admissible in the sense of
`IntegralOperator.IsAdmissibleKernel`: the rows of $g$ are integrable, close in $L^1$ for nearby
points, and bounded in $L^1$. A **product integration rule** replaces the smooth factor
$w_x = l(x, \cdot) \, u(\cdot)$ of the integrand by an approximation $P w_x$ and integrates the
singular factor exactly:
$$(K_n u)(x) = \int g(x, y) \, (P w_x)(y) \, d\nu(y).$$
Here $P$ is any bounded linear operator on $C(X)$. For $P$ a piecewise polynomial interpolation
operator, this gives the product trapezoidal rule and the product Simpson rule. The operator $K_n$
is not a Nyström operator: its weights $\int g(x, y) \varphi_j(y) \, d\nu(y)$ depend on the point
$x$, and for this reason the singular factor does no harm. The presentation follows
[han2009theoretical], §12.5, equations (12.5.14)–(12.5.17).

Let $(P_n)$ be a sequence of operators with uniformly bounded norms that converges pointwise to the
identity. Then the family of product integration operators of the $P_n$ is collectively compact and
converges pointwise to the integral operator $K$ of the kernel $l g$. So the perturbation theory of
`Numlib.IntegralEquations.SecondKind` applies to $\mu - K_n$ without change. This is the content of
Theorem 12.5.1 and Exercise 12.5.1 of [han2009theoretical].

## Main definitions

* `IntegralOperator.prodFactor`: the function $w_x = l(x, \cdot) \, u(\cdot)$ that a product rule
  approximates.
* `IntegralOperator.productCLM`: the product integration operator $K_n$ of an admissible $g$, a
  continuous $l$ and a bounded operator $P$.

## Main results

* `IntegralOperator.continuous_prodFactor`: $x \mapsto w_x$ is continuous into $C(X)$, so the set of
  the $w_x$ is compact.
* `IntegralOperator.norm_productCLM_le`: $\|K_n\| \le c_g \|P\| \|l\|$, where
  $c_g = \sup_x \int |g(x, y)| \, d\nu(y)$ is `IntegralOperator.rowBound`.
* `IntegralOperator.productCLM_one`: for $P = 1$, the product integration operator is the integral
  operator $K$ of the admissible kernel $l g$.
* `IntegralOperator.admissibleKernelCLM_sub_productCLM_apply` and
  `IntegralOperator.norm_admissibleKernelCLM_sub_productCLM_le`: $(Ku - K_n u)(x) = \int g(x, y)
  (w_x - P w_x)(y) \, d\nu(y)$, so $\|Ku - K_n u\|_\infty \le c_g \sup_x \|w_x - P w_x\|$.
* `IntegralOperator.tendsto_productCLM`: if $P_n v \to v$ for every $v$, then $K_n u \to K u$ for
  every $u$.
* `IntegralOperator.isCollectivelyCompact_productCLM`: for uniformly bounded $P_n$, the family
  $(K_n)$ is collectively compact.

## Proof outline

The consistency error $Ku - K_n u$ is the approximation error $w_x - P w_x$ integrated against
$g(x, \cdot)$. So a concrete rule needs an interpolation error bound for the functions $w_x$ that is
uniform in $x$. For the pointwise convergence, the bound $|(K_n u)(x) - (Ku)(x)| \le c_g \|P_n w_x -
w_x\|$ is uniform in $x$, because the set $\{w_x : x \in X\}$ is compact in $C(X)$ and a pointwise
convergent sequence of bounded operators converges uniformly on a compact set
(`tendstoUniformlyOn_of_tendsto_of_isCompact`). For the collective compactness, the uniform bound is
`IntegralOperator.norm_productCLM_le`, the equicontinuity is
`IntegralOperator.exists_delta_product`, and the Arzelà–Ascoli theorem in the form
`ContinuousMap.isCompact_closure_of_forall_norm_le` applies.
-/

open Filter Topology

namespace IntegralOperator

open MeasureTheory Metric Set

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-! ### The functions that a product rule approximates -/


/-- Let $l$ be a continuous kernel on $X \times X$, let $x \in X$ and let $u \in C(X)$. The function
that a product rule approximates is
$$w_x(y) = l(x, y) \, u(y),$$
as an element of $C(X)$. The product rule replaces $w_x$ by an approximation $P w_x$ and
integrates the result against the singular factor $g(x, \cdot)$. -/
noncomputable def prodFactor (l : C(X × X, ℝ)) (x : X) (u : C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun y => l (x, y) * u y, (l.continuous.comp (by fun_prop)).mul u.continuous⟩

omit [CompactSpace X] in
/-- The function `IntegralOperator.prodFactor l x u` maps $y$ to $l(x, y) u(y)$. -/
@[simp]
theorem prodFactor_apply (l : C(X × X, ℝ)) (x : X) (u : C(X, ℝ)) (y : X) :
    prodFactor l x u y = l (x, y) * u y := rfl

omit [CompactSpace X] in
/-- The function $w_x = l(x, \cdot) u(\cdot)$ is additive in $u$: the function for $u + v$ is the
sum of the functions for $u$ and for $v$. This is one half of the linearity of
`IntegralOperator.productCLM`. -/
theorem prodFactor_add (l : C(X × X, ℝ)) (x : X) (u v : C(X, ℝ)) :
    prodFactor l x (u + v) = prodFactor l x u + prodFactor l x v := by
  ext y
  simp only [prodFactor_apply, ContinuousMap.add_apply]
  ring

omit [CompactSpace X] in
/-- The function $w_x = l(x, \cdot) u(\cdot)$ is homogeneous in $u$: the function for $r u$ is $r$
times the function for $u$. This is the other half of the linearity of
`IntegralOperator.productCLM`. -/
theorem prodFactor_smul (l : C(X × X, ℝ)) (x : X) (r : ℝ) (u : C(X, ℝ)) :
    prodFactor l x (r • u) = r • prodFactor l x u := by
  ext y
  simp only [prodFactor_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

/-- For a continuous kernel $l$ on the compact space $X \times X$, $x \in X$ and $u \in C(X)$,
$$\|l(x, \cdot) \, u(\cdot)\|_\infty \le \|l\|_\infty \, \|u\|_\infty.$$
-/
theorem norm_prodFactor_le (l : C(X × X, ℝ)) (x : X) (u : C(X, ℝ)) :
    ‖prodFactor l x u‖ ≤ ‖l‖ * ‖u‖ := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro y
  rw [prodFactor_apply, norm_mul]
  exact mul_le_mul (l.norm_coe_le_norm _) (u.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)

/-- Let $l$ be a continuous kernel, let $x, z \in X$, and let $\eta \ge 0$ with
$|l(x, y) - l(z, y)| \le \eta$ for every $y \in X$. Then for every $u \in C(X)$,
$$\|l(x, \cdot) \, u(\cdot) - l(z, \cdot) \, u(\cdot)\|_\infty \le \eta \, \|u\|_\infty.$$
-/
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

/-- For a continuous kernel $l$ and $u \in C(X)$, the map $x \mapsto l(x, \cdot) \, u(\cdot)$ from
$X$ to $C(X)$ is continuous. This follows from the uniform continuity of $l$ on the compact
space $X \times X$. -/
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

/-- Let $g$ be an admissible kernel, let $l$ be a continuous kernel, let $P$ be a bounded operator
on $C(X)$, and let $u \in C(X)$. Let $x, z \in X$ and $\eta \ge 0$ with
$|l(x, y) - l(z, y)| \le \eta$ for every $y$. Then
$$\left| \int g(x, y) (P w_x)(y) \, d\nu(y) - \int g(z, y) (P w_z)(y) \, d\nu(y) \right| \le c_g
  \|P\| \eta \|u\| + \left( \int |g(x, y) - g(z, y)| \, d\nu(y) \right) \|P\| \|l\| \|u\|,$$
where $w_x = l(x, \cdot) u(\cdot)$ and $c_g$ is the row bound `IntegralOperator.rowBound ν g`.

The first term comes from the variation of the smooth factor $l$ and the second from the
variation of the singular factor $g$. This is the estimate behind the equicontinuity in the
proof of Theorem 12.5.1 of [han2009theoretical], §12.5. -/
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

/-- Let $g$ be an admissible kernel, let $l$ be a continuous kernel, and let $C_P, C_u \ge 0$ and
$\varepsilon > 0$. Then there is $\delta > 0$ such that for every bounded operator $P$ on $C(X)$
with $\|P\| \le C_P$, every $u \in C(X)$ with $\|u\| \le C_u$, and all $x, z \in X$ with
$d(x, z) < \delta$,
$$\left| \int g(x, y) (P w_x)(y) \, d\nu(y) - \int g(z, y) (P w_z)(y) \, d\nu(y) \right| <
  \varepsilon,$$
where $w_x = l(x, \cdot) u(\cdot)$.

The continuity of one function $K_n u$ and the equicontinuity of the family
$\{K_n u : n, \|u\| \le 1\}$ both follow from this. -/
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

/-- Let $g$ be an admissible kernel, let $l$ be a continuous kernel, let $P$ be a bounded operator
on $C(X)$, and let $u \in C(X)$. Then the function
$x \mapsto \int g(x, y) (P w_x)(y) \, d\nu(y)$, with $w_x = l(x, \cdot) u(\cdot)$, is
continuous. -/
theorem continuous_product (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (u : C(X, ℝ)) :
    Continuous fun x => ∫ y, g (x, y) * (P (prodFactor l x u)) y ∂ν := by
  refine Metric.continuous_iff.2 fun x₀ ε hε => ?_
  obtain ⟨δ, hδ, hbound⟩ :=
    exists_delta_product hg l (Cp := ‖P‖) (Cu := ‖u‖) (norm_nonneg P) (norm_nonneg u) hε
  refine ⟨δ, hδ, fun x hx => ?_⟩
  rw [Real.dist_eq]
  exact hbound P le_rfl u le_rfl x x₀ hx

/-- Let $X$ be a compact metric space with a Borel measure $\nu$, let $g$ be an admissible kernel,
let $l$ be a continuous kernel on $X \times X$, and let $P$ be a bounded linear operator on
$C(X)$. The **product integration operator** is the bounded linear operator $K_n$ on $C(X)$
given by
$$(K_n u)(x) = \int g(x, y) \, \big( P (l(x, \cdot) \, u(\cdot)) \big)(y) \, d\nu(y).$$
This is equation (12.5.14) of [han2009theoretical], §12.5, with an arbitrary bounded operator
$P$ in place of the interpolation operator of a concrete rule.

The operator is not an instance of the Nyström operator `IntegralOperator.nystromCLM`, because
the weights $\int g(x, y) \varphi_j(y) \, d\nu(y)$ depend on the point $x$. It is built with the
bound $c_g \|P\| \|l\|$, where $c_g$ is `IntegralOperator.rowBound ν g`. The argument `hg` is
the proof that $g$ is admissible. -/
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

/-- The product integration operator maps $u$ to $x \mapsto \int g(x, y) \, (P w_x)(y) \, d\nu(y)$,
where $w_x = l(x, \cdot) u(\cdot)$. -/
@[simp]
theorem productCLM_apply (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (u : C(X, ℝ)) (x : X) :
    productCLM hg l P u x = ∫ y, g (x, y) * (P (prodFactor l x u)) y ∂ν := rfl

/-- Let $g$ be an admissible kernel, let $l$ be a continuous kernel, and let $P$ be a bounded
operator on $C(X)$. Then the product integration operator satisfies
$$\|K_n\| \le c_g \, \|P\| \, \|l\|,$$
where $c_g = \sup_x \int |g(x, y)| \, d\nu(y)$ is `IntegralOperator.rowBound ν g`. So the
product integration operators of a family of uniformly bounded $P$ are uniformly bounded. This
is the bound in the proof of Theorem 12.5.1 of [han2009theoretical], §12.5. -/
theorem norm_productCLM_le (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) :
    ‖productCLM hg l P‖ ≤ rowBound ν g * (‖P‖ * ‖l‖) := by
  refine LinearMap.mkContinuous_norm_le _ ?_ _
  have := hg.rowBound_nonneg (μ := ν) (k := g)
  positivity

/-- Let $g$ be an admissible kernel and let $l$ be a continuous kernel. Then the product integration
operator for $P = 1$ is the integral operator of the kernel $(x, y) \mapsto g(x, y) \, l(x, y)$:
$$\int g(x, y) \, l(x, y) \, u(y) \, d\nu(y).$$

The kernel $g l$ is admissible by the splitting rule
`IntegralOperator.IsAdmissibleKernel.mul_continuousMap`, and its operator is
`IntegralOperator.admissibleKernelCLM`. -/
theorem productCLM_one (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ)) :
    productCLM hg l 1 = admissibleKernelCLM (hg.mul_continuousMap l) := by
  ext u x
  rw [productCLM_apply, admissibleKernelCLM_apply]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [one_apply_eq_self, prodFactor_apply]
  ring

/-- Let $g$ be an admissible kernel, let $l$ be a continuous kernel, let $P$ be a bounded operator
on $C(X)$, and let $K$ be the integral operator of the admissible kernel $g l$. Then for every
$u \in C(X)$ and $x \in X$,
$$(Ku - K_n u)(x) = \int g(x, y) \, (w_x - P w_x)(y) \, d\nu(y), \qquad w_x = l(x, \cdot) \,
  u(\cdot).$$

The proof uses only the linearity of the integral, and the estimate
`IntegralOperator.norm_admissibleKernelCLM_sub_productCLM_le` follows from it. This identity
turns an interpolation error into an operator error in [han2009theoretical], §12.5. -/
theorem admissibleKernelCLM_sub_productCLM_apply (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (u : C(X, ℝ)) (x : X) :
    (admissibleKernelCLM (hg.mul_continuousMap l) u - productCLM hg l P u) x
      = ∫ y, g (x, y) * (prodFactor l x u - P (prodFactor l x u)) y ∂ν := by
  rw [ContinuousMap.sub_apply, ← productCLM_one hg l, productCLM_apply, productCLM_apply,
    ← integral_sub (hg.integrable_mul _ x) (hg.integrable_mul _ x)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ContinuousMap.sub_apply, one_apply_eq_self]
  ring

/-- Let $g$ be an admissible kernel, let $l$ be a continuous kernel, let $P$ be a bounded operator
on $C(X)$, let $K$ be the integral operator of the admissible kernel $g l$, and let
$u \in C(X)$. If $C \ge 0$ and
$$\|w_x - P w_x\|_\infty \le C \quad \text{for every } x \in X, \qquad w_x = l(x, \cdot) \,
  u(\cdot),$$
then
$$\|Ku - K_n u\|_\infty \le c_g \, C,$$
where $c_g$ is the row bound `IntegralOperator.rowBound ν g`.

With a uniform bound on $\|(\mu - K_n)^{-1}\|$, this turns the interpolation error of a concrete
rule into the rate of convergence of $u_n$ to $u$, in [han2009theoretical], §12.5, for the
product trapezoidal rule and for product integration on graded meshes. -/
theorem norm_admissibleKernelCLM_sub_productCLM_le (hg : IsAdmissibleKernel ν g)
    (l : C(X × X, ℝ)) (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (u : C(X, ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ x : X, ‖prodFactor l x u - P (prodFactor l x u)‖ ≤ C) :
    ‖admissibleKernelCLM (hg.mul_continuousMap l) u - productCLM hg l P u‖
      ≤ rowBound ν g * C := by
  rw [ContinuousMap.norm_le _ (mul_nonneg hg.rowBound_nonneg hC)]
  intro x
  rw [admissibleKernelCLM_sub_productCLM_apply, Real.norm_eq_abs]
  exact (hg.abs_integral_mul_le _ x).trans
    (mul_le_mul (hg.le_rowBound x) (hP x) (norm_nonneg _) hg.rowBound_nonneg)

/-- Let $g$ be an admissible kernel, let $l$ be a continuous kernel, and let $(P_n)$ be bounded
operators on $C(X)$ with $P_n v \to v$ for every $v \in C(X)$. Then for every $u \in C(X)$, the
product integration operators satisfy
$$K_n u \to K u \quad \text{in } C(X),$$
where $K$ is the product integration operator for $P = 1$, that is, the integral operator of
$g l$ (`IntegralOperator.productCLM_one`). This is Exercise 12.5.1 of [han2009theoretical],
§12.5, and assumption A2 of the theory of collectively compact operators.

The bound $|(K_n u)(x) - (Ku)(x)| \le c_g \|P_n w_x - w_x\|$ is uniform in $x$, because the set
$\{w_x = l(x, \cdot) u(\cdot) : x \in X\}$ is compact in $C(X)$ and a pointwise convergent
sequence of bounded operators converges uniformly on compact sets
(`tendstoUniformlyOn_of_tendsto_of_isCompact`). -/
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

/-- Let $g$ be an admissible kernel, let $l$ be a continuous kernel, and let $(P_n)$ be bounded
operators on $C(X)$ with $\|P_n\| \le C_P$ for every $n$. Then the family of product integration
operators $(K_n)$ of the $P_n$ is collectively compact. This is assumption A3 of the theory of
collectively compact operators. With the pointwise convergence
`IntegralOperator.tendsto_productCLM`, it is what the proof of Theorem 12.5.1 of
[han2009theoretical], §12.5, verifies.

The images of the unit ball are uniformly bounded by `IntegralOperator.norm_productCLM_le` and
equicontinuous by `IntegralOperator.exists_delta_product`, so the Arzelà–Ascoli theorem in the
form `ContinuousMap.isCompact_closure_of_forall_norm_le` applies. -/
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
