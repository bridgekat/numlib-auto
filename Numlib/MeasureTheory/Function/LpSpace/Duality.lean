/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.LpSpace.Duality`, beside
`Mathlib.MeasureTheory.Function.Holder` which defines the pairing.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.MeasureTheory.Function.LpSpace.Convergence

/-!
# The duality between $L^p$ and $L^q$

Let $\mu$ be a measure, let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let
$p, q \in [1, \infty]$ be conjugate exponents, $1/p + 1/q = 1$. Every $u \in L^q(\mu)$ defines the
continuous linear functional $f \mapsto \int u f \, d\mu$ on $L^p(\mu)$. On a $\sigma$-finite
measure this map $L^q \to (L^p)^*$ is an isometry. It is onto when $1 \le p < \infty$: every
continuous linear functional $\varphi$ on $L^p$ is integration against a unique $u \in L^q$, and
$\|u\|_q = \|\varphi\|$. These are the **Riesz representation theorems** for $L^p$, Theorem 4.11 of
[brezis2011functional] for $1 < p < \infty$ and Theorem 4.14 for $p = 1$. Consequently $L^p$ is
reflexive for $1 < p < \infty$ (Theorem 4.10 of [brezis2011functional]). In contrast, the map
$L^1 \to (L^\infty)^*$ is not onto, as discussed in §4.3 of [brezis2011functional].

## Main definitions

* `MeasureTheory.Lp.toDualCLM`: the continuous linear map $L^q \to (L^p)^*$,
  $u \mapsto (f \mapsto \int u f \, d\mu)$.
* `MeasureTheory.Lp.toDual`: the same map as a linear isometry, for a $\sigma$-finite measure.
* `MeasureTheory.Lp.dualEquiv`: the identification $(L^p)^* = L^q$ as a linear isometric
  equivalence, for $1 \le p < \infty$ and a $\sigma$-finite measure.
* `MeasureTheory.Lp.dualToSignedMeasure`: the finite signed measure
  $E \mapsto \varphi(\mathbf{1}_E)$ of a functional $\varphi$ on $L^p$ of a finite measure.
* `MeasureTheory.extremal`: the function $|u|^{r - 2} \bar u$ that realizes the norm of $u$ in the
  pairing.

## Main results

* `MeasureTheory.Lp.norm_toDualCLM_apply_of_ne_top`, `MeasureTheory.Lp.norm_toDualCLM_apply`: the
  norm of $f \mapsto \int u f \, d\mu$ is $\|u\|_q$, for every measure when $q \neq \infty$, and for
  a $\sigma$-finite measure in general.
* `MeasureTheory.Lp.exists_forall_eq_integral_of_isFiniteMeasure`,
  `MeasureTheory.Lp.exists_forall_eq_integral`: for real scalars and $1 \le p < \infty$, every
  continuous linear functional on $L^p$ is $f \mapsto \int u f \, d\mu$ for some $u \in L^q$, on a
  finite and on a $\sigma$-finite measure.
* `MeasureTheory.Lp.toDual_surjective`: the **Riesz representation theorem**, the map
  $L^q \to (L^p)^*$ is onto for $1 \le p < \infty$ and a $\sigma$-finite measure.
* `MeasureTheory.Lp.isReflexive_of_one_lt_of_ne_top`, `MeasureTheory.Lp.instIsReflexive`: $L^p$ is
  reflexive for $1 < p < \infty$ and a $\sigma$-finite measure.
* `MeasureTheory.Lp.exists_strongDual_top_apply_eq`: for a $\sigma$-finite measure without atoms on
  a finite-dimensional real normed space and a point $x_0$ whose neighbourhoods have positive
  measure, some functional on $L^\infty$ is the evaluation at $x_0$ on the continuous compactly
  supported functions and is not given by any $u \in L^1$.
* `MeasureTheory.Lp.not_surjective_toDual_top`: on a nonempty open subset of a finite-dimensional
  real normed space, with a $\sigma$-finite measure without atoms that is positive on nonempty open
  sets, the map $L^1 \to (L^\infty)^*$ is not onto.
* `MeasureTheory.continuous_integral_mul_prod`: the map $(f, g) \mapsto \int f g \, d\mu$ on
  $L^p \times L^q$ is continuous.

## Proof outline

Brezis proves Theorem 4.11 from the reflexivity of $L^p$, by uniform convexity and the Milman–Pettis
theorem, and Theorem 4.14 from the case $p = 2$ with a weight. Here both are proved at once by the
Radon–Nikodym theorem, which needs neither. On a finite measure, a functional $\varphi$ on $L^p$,
$p < \infty$, defines the finite signed measure $E \mapsto \varphi(\mathbf{1}_E)$, which is
absolutely continuous with respect to $\mu$. Its Radon–Nikodym derivative $u_0$ (Mathlib's
`MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq`) represents $\varphi$ on indicator functions,
hence on simple functions, and, by bounded approximation, on bounded functions. The bound
$\|u_0\|_q \le \|\varphi\|$ comes from testing $\varphi$ against truncations of the functions
$|u_0|^{q - 2} u_0$ of the book, as in the proof of Theorem 4.14 of [brezis2011functional]. The
density of the bounded functions completes the proof.

The $\sigma$-finite case reduces to the finite case by a weight $\theta \in L^p$ with
$0 < \theta \le 1$: multiplication by $\theta$ is an isometry of $L^p(\theta^p \mu)$ onto
$L^p(\mu)$. The complex case follows from the real case, applied to the real and imaginary parts of
$\varphi$ on real functions. Reflexivity is then a formal consequence of the two surjections
$L^q \to (L^p)^*$ and $L^p \to (L^q)^*$.

## Implementation notes

* The map `MeasureTheory.Lp.toDualCLM` is Mathlib's `ContinuousLinearMap.lpPairing` for the
  multiplication of $\mathbb{K}$. For $p = q = 2$ over $\mathbb{R}$ it is the inner product
  (`MeasureTheory.L2.inner_eq_integral_mul`).
* The pairing is bilinear, $\int u f$ and not $\int \bar u f$, because `StrongDual 𝕜 E` consists of
  $\mathbb{K}$-linear functionals. For $\mathbb{K} = \mathbb{C}$ the extremal function therefore
  contains a complex conjugate.
* Without $\sigma$-finiteness the isometry can fail for $q = \infty$: for a measure that is infinite
  on every nonempty measurable set, $L^1 = 0$.
* The hypotheses $p \ge 1$, $q \ge 1$ and $1/p + 1/q = 1$ are the instances `Fact (1 ≤ p)`,
  `Fact (1 ≤ q)` and `p.HolderConjugate q`.
-/

noncomputable section

open Filter Metric Set Topology
open scoped ENNReal NNReal symmDiff

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} {μ : Measure α}

/-! ### The pairing -/

namespace Lp

variable (𝕜 p q μ) in
/-- Let $p, q \in [1, \infty]$ be conjugate exponents, $1/p + 1/q = 1$. The **pairing** of
$L^q(\mu; \mathbb{K})$ with the dual of $L^p(\mu; \mathbb{K})$ is the continuous linear map
$$L^q(\mu) \to L^p(\mu)^*, \qquad u \mapsto \Big(f \mapsto \int u f \, d\mu\Big).$$
This is the operator $T$ of Step 3 of the proof of Theorem 4.10 of [brezis2011functional].

The definition is Mathlib's `ContinuousLinearMap.lpPairing` for the multiplication of
$\mathbb{K}$. -/
def toDualCLM [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] :
    Lp 𝕜 q μ →L[𝕜] StrongDual 𝕜 (Lp 𝕜 p μ) :=
  (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ q p

/-- For conjugate exponents $p, q \in [1, \infty]$, $u \in L^q(\mu)$ and $f \in L^p(\mu)$, the value
of `MeasureTheory.Lp.toDualCLM` at $u$ and $f$ is $\int u(x) f(x) \, d\mu(x)$. -/
theorem toDualCLM_apply [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] (u : Lp 𝕜 q μ)
    (f : Lp 𝕜 p μ) : toDualCLM 𝕜 p q μ u f = ∫ x, u x * f x ∂μ := by
  change (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ q p u f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rfl

/-- Hölder's inequality for the pairing. For conjugate exponents $p, q \in [1, \infty]$ and
$u \in L^q(\mu)$, the functional $f \mapsto \int u f \, d\mu$ on $L^p(\mu)$ has norm at most
$\|u\|_q$. -/
theorem norm_toDualCLM_apply_le [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (u : Lp 𝕜 q μ) : ‖toDualCLM 𝕜 p q μ u‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun f => ?_
  rw [toDualCLM_apply]
  have h : ‖∫ x, u x * f x ∂μ‖ₑ ≤ ‖u‖ₑ * ‖f‖ₑ := by
    calc ‖∫ x, u x * f x ∂μ‖ₑ ≤ ∫⁻ x, ‖u x * f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun x => u x * f x) 1 μ :=
        (eLpNorm_one_eq_lintegral_enorm ((Lp.aestronglyMeasurable u).mul
          (Lp.aestronglyMeasurable f))).symm
      _ ≤ ‖ContinuousLinearMap.mul 𝕜 𝕜‖ₑ * eLpNorm u q μ * eLpNorm f p μ :=
        eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm (ContinuousLinearMap.mul 𝕜 𝕜)
          (Lp.aestronglyMeasurable u) (Lp.aestronglyMeasurable f)
      _ ≤ 1 * ‖u‖ₑ * ‖f‖ₑ := by
        rw [Lp.enorm_def, Lp.enorm_def]
        gcongr
        rw [enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
          coe_nnnorm, NNReal.coe_one]
        exact ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
      _ = ‖u‖ₑ * ‖f‖ₑ := by rw [one_mul]
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, coe_nnnorm] at h
  exact h

end Lp

/-! ### The inner product of $L^2$ -/

open scoped InnerProductSpace in
/-- **The inner product of two real functions in $L^2(\mu)$ is the integral of their product**: for
$f, g \in L^2(\mu; \mathbb{R})$,
$$\langle f, g \rangle = \int f g \, d\mu.$$

This is the real case of `MeasureTheory.L2.inner_def`. It shows that the pairing
`MeasureTheory.Lp.toDualCLM ℝ 2 2 μ` is the inner product. -/
theorem L2.inner_eq_integral_mul (f g : Lp ℝ 2 μ) : ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])

/-!
### The extremal test functions

For $u \colon \alpha \to \mathbb{K}$ and $r \in \mathbb{R}$, the function $|u|^{r - 2} \bar u$ is
the test function against which $u \in L^r$ is paired to realize its norm. Pointwise,
$u \cdot |u|^{r - 2} \bar u = |u|^r$ and $\big||u|^{r - 2} \bar u\big| \le |u|^{r - 1}$. For $r = 1$
it is $\bar u / |u|$, the conjugate of the sign of $u$.
-/

section Extremal

variable (u : α → 𝕜) (r : ℝ)

/-- Let $u \colon \alpha \to \mathbb{K}$ and $r \in \mathbb{R}$. The **extremal test function** of
$u$ is
$$x \mapsto |u(x)|^{r - 2} \, \overline{u(x)}.$$
It is $0$ where $u = 0$. -/
def extremal (x : α) : 𝕜 := ((‖u x‖ ^ (r - 2) : ℝ) : 𝕜) * starRingEnd 𝕜 (u x)

omit [MeasurableSpace α] in
/-- For $u \colon \alpha \to \mathbb{K}$, $r \neq 0$ and every $x$, $u(x) \cdot |u(x)|^{r - 2}
\overline{u(x)} = |u(x)|^r$. -/
theorem mul_extremal {r : ℝ} (hr : r ≠ 0) (x : α) :
    u x * extremal u r x = ((‖u x‖ ^ r : ℝ) : 𝕜) := by
  unfold extremal
  by_cases h : u x = 0
  · simp [h, Real.zero_rpow hr]
  · rw [mul_left_comm, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
      ← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.2 h)]
    norm_num

omit [MeasurableSpace α] in
/-- For $u \colon \alpha \to \mathbb{K}$, $r \in \mathbb{R}$ and every $x$, the extremal test
function satisfies $\big||u(x)|^{r - 2} \overline{u(x)}\big| \le |u(x)|^{r - 1}$.

Equality holds where $u(x) \neq 0$, but the theorem states only the inequality. -/
theorem norm_extremal_le (r : ℝ) (x : α) : ‖extremal u r x‖ ≤ ‖u x‖ ^ (r - 1) := by
  unfold extremal
  by_cases h : u x = 0
  · simp only [h, norm_zero, map_zero, mul_zero]
    positivity
  · rw [norm_mul, RCLike.norm_conj, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
      ← Real.rpow_add_one (norm_ne_zero_iff.2 h), show r - 2 + 1 = r - 1 by ring]

omit [MeasurableSpace α] in
/-- For $u \colon \alpha \to \mathbb{K}$ and every $x$, the extremal test function for $r = 1$, the
conjugate of the sign of $u$, has absolute value at most $1$. -/
theorem norm_extremal_one_le (x : α) : ‖extremal u 1 x‖ ≤ 1 := by
  simpa using norm_extremal_le u 1 x

/-- If $u$ is almost everywhere strongly measurable, then for every $r \in \mathbb{R}$ its extremal
test function is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_extremal {u : α → 𝕜} (hu : AEStronglyMeasurable u μ) (r : ℝ) :
    AEStronglyMeasurable (extremal u r) μ := by
  unfold extremal
  exact (RCLike.continuous_ofReal.comp_aestronglyMeasurable
    (hu.norm.aemeasurable.pow_const (r - 2)).aestronglyMeasurable).mul
    (RCLike.continuous_conj.comp_aestronglyMeasurable hu)

/-- Let $u$ be almost everywhere strongly measurable, let $r > 1$, and let $p, q \in [0, \infty]$
satisfy $p (r - 1) = q$. Then the extremal test function $v = |u|^{r - 2} \bar u$ satisfies
$$\|v\|_p \le \|u\|_q^{r - 1}.$$
In particular $v \in L^p$ when $u \in L^q$. For $q = r$ the condition is $(r - 1) p = r$.

The seminorms are the `ℝ≥0∞`-valued `MeasureTheory.eLpNorm`. -/
theorem eLpNorm_extremal_le {u : α → 𝕜} (hu : AEStronglyMeasurable u μ) {r : ℝ} (hr : 1 < r)
    (hpq : p * ENNReal.ofReal (r - 1) = q) :
    eLpNorm (extremal u r) p μ ≤ eLpNorm u q μ ^ (r - 1) := by
  calc eLpNorm (extremal u r) p μ ≤ eLpNorm (fun x => ‖u x‖ ^ (r - 1)) p μ :=
        eLpNorm_mono_real (aestronglyMeasurable_extremal hu r) (norm_extremal_le u r)
    _ = eLpNorm u (p * ENNReal.ofReal (r - 1)) μ ^ (r - 1) :=
        eLpNorm_norm_rpow u hu (by linarith)
    _ = eLpNorm u q μ ^ (r - 1) := by rw [hpq]

end Extremal

/-! ### The signed measure of a functional on $L^p$ of a finite measure -/

/-- Let $E$ be a normed group, let $1 \le p < \infty$, let $(s_i)_{i \in \mathbb{N}}$ be pairwise
disjoint measurable sets of finite measure whose union $s$ has finite measure, and let
$c \in E$. Then $\sum_i c \mathbf{1}_{s_i} = c \mathbf{1}_s$, with the series convergent in
$L^p(\mu; E)$. -/
theorem hasSum_indicatorConstLp_iUnion {E : Type*} [NormedAddCommGroup E] [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {s : ℕ → Set α} (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise fun i j => Disjoint (s i) (s j)) (hμs : ∀ i, μ (s i) ≠ ∞)
    (hμ : μ (⋃ i, s i) ≠ ∞) (c : E) :
    HasSum (fun i => indicatorConstLp p (hs i) (hμs i) c)
      (indicatorConstLp p (MeasurableSet.iUnion hs) hμ c) := by
  classical
  have hmeas : ∀ F : Finset ℕ, MeasurableSet (⋃ i ∈ F, s i) := fun F =>
    F.measurableSet_biUnion fun i _ => hs i
  have hfin : ∀ F : Finset ℕ, μ (⋃ i ∈ F, s i) ≠ ∞ := fun F =>
    ((measure_mono (iUnion₂_subset fun i _ => subset_iUnion s i)).trans_lt hμ.lt_top).ne
  -- the partial sums are the indicators of the finite unions
  have hpart : ∀ F : Finset ℕ, ∑ i ∈ F, indicatorConstLp p (hs i) (hμs i) c =
      indicatorConstLp p (hmeas F) (hfin F) c := fun F => by
    apply Lp.ext
    have h1 : ∀ᵐ x ∂μ, ∀ i ∈ F, indicatorConstLp p (hs i) (hμs i) c x =
        (s i).indicator (fun _ => c) x :=
      (eventually_all_finset F).2 fun i _ => indicatorConstLp_coeFn
    filter_upwards [Lp.coeFn_fun_finsetSum F fun i => indicatorConstLp p (hs i) (hμs i) c, h1,
      indicatorConstLp_coeFn (p := p) (hs := hmeas F) (hμs := hfin F) (c := c)] with x hx h1 hx'
    rw [hx, hx', Finset.indicator_biUnion_apply F s (hd.set_pairwise _)]
    exact Finset.sum_congr rfl h1
  -- the measure of the remainder tends to zero
  have htail : Tendsto (fun F : Finset ℕ => μ ((⋃ i ∈ F, s i) ∆ (⋃ i, s i))) atTop (𝓝 0) := by
    have hsum : ∑' i, μ (s i) ≠ ∞ := by rwa [← measure_iUnion hd hs]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_tsum_compl_atTop_zero hsum) (fun _ => zero_le) fun F => ?_
    rw [← measure_iUnion (hd.comp_of_injective Subtype.val_injective) fun i => hs i]
    refine measure_mono fun x hx => ?_
    rcases hx with ⟨hx, hx'⟩ | ⟨hx, hxF⟩
    · exact absurd (mem_iUnion.2 ((mem_iUnion₂.1 hx).imp fun i hi => hi.2)) hx'
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨⟨i, fun hiF => hxF (mem_iUnion₂.2 ⟨i, hiF, hi⟩)⟩, hi⟩
  exact (tendsto_indicatorConstLp_set (t := fun F : Finset ℕ => ⋃ i ∈ F, s i) (ht := hmeas)
    (hμt := hfin) hp htail).congr fun F => (hpart F).symm

namespace Lp

variable [IsFiniteMeasure μ] [Fact (1 ≤ p)]

open scoped Classical in
/-- Let $\mu$ be a finite measure, let $1 \le p < \infty$, and let $\varphi$ be a continuous linear
functional on $L^p(\mu; \mathbb{R})$. The **signed measure of $\varphi$** is the finite signed
measure $E \mapsto \varphi(\mathbf{1}_E)$ on the measurable sets $E$. Its Radon–Nikodym
derivative with respect to $\mu$ represents $\varphi$.

Its value on a set that is not measurable is $0$. The countable additivity is the convergence
$\mathbf{1}_{\bigcup_i E_i} = \sum_i \mathbf{1}_{E_i}$ in $L^p$
(`MeasureTheory.hasSum_indicatorConstLp_iUnion`). -/
def dualToSignedMeasure (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) : SignedMeasure α where
  measureOf' s :=
    if hs : MeasurableSet s then φ (indicatorConstLp p hs (measure_ne_top μ s) 1) else 0
  empty' := by simp
  not_measurable' _ hs := dite_eq_right hs
  m_iUnion' s hs hd := by
    simp only [hs, MeasurableSet.iUnion hs, dite_true]
    exact (hasSum_indicatorConstLp_iUnion hp hs hd (fun i => measure_ne_top μ _)
      (measure_ne_top μ _) (1 : ℝ)).mapL φ

open scoped Classical in
/-- For a measurable set $E$, the signed measure `MeasureTheory.Lp.dualToSignedMeasure` of $\varphi$
has the value $\varphi(\mathbf{1}_E)$ at $E$. -/
theorem dualToSignedMeasure_apply (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) {E : Set α}
    (hE : MeasurableSet E) :
    dualToSignedMeasure hp φ E = φ (indicatorConstLp p hE (measure_ne_top μ E) 1) := by
  change dite _ _ _ = _
  rw [dite_eq_left hE]

/-- The signed measure $E \mapsto \varphi(\mathbf{1}_E)$ is absolutely continuous with respect to
$\mu$, because the indicator function of a $\mu$-null set is $0$ in $L^p$. -/
theorem dualToSignedMeasure_absolutelyContinuous (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    dualToSignedMeasure hp φ ≪ᵥ μ.toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun E hE hμE => ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hμE
  rw [dualToSignedMeasure_apply hp φ hE]
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have : indicatorConstLp p hE (measure_ne_top μ E) (1 : ℝ) = 0 := by
    rw [← norm_eq_zero, norm_indicatorConstLp hp0 hp, measureReal_def, hμE, ENNReal.toReal_zero,
      Real.zero_rpow (one_div_ne_zero (ENNReal.toReal_ne_zero.2 ⟨hp0, hp⟩)), mul_zero]
  rw [this, map_zero]

/-- Let $u_0$ be the Radon–Nikodym derivative of the signed measure
$E \mapsto \varphi(\mathbf{1}_E)$ with respect to $\mu$. Then
$\int_E u_0 \, d\mu = \varphi(\mathbf{1}_E)$ for every measurable set $E$. -/
theorem setIntegral_rnDeriv_dualToSignedMeasure (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    {E : Set α} (hE : MeasurableSet E) :
    ∫ x in E, (dualToSignedMeasure hp φ).rnDeriv μ x ∂μ =
      φ (indicatorConstLp p hE (measure_ne_top μ E) 1) := by
  rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hE,
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ (dualToSignedMeasure_absolutelyContinuous hp φ),
    dualToSignedMeasure_apply]

omit [IsFiniteMeasure μ] [Fact (1 ≤ p)] in
/-- Let $s$ be a measurable set of finite measure and let $c \in \mathbb{R}$. In $L^p(\mu)$, the
class of the function $c \mathbf{1}_s$ is $c$ times the class of $\mathbf{1}_s$. Here
$p \in [0, \infty]$ is arbitrary. -/
theorem toLp_indicator_const_eq_smul {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ)
    (h : MemLp (s.indicator fun _ => c) p μ) :
    h.toLp _ = c • indicatorConstLp p hs hμs (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [h.coeFn_toLp, Lp.coeFn_smul c (indicatorConstLp p hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  by_cases hx : x ∈ s <;> simp [hx]

/-- Let $u_0$ be the Radon–Nikodym derivative of the signed measure
$E \mapsto \varphi(\mathbf{1}_E)$ with respect to $\mu$. Then
$\varphi(g) = \int u_0 \, g \, d\mu$ for every simple function $g$. -/
theorem apply_toLp_simpleFunc_eq_integral_rnDeriv_mul (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    (g : SimpleFunc α ℝ) :
    φ ((g.memLp_of_isFiniteMeasure p μ).toLp g) =
      ∫ x, (dualToSignedMeasure hp φ).rnDeriv μ x * g x ∂μ := by
  set u₀ := (dualToSignedMeasure hp φ).rnDeriv μ with hu₀_def
  have hu₀ : Integrable u₀ μ := SignedMeasure.integrable_rnDeriv _ _
  induction g using SimpleFunc.induction with
  | @const c s hs =>
    have hg : ⇑(SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0)) =
        s.indicator fun _ => c := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    simp only [hg]
    rw [toLp_indicator_const_eq_smul hs (measure_ne_top μ s), map_smul, smul_eq_mul,
      ← setIntegral_rnDeriv_dualToSignedMeasure hp φ hs]
    simp_rw [← Set.indicator_mul_right s (fun x => u₀ x) (fun _ => c)]
    rw [integral_indicator hs, integral_mul_const, mul_comm]
  | @add f g _ hf hg =>
    obtain ⟨Cf, hCf⟩ := f.exists_forall_norm_le
    obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
    have := MemLp.toLp_add (f.memLp_of_isFiniteMeasure p μ) (g.memLp_of_isFiniteMeasure p μ)
    simp only [FunLike.coe_add]
    rw [this, map_add, hf, hg, ← integral_add
      (hu₀.mul_bdd f.aestronglyMeasurable (ae_of_all _ hCf))
      (hu₀.mul_bdd g.aestronglyMeasurable (ae_of_all _ hCg))]
    simp only [Pi.add_apply, mul_add]

/-- Let $u_0$ be the Radon–Nikodym derivative of the signed measure
$E \mapsto \varphi(\mathbf{1}_E)$ with respect to $\mu$. If $f \in L^p(\mu)$ and $|f| \le C$
almost everywhere for some $C \in \mathbb{R}$, then $\varphi(f) = \int u_0 \, f \, d\mu$. -/
theorem apply_eq_integral_rnDeriv_mul_of_ae_bound (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    (f : Lp ℝ p μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    φ f = ∫ x, (dualToSignedMeasure hp φ).rnDeriv μ x * f x ∂μ := by
  have hp1 : 1 ≤ p := Fact.out
  set u₀ := (dualToSignedMeasure hp φ).rnDeriv μ with hu₀_def
  have hu₀ : Integrable u₀ μ := SignedMeasure.integrable_rnDeriv _ _
  wlog hC0 : 0 ≤ C generalizing C
  · exact this (hC.mono fun x hx => hx.trans (le_max_left C 0)) (le_max_right C 0)
  -- a strongly measurable representative and its bounded simple approximations
  have hfm : StronglyMeasurable ((Lp.aestronglyMeasurable f).mk f) :=
    (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have hfmk : (Lp.aestronglyMeasurable f).mk f =ᵐ[μ] f := (Lp.aestronglyMeasurable f).ae_eq_mk.symm
  have hCmk : ∀ᵐ x ∂μ, ‖(Lp.aestronglyMeasurable f).mk f x‖ ≤ C := by
    filter_upwards [hC, hfmk] with x hx hx'
    rw [hx']; exact hx
  set g : ℕ → SimpleFunc α ℝ := fun n => hfm.approxBounded C n with hg_def
  have hg_bound : ∀ n x, ‖g n x‖ ≤ C := fun n x => hfm.norm_approxBounded_le hC0 n x
  have hg_lim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
    filter_upwards [hfm.tendsto_approxBounded_ae hCmk, hfmk] with x hx hx'
    rw [← hx']; exact hx
  have hg_mem : ∀ n, MemLp (g n) p μ := fun n => (g n).memLp_of_isFiniteMeasure p μ
  -- uniform integrability of a uniformly bounded family
  have hui : UnifIntegrable (fun n => ⇑(g n)) p μ := by
    refine unifIntegrable_of hp1 hp (fun n => (g n).aestronglyMeasurable) fun ε _ =>
      ⟨C.toNNReal + 1, fun n => ?_⟩
    have hset : {x | C.toNNReal + 1 ≤ ‖g n x‖₊} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      have h1 : C.toNNReal + 1 ≤ ‖g n x‖₊ := hx
      rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_one, coe_nnnorm,
        Real.coe_toNNReal C hC0] at h1
      linarith [hg_bound n x]
    simp only [hset, Set.indicator_empty, eLpNorm_fun_zero, zero_le]
  -- convergence in `L^p`, hence of `φ`
  have h1 : Tendsto (fun n => (hg_mem n).toLp (g n)) atTop (𝓝 f) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine (tendsto_Lp_finite_of_tendsto_ae hp1 hp (fun n => (g n).aestronglyMeasurable)
      (Lp.memLp f) hui hg_lim).congr fun n => eLpNorm_congr_ae ?_
    exact ((hg_mem n).coeFn_toLp.sub (ae_eq_refl _)).symm
  have h2 : Tendsto (fun n => φ ((hg_mem n).toLp (g n))) atTop (𝓝 (φ f)) :=
    (φ.continuous.tendsto f).comp h1
  -- the integrals converge by dominated convergence
  have h4 : Tendsto (fun n => ∫ x, u₀ x * g n x ∂μ) atTop (𝓝 (∫ x, u₀ x * f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖u₀ x‖ * C)
      (fun n => (hu₀.mul_bdd (g n).aestronglyMeasurable (ae_of_all _ (hg_bound n))).1)
      (hu₀.norm.mul_const C) (fun n => ae_of_all _ fun x => ?_) ?_
    · rw [norm_mul]
      gcongr
      exact hg_bound n x
    · filter_upwards [hg_lim] with x hx
      exact tendsto_const_nhds.mul hx
  simp_rw [apply_toLp_simpleFunc_eq_integral_rnDeriv_mul hp φ] at h2
  exact tendsto_nhds_unique h2 h4

end Lp

/-! ### The bound in $L^q$, and the representation theorem on a finite measure -/

/-- Let $\mu$ be $\sigma$-finite, let $E$ be a normed group, let $u \colon \alpha \to E$ be almost
everywhere strongly measurable, and let $M \in \mathbb{R}$. Suppose that $\|u\|$ is integrable
on every measurable set $A$ with $\mu(A) < \infty$, and that
$$\int_A \|u\| \, d\mu \le M \mu(A)$$
for every such $A$. Then $\|u\| \le M$ almost everywhere. -/
theorem ae_norm_le_of_forall_setIntegral_norm_le [SigmaFinite μ] {E : Type*}
    [NormedAddCommGroup E] {u : α → E} (hu : AEStronglyMeasurable u μ) {M : ℝ}
    (hint : ∀ A, MeasurableSet A → μ A < ∞ → IntegrableOn (fun x => ‖u x‖) A μ)
    (h : ∀ A, MeasurableSet A → μ A < ∞ → ∫ x in A, ‖u x‖ ∂μ ≤ M * μ.real A) :
    ∀ᵐ x ∂μ, ‖u x‖ ≤ M := by
  -- pass to a strongly measurable representative
  set u' := hu.mk u with hu'_def
  have hu'm : Measurable fun x => ‖u' x‖ := hu.stronglyMeasurable_mk.norm.measurable
  have huu' : u =ᵐ[μ] u' := hu.ae_eq_mk
  have hint' : ∀ A, MeasurableSet A → μ A < ∞ → IntegrableOn (fun x => ‖u' x‖) A μ :=
    fun A hA hAfin => (hint A hA hAfin).congr_fun_ae (ae_restrict_of_ae (huu'.mono fun x hx => by
      simp only [hx]))
  have h' : ∀ A, MeasurableSet A → μ A < ∞ → ∫ x in A, ‖u' x‖ ∂μ ≤ M * μ.real A :=
    fun A hA hAfin =>
      (setIntegral_congr_ae hA (huu'.mono fun x hx _ => by rw [hx])).symm.le.trans (h A hA hAfin)
  suffices ∀ᵐ x ∂μ, ‖u' x‖ ≤ M by
    filter_upwards [this, huu'] with x hx hx'
    rw [hx']; exact hx
  by_contra hcon
  rw [ae_iff] at hcon
  -- the exceptional set is covered by the sets `{M + 1/(n+1) ≤ ‖u'‖}`
  have hcover : {x | ¬ ‖u' x‖ ≤ M} ⊆ ⋃ n : ℕ, {x | M + 1 / (n + 1) ≤ ‖u' x‖} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, not_le] at hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
    exact mem_iUnion.2 ⟨n, by simp only [Set.mem_ofPred_eq]; linarith⟩
  have hS : ∀ n : ℕ, MeasurableSet {x | M + 1 / (n + 1) ≤ ‖u' x‖} := fun n =>
    measurableSet_le measurable_const hu'm
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < μ {x | M + 1 / (n + 1) ≤ ‖u' x‖} := by
    by_contra hall
    push Not at hall
    refine hcon (measure_mono_null hcover (measure_iUnion_null fun n => ?_))
    exact le_antisymm (hall n) zero_le
  -- a subset of positive finite measure on which `‖u'‖ ≥ M + 1/(n+1)`
  obtain ⟨A, hA, hAsub, hApos, hAfin⟩ := Measure.exists_subset_measure_lt_top (hS n) hn
  have hμA : 0 < μ.real A := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hApos.ne' hAfin.ne
  have h1 : (M + 1 / (n + 1)) * μ.real A ≤ ∫ x in A, ‖u' x‖ ∂μ :=
    setIntegral_ge_of_const_le_real hA hAfin.ne (fun x hx => hAsub hx) (hint' A hA hAfin)
  have h2 := h' A hA hAfin
  have h3 : (0 : ℝ) < 1 / (n + 1) * μ.real A := by positivity
  nlinarith

namespace Lp

variable [IsFiniteMeasure μ] [Fact (1 ≤ p)]

/-- Let $\mu$ be a finite measure, let $1 \le p < \infty$ and $q$ be conjugate exponents, and let
$\varphi$ be a continuous linear functional on $L^p(\mu; \mathbb{R})$. The Radon–Nikodym
derivative $u_0$ of the signed measure $E \mapsto \varphi(\mathbf{1}_E)$ satisfies
$\|u_0\|_q \le \|\varphi\|$. This is inequality (14) in the proof of Theorem 4.14 of
[brezis2011functional].

The proof tests $\varphi$ against truncations of the extremal test functions. The seminorm is
the `ℝ≥0∞`-valued `MeasureTheory.eLpNorm`. -/
theorem eLpNorm_rnDeriv_dualToSignedMeasure_le [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    eLpNorm ((dualToSignedMeasure hp φ).rnDeriv μ) q μ ≤ ENNReal.ofReal ‖φ‖ := by
  set u₀ := (dualToSignedMeasure hp φ).rnDeriv μ with hu₀_def
  have hu₀m : Measurable u₀ := SignedMeasure.measurable_rnDeriv _ _
  have hu₀ : Integrable u₀ μ := SignedMeasure.integrable_rnDeriv _ _
  by_cases hq : q = ∞
  · -- the case `q = ∞`, `p = 1`: the sets `{‖u₀‖ > ‖φ‖}` are null
    have hp1' : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).1 hq
    subst hq
    rw [eLpNorm_exponent_top hu₀m.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_bound (ae_norm_le_of_forall_setIntegral_norm_le
      hu₀m.aestronglyMeasurable (fun A _ _ => hu₀.norm.integrableOn) fun A hA hAfin => ?_)
    -- the test function `1_A · sign u₀`
    have hg_bound : ∀ x, ‖A.indicator (extremal u₀ 1) x‖ ≤ 1 := fun x =>
      (norm_indicator_le_norm_self _ _).trans (norm_extremal_one_le u₀ x)
    set g : α → ℝ := A.indicator (extremal u₀ 1) with hg_def
    have hg_meas : AEStronglyMeasurable g μ :=
      (aestronglyMeasurable_extremal hu₀m.aestronglyMeasurable 1).indicator hA
    have hg_mem : MemLp g p μ :=
      (memLp_top_of_bound hg_meas 1 (ae_of_all _ hg_bound)).mono_exponent le_top
    have h1 := apply_eq_integral_rnDeriv_mul_of_ae_bound hp φ (hg_mem.toLp g)
      (hg_mem.coeFn_toLp.mono fun x hx => hx ▸ hg_bound x)
    have h2 : ∫ x, u₀ x * (hg_mem.toLp g) x ∂μ = ∫ x in A, ‖u₀ x‖ ∂μ := by
      rw [← integral_indicator hA]
      refine integral_congr_ae ?_
      filter_upwards [hg_mem.coeFn_toLp] with x hx
      rw [hx]
      by_cases hxA : x ∈ A
      · have := mul_extremal u₀ one_ne_zero x
        simp only [RCLike.ofReal_real_eq_id, id, Real.rpow_one] at this
        simp only [hg_def, Set.indicator_of_mem hxA, this]
      · simp [hg_def, Set.indicator_of_notMem hxA]
    have h3 : ‖hg_mem.toLp g‖ ≤ μ.real A := by
      rw [Lp.norm_toLp, measureReal_def]
      refine ENNReal.toReal_mono hAfin.ne ?_
      rw [hg_def, eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet]
      refine (eLpNorm_le_of_ae_bound (C := 1)
        (aestronglyMeasurable_extremal hu₀m.aestronglyMeasurable 1).restrict
        (ae_of_all _ fun x => norm_extremal_one_le u₀ x)).trans ?_
      rw [Measure.restrict_apply_univ, hp1', ENNReal.toReal_one, inv_one, ENNReal.rpow_one,
        ENNReal.ofReal_one, mul_one]
    calc ∫ x in A, ‖u₀ x‖ ∂μ = φ (hg_mem.toLp g) := by rw [h1, h2]
      _ ≤ ‖φ‖ * ‖hg_mem.toLp g‖ := (le_abs_self _).trans (φ.le_opNorm _)
      _ ≤ ‖φ‖ * μ.real A := by gcongr
  · -- the case `q < ∞`: test against the truncated extremal functions
    have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    have hqr1 : 1 < q.toReal := hpq.symm.lt
    have hqr0 : q.toReal ≠ 0 := by positivity
    have hpq' : p * ENNReal.ofReal (q.toReal - 1) = q := by
      rw [← ENNReal.ofReal_toReal hp, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_comm,
        hpq.symm.sub_one_mul_conj, ENNReal.ofReal_toReal hq]
    -- the truncations
    have hS : ∀ n : ℕ, MeasurableSet {x | ‖u₀ x‖ ≤ n} := fun n =>
      measurableSet_le hu₀m.norm measurable_const
    set v : ℕ → α → ℝ := fun n => {x | ‖u₀ x‖ ≤ n}.indicator u₀ with hv_def
    have hv_bound : ∀ n x, ‖v n x‖ ≤ n := fun n x => by
      change ‖{x | ‖u₀ x‖ ≤ n}.indicator u₀ x‖ ≤ n
      by_cases hx : x ∈ {x | ‖u₀ x‖ ≤ n}
      · rw [Set.indicator_of_mem hx]; exact hx
      · rw [Set.indicator_of_notMem hx]; simp
    have hv_meas : ∀ n, AEStronglyMeasurable (v n) μ := fun n =>
      (hu₀m.indicator (hS n)).aestronglyMeasurable
    have hv_memq : ∀ n, MemLp (v n) q μ := fun n =>
      (memLp_top_of_bound (hv_meas n) n (ae_of_all _ (hv_bound n))).mono_exponent le_top
    -- the bound for each truncation
    have hkey : ∀ n, eLpNorm (v n) q μ ≤ ENNReal.ofReal ‖φ‖ := by
      intro n
      set g := extremal (v n) q.toReal with hg_def
      have hg_bound : ∀ x, ‖g x‖ ≤ (n : ℝ) ^ (q.toReal - 1) := fun x =>
        (norm_extremal_le _ _ x).trans
          (Real.rpow_le_rpow (norm_nonneg _) (hv_bound n x) (by linarith))
      have hg_meas : AEStronglyMeasurable g μ := aestronglyMeasurable_extremal (hv_meas n) _
      have hg_mem : MemLp g p μ :=
        (memLp_top_of_bound hg_meas _ (ae_of_all _ hg_bound)).mono_exponent le_top
      have h1 := apply_eq_integral_rnDeriv_mul_of_ae_bound hp φ (hg_mem.toLp g)
        (hg_mem.coeFn_toLp.mono fun x hx => hx ▸ hg_bound x)
      have h2 : ∫ x, u₀ x * (hg_mem.toLp g) x ∂μ = ∫ x, ‖v n x‖ ^ q.toReal ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hg_mem.coeFn_toLp] with x hx
        rw [hx]
        have hmul := mul_extremal (v n) hqr0 x
        simp only [RCLike.ofReal_real_eq_id, id] at hmul
        rw [← hmul]
        by_cases hxS : x ∈ {x | ‖u₀ x‖ ≤ n}
        · have hv : v n x = u₀ x := Set.indicator_of_mem hxS _
          rw [hg_def, hv]
        · have hv : v n x = 0 := Set.indicator_of_notMem hxS _
          simp only [hg_def, extremal, hv, map_zero, mul_zero]
      set I := ∫ x, ‖v n x‖ ^ q.toReal ∂μ with hI_def
      have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
      have hN := (hv_memq n).eLpNorm_eq_integral_rpow_norm (zero_lt_one.trans_le
        (Fact.out : 1 ≤ q)).ne' hq
      rw [← hI_def] at hN
      set N := I ^ q.toReal⁻¹ with hN_def
      have hN0 : 0 ≤ N := by positivity
      -- `I ≤ ‖φ‖ * N ^ (q - 1)`
      have hIle : I ≤ ‖φ‖ * N ^ (q.toReal - 1) := by
        calc I = φ (hg_mem.toLp g) := by rw [h1, h2]
          _ ≤ ‖φ‖ * ‖hg_mem.toLp g‖ := (le_abs_self _).trans (φ.le_opNorm _)
          _ ≤ ‖φ‖ * N ^ (q.toReal - 1) := by
            gcongr
            rw [Lp.norm_toLp]
            refine (ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by linarith)
              (hv_memq n).eLpNorm_ne_top) (eLpNorm_extremal_le (hv_meas n) hqr1 hpq')).trans ?_
            rw [hN, ENNReal.ofReal_rpow_of_nonneg hN0 (by linarith),
              ENNReal.toReal_ofReal (by positivity)]
      -- hence `N ≤ ‖φ‖`
      have hNle : N ≤ ‖φ‖ := by
        rcases eq_or_lt_of_le hN0 with hN0' | hN0'
        · rw [← hN0']; exact norm_nonneg φ
        have hI : I = N ^ (q.toReal - 1) * N := by
          rw [← Real.rpow_add_one hN0'.ne', sub_add_cancel, hN_def, Real.rpow_inv_rpow hI0 hqr0]
        have hpos : 0 < N ^ (q.toReal - 1) := Real.rpow_pos_of_pos hN0' _
        rw [hI, mul_comm] at hIle
        exact le_of_mul_le_mul_right hIle hpos
      rw [hN]
      exact ENNReal.ofReal_le_ofReal hNle
    -- pass to the limit `n → ∞`
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (u₀ x)) := ae_of_all _ fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖u₀ x‖⌉₊] with n hn
      change u₀ x = {x | ‖u₀ x‖ ≤ n}.indicator u₀ x
      rw [Set.indicator_of_mem]
      change ‖u₀ x‖ ≤ (n : ℝ)
      exact (Nat.le_ceil ‖u₀ x‖).trans (Nat.cast_le.2 hn)
    calc eLpNorm u₀ q μ ≤ atTop.liminf fun n => eLpNorm (v n) q μ :=
          eLpNorm_lim_le_liminf_eLpNorm hv_meas u₀ hu₀m.aestronglyMeasurable hlim
      _ ≤ ENNReal.ofReal ‖φ‖ := liminf_le_of_frequently_le' (Frequently.of_forall hkey)

/-- **The Riesz representation theorem on a finite measure**, for real scalars. Let $\mu$ be a
finite measure, and let $1 \le p < \infty$ and $q$ be conjugate exponents. For every continuous
linear functional $\varphi$ on $L^p(\mu; \mathbb{R})$ there is $u \in L^q(\mu; \mathbb{R})$ with
$$\varphi(f) = \int u f \, d\mu \quad \text{for every } f \in L^p(\mu).$$
This is Theorems 4.11 and 4.14 of [brezis2011functional] for a finite measure. -/
theorem exists_forall_eq_integral_of_isFiniteMeasure [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ u : Lp ℝ q μ, ∀ f : Lp ℝ p μ, φ f = ∫ x, u x * f x ∂μ := by
  set u₀ := (dualToSignedMeasure hp φ).rnDeriv μ with hu₀_def
  have hu : MemLp u₀ q μ :=
    (eLpNorm_rnDeriv_dualToSignedMeasure_le hp φ).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hu.toLp u₀, ?_⟩
  suffices h : φ = toDualCLM ℝ p q μ (hu.toLp u₀) by
    intro f
    rw [h, toDualCLM_apply]
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.induction hp (fun f : Lp ℝ p μ => φ f = toDualCLM ℝ p q μ (hu.toLp u₀) f) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, toDualCLM_apply,
      apply_eq_integral_rnDeriv_mul_of_ae_bound hp φ _ (C := ‖c‖)
        (indicatorConstLp_coeFn.mono fun x hx => by rw [hx]; exact norm_indicator_le_norm_self _ _)]
    exact integral_congr_ae (hu.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx])
  · intro f g _ _ _ hf hg
    rw [map_add, map_add, hf, hg]
  · exact isClosed_eq φ.continuous (toDualCLM ℝ p q μ _).continuous

end Lp

/-! ### The $\sigma$-finite case, by a weight -/

/-- Let $\rho \colon \alpha \to [0, \infty)$ be measurable with $\rho(x) > 0$ for every $x$. Then
$\mu$ is absolutely continuous with respect to the measure $\rho \mu$ with density $\rho$. -/
theorem absolutelyContinuous_withDensity_of_pos {ρ : α → ℝ≥0} (hρ : Measurable ρ)
    (h0 : ∀ x, 0 < ρ x) : μ ≪ μ.withDensity fun x => (ρ x : ℝ≥0∞) := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hνs => ?_
  rw [withDensity_apply_eq_zero (by fun_prop)] at hνs
  have : {x | (ρ x : ℝ≥0∞) ≠ 0} ∩ s = s :=
    Set.inter_eq_right.2 fun x _ => by simpa using (h0 x).ne'
  rwa [this] at hνs

/-- Let $\rho \colon \alpha \to [0, \infty)$ and $h \colon \alpha \to \mathbb{R}$ be measurable,
with $h \ge 0$, let $0 < r < \infty$ with $h^r = \rho$, and let $g \colon \alpha \to \mathbb{R}$
be almost everywhere strongly measurable for $\mu$. Then
$$\|h g\|_{L^r(\mu)} = \|g\|_{L^r(\rho \mu)}.$$
So multiplication by $h$ is an isometry from $L^r(\rho \mu)$ to $L^r(\mu)$. -/
theorem eLpNorm_mul_withDensity {ρ : α → ℝ≥0} (hρ : Measurable ρ) {h : α → ℝ} (hh : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) {r : ℝ≥0∞} (hr0 : r ≠ 0) (hr : r ≠ ∞) (hhr : ∀ x, h x ^ r.toReal = ρ x)
    {g : α → ℝ} (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => h x * g x) r μ = eLpNorm g r (μ.withDensity fun x => (ρ x : ℝ≥0∞)) := by
  have hνμ : μ.withDensity (fun x => (ρ x : ℝ≥0∞)) ≪ μ := withDensity_absolutelyContinuous μ _
  have hhg : AEStronglyMeasurable (fun x => h x * g x) μ := hh.aestronglyMeasurable.mul hg
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr hhg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr (hg.mono_ac hνμ),
    lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (hg.enorm.pow_const _)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
    Real.enorm_eq_ofReal (hh0 x)]
  rw [ENNReal.ofReal_rpow_of_nonneg (hh0 x) ENNReal.toReal_nonneg, hhr x,
    ENNReal.ofReal_coe_nnreal]

/-- If two measures $\mu$ and $\nu$ have the same null sets, then every function
$f \colon \alpha \to \mathbb{K}$ has the same essential supremum of $|f|$ for $\mu$ and for
$\nu$. -/
theorem eLpNormEssSup_congr_ae_measure {ν : Measure α} (h : ae μ = ae ν) (f : α → 𝕜) :
    eLpNormEssSup f μ = eLpNormEssSup f ν := by
  simp only [eLpNormEssSup, essSup, h]

namespace Lp

/-- **The Riesz representation theorem on a $\sigma$-finite measure**, for real scalars. Let $\mu$
be a $\sigma$-finite measure, and let $1 \le p < \infty$ and $q$ be conjugate exponents. For
every continuous linear functional $\varphi$ on $L^p(\mu; \mathbb{R})$ there is
$u \in L^q(\mu; \mathbb{R})$ with
$$\varphi(f) = \int u f \, d\mu \quad \text{for every } f \in L^p(\mu).$$
This is Theorems 4.11 and 4.14 of [brezis2011functional].

The proof reduces to the finite measure $\theta^p \mu$ by a weight $\theta \in L^p$ with
$0 < \theta \le 1$. Multiplication by $\theta$ is an isometry of $L^p(\theta^p \mu)$ onto
$L^p(\mu)$. The representative of $g \mapsto \varphi(\theta g)$ on $\theta^p \mu$, multiplied by
$\theta^{p - 1}$, represents $\varphi$. -/
theorem exists_forall_eq_integral [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ u : Lp ℝ q μ, ∀ f : Lp ℝ p μ, φ f = ∫ x, u x * f x ∂μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- the weight `θ = ρ ^ (1/p)`, `0 < ρ ≤ 1` integrable
  obtain ⟨w, hw0, hwm, hwint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  set ρ : α → ℝ≥0 := fun x => min (w x) 1 with hρ_def
  have hρm : Measurable ρ := hwm.min measurable_const
  have hρ0 : ∀ x, 0 < ρ x := fun x => lt_min (hw0 x) one_pos
  set θ : α → ℝ := fun x => (ρ x : ℝ) ^ p.toReal⁻¹ with hθ_def
  have hθm : Measurable θ := (measurable_coe_nnreal_real.comp hρm).pow_const _
  have hθ0 : ∀ x, 0 < θ x := fun x => Real.rpow_pos_of_pos (NNReal.coe_pos.2 (hρ0 x)) _
  have hθp : ∀ x, θ x ^ p.toReal = ρ x := fun x => Real.rpow_inv_rpow (ρ x).coe_nonneg hpr.ne'
  set ν := μ.withDensity fun x => (ρ x : ℝ≥0∞) with hν_def
  have hνfin : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity (ne_top_of_le_ne_top (hwint.trans_le le_top).ne
      (lintegral_mono fun x => ENNReal.coe_le_coe.2 (min_le_left (w x) 1)))
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous μ _
  have hμν : μ ≪ ν := absolutelyContinuous_withDensity_of_pos hρm hρ0
  have hae : ae μ = ae ν := le_antisymm hμν.ae_le hνμ.ae_le
  -- multiplication by `θ`, an isometry `L^p(ν) → L^p(μ)`
  have hmul : ∀ g : Lp ℝ p ν, MemLp (fun x => θ x * g x) p μ := fun g =>
    memLp_iff.2 ((eLpNorm_mul_withDensity hρm hθm (fun x => (hθ0 x).le) hp0 hp hθp
      ((Lp.aestronglyMeasurable g).mono_ac hμν)).trans_lt (Lp.eLpNorm_lt_top g))
  let Φ : Lp ℝ p ν →L[ℝ] Lp ℝ p μ := LinearMap.mkContinuous
    { toFun := fun g => (hmul g).toLp _
      map_add' := fun g₁ g₂ => by
        apply Lp.ext
        filter_upwards [(hmul (g₁ + g₂)).coeFn_toLp, (hmul g₁).coeFn_toLp, (hmul g₂).coeFn_toLp,
          Lp.coeFn_add ((hmul g₁).toLp _) ((hmul g₂).toLp _), hμν.ae_eq (Lp.coeFn_add g₁ g₂)]
          with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply, mul_add]
      map_smul' := fun c g => by
        apply Lp.ext
        filter_upwards [(hmul (c • g)).coeFn_toLp, (hmul g).coeFn_toLp,
          Lp.coeFn_smul c ((hmul g).toLp _), hμν.ae_eq (Lp.coeFn_smul c g)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul, mul_left_comm] }
    1 fun g => by
      rw [one_mul, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def,
        eLpNorm_mul_withDensity hρm hθm (fun x => (hθ0 x).le) hp0 hp hθp
          ((Lp.aestronglyMeasurable g).mono_ac hμν)]
  have hΦ : ∀ g : Lp ℝ p ν, ⇑(Φ g) =ᵐ[μ] fun x => θ x * g x := fun g => (hmul g).coeFn_toLp
  -- the representative of `g ↦ φ (θ g)` on the finite measure `ν`
  obtain ⟨v, hv⟩ := exists_forall_eq_integral_of_isFiniteMeasure (μ := ν) (q := q) hp (φ.comp Φ)
  -- `u = θ ^ (p - 1) v` lies in `L^q(μ)`
  set u : α → ℝ := fun x => θ x ^ (p.toReal - 1) * v x with hu_def
  have hu : MemLp u q μ := by
    by_cases hq : q = ∞
    · subst hq
      have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).1 rfl
      have hu_eq : u = v := by
        ext x
        simp only [hu_def, hp1, ENNReal.toReal_one, sub_self, Real.rpow_zero, one_mul]
      rw [memLp_iff, hu_eq, eLpNorm_exponent_top ((Lp.aestronglyMeasurable v).mono_ac hμν),
        eLpNormEssSup_congr_ae_measure hae, ← eLpNorm_exponent_top (Lp.aestronglyMeasurable v)]
      exact Lp.eLpNorm_lt_top v
    · have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
      refine memLp_iff.2 ((eLpNorm_mul_withDensity hρm (hθm.pow_const _)
        (fun x => by positivity) hq0 hq (fun x => ?_)
        ((Lp.aestronglyMeasurable v).mono_ac hμν)).trans_lt (Lp.eLpNorm_lt_top v))
      rw [← Real.rpow_mul (hθ0 x).le, hpq.sub_one_mul_conj, hθp]
  refine ⟨hu.toLp u, fun f => ?_⟩
  -- `f = θ g` with `g = f / θ ∈ L^p(ν)`
  have hg_meas : AEStronglyMeasurable (fun x => f x / θ x) μ := by
    simp_rw [div_eq_mul_inv]
    exact (Lp.aestronglyMeasurable f).mul hθm.inv.aestronglyMeasurable
  have hg : MemLp (fun x => f x / θ x) p ν := by
    rw [memLp_iff, ← eLpNorm_mul_withDensity hρm hθm (fun x => (hθ0 x).le) hp0 hp hθp hg_meas]
    refine (eLpNorm_congr_ae (ae_of_all _ fun x => ?_)).trans_lt (Lp.eLpNorm_lt_top f)
    exact mul_div_cancel₀ _ (hθ0 x).ne'
  have hΦg : Φ (hg.toLp _) = f := by
    apply Lp.ext
    filter_upwards [hΦ (hg.toLp _), hμν.ae_eq hg.coeFn_toLp] with x hx hx'
    rw [hx, hx']
    exact mul_div_cancel₀ _ (hθ0 x).ne'
  calc φ f = (φ.comp Φ) (hg.toLp _) := by rw [ContinuousLinearMap.comp_apply, hΦg]
    _ = ∫ x, v x * (hg.toLp _) x ∂ν := hv _
    _ = ∫ x, v x * (f x / θ x) ∂ν :=
        integral_congr_ae ((ae_eq_refl _).mul hg.coeFn_toLp)
    _ = ∫ x, ρ x • (v x * (f x / θ x)) ∂μ := integral_withDensity_eq_integral_smul hρm _
    _ = ∫ x, (hu.toLp u) x * f x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hu.coeFn_toLp] with x hx
        rw [hx]
        simp only [hu_def, NNReal.smul_def, smul_eq_mul]
        rw [← hθp x, Real.rpow_sub_one (hθ0 x).ne']
        field_simp

end Lp

/-! ### The pairing is an isometry -/

namespace Lp

/-- Let $p, q \in [1, \infty]$ be conjugate exponents with $q \neq \infty$, and let $\mu$ be any
measure. For $u \in L^q(\mu; \mathbb{K})$, the functional $f \mapsto \int u f \, d\mu$ on
$L^p(\mu)$ has norm $\|u\|_q$.

The inequality $\|u\|_q \le \|f \mapsto \int u f\|$ comes from the extremal test function
$|u|^{q - 2} \bar u$, as in Step 3 of the proof of Theorem 4.10 of [brezis2011functional]. -/
theorem norm_toDualCLM_apply_of_ne_top [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hq : q ≠ ∞) (u : Lp 𝕜 q μ) : ‖toDualCLM 𝕜 p q μ u‖ = ‖u‖ := by
  refine le_antisymm (norm_toDualCLM_apply_le u) ?_
  rcases eq_or_ne u 0 with rfl | hu0
  · simp
  have hq1 : 1 ≤ q := Fact.out
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  have hqr0 : q.toReal ≠ 0 := (ENNReal.toReal_pos hq0 hq).ne'
  have hqr1 : 1 ≤ q.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hq hq1
  -- the extremal function and its `L^p` norm
  set f₀ := extremal (⇑u) q.toReal with hf₀_def
  have hf₀m : AEStronglyMeasurable f₀ μ :=
    aestronglyMeasurable_extremal (Lp.aestronglyMeasurable u) _
  have hf₀ : eLpNorm f₀ p μ ≤ eLpNorm u q μ ^ (q.toReal - 1) := by
    rcases eq_or_lt_of_le hqr1 with h1 | h1
    · have hq1' : q = 1 := (ENNReal.toReal_eq_one_iff q).1 h1.symm
      have hp : p = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).2 hq1'
      rw [hp, ← h1, sub_self, ENNReal.rpow_zero, eLpNorm_exponent_top hf₀m, hf₀_def, ← h1]
      exact (eLpNormEssSup_le_of_ae_bound (ae_of_all _ (norm_extremal_one_le _))).trans
        (by simp)
    · have hp : p ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one p q).2 fun h => by
        rw [h, ENNReal.toReal_one] at h1; exact lt_irrefl _ h1
      have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
      have hpq' : p * ENNReal.ofReal (q.toReal - 1) = q := by
        rw [← ENNReal.ofReal_toReal hp, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_comm,
          hpq.symm.sub_one_mul_conj, ENNReal.ofReal_toReal hq]
      exact eLpNorm_extremal_le (Lp.aestronglyMeasurable u) h1 hpq'
  have hf₀mem : MemLp f₀ p μ :=
    hf₀.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by linarith) (Lp.eLpNorm_ne_top u))
  -- the pairing of `u` with its extremal function is `‖u‖ ^ q`
  have hpair : toDualCLM 𝕜 p q μ u (hf₀mem.toLp f₀) = ((‖u‖ ^ q.toReal : ℝ) : 𝕜) := by
    rw [toDualCLM_apply]
    calc ∫ x, u x * (hf₀mem.toLp f₀) x ∂μ = ∫ x, ((‖u x‖ ^ q.toReal : ℝ) : 𝕜) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hf₀mem.coeFn_toLp] with x hx
          rw [hx]
          exact mul_extremal (⇑u) hqr0 x
      _ = ((∫ x, ‖u x‖ ^ q.toReal ∂μ : ℝ) : 𝕜) := integral_ofReal
      _ = ((‖u‖ ^ q.toReal : ℝ) : 𝕜) := by
          congr 1
          rw [Lp.norm_def, (Lp.memLp u).eLpNorm_eq_integral_rpow_norm hq0 hq,
            ENNReal.toReal_ofReal (by positivity),
            Real.rpow_inv_rpow (integral_nonneg fun x => by positivity) hqr0]
  have hnorm_f₀ : ‖hf₀mem.toLp f₀‖ ≤ ‖u‖ ^ (q.toReal - 1) := by
    rw [Lp.norm_toLp, Lp.norm_def, ENNReal.toReal_rpow]
    exact ENNReal.toReal_mono
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (Lp.eLpNorm_ne_top u)) hf₀
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have key : ‖u‖ ^ (q.toReal - 1) * ‖u‖ ≤ ‖u‖ ^ (q.toReal - 1) * ‖toDualCLM 𝕜 p q μ u‖ := by
    calc ‖u‖ ^ (q.toReal - 1) * ‖u‖ = ‖u‖ ^ q.toReal := by
          rw [← Real.rpow_add_one hu_pos.ne', sub_add_cancel]
      _ = ‖toDualCLM 𝕜 p q μ u (hf₀mem.toLp f₀)‖ := by
          rw [hpair, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
      _ ≤ ‖toDualCLM 𝕜 p q μ u‖ * ‖hf₀mem.toLp f₀‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖toDualCLM 𝕜 p q μ u‖ * ‖u‖ ^ (q.toReal - 1) := by gcongr
      _ = ‖u‖ ^ (q.toReal - 1) * ‖toDualCLM 𝕜 p q μ u‖ := mul_comm _ _
  exact le_of_mul_le_mul_left key (Real.rpow_pos_of_pos hu_pos _)

/-- Let $\mu$ be a $\sigma$-finite measure and let $p, q \in [1, \infty]$ be conjugate exponents.
For $u \in L^q(\mu; \mathbb{K})$, the functional $f \mapsto \int u f \, d\mu$ on $L^p(\mu)$ has
norm $\|u\|_q$.

For $q = \infty$, the proof reads inequality (14) in the proof of Theorem 4.14 of
[brezis2011functional] backwards: the sets $\{|u| > \|f \mapsto \int u f\|\}$ are null. Without
$\sigma$-finiteness the statement can fail for $q = \infty$: for a measure that is infinite on
every nonempty measurable set, $L^1 = 0$. -/
theorem norm_toDualCLM_apply [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (u : Lp 𝕜 q μ) : ‖toDualCLM 𝕜 p q μ u‖ = ‖u‖ := by
  by_cases hq : q = ∞
  · subst hq
    have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).1 rfl
    refine le_antisymm (norm_toDualCLM_apply_le u) ?_
    rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable u)]
    refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (eLpNormEssSup_le_of_ae_bound
      (ae_norm_le_of_forall_setIntegral_norm_le (Lp.aestronglyMeasurable u)
        (fun A _ hAfin => Measure.integrableOn_of_bounded hAfin.ne
          (Lp.aestronglyMeasurable u).norm (ae_restrict_of_ae
            ((ae_norm_le_norm_top u).mono fun x hx => by rwa [norm_norm])))
        fun A hA hAfin => ?_))
    -- the test function `1_A · conj u / ‖u‖`
    set g : α → 𝕜 := A.indicator (extremal (⇑u) 1) with hg_def
    have hg_mem : MemLp g p μ := by
      rw [hp1, memLp_one_iff_integrable, hg_def, integrable_indicator_iff hA]
      exact Measure.integrableOn_of_bounded hAfin.ne
        (aestronglyMeasurable_extremal (Lp.aestronglyMeasurable u) 1)
        (ae_of_all _ (norm_extremal_one_le _))
    have h2 : toDualCLM 𝕜 p ∞ μ u (hg_mem.toLp g) = ((∫ x in A, ‖u x‖ ∂μ : ℝ) : 𝕜) := by
      rw [toDualCLM_apply, ← integral_indicator hA, ← integral_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [hg_mem.coeFn_toLp] with x hx
      rw [hx]
      by_cases hxA : x ∈ A
      · have := mul_extremal (⇑u) one_ne_zero x
        simp only [Real.rpow_one] at this
        simp only [hg_def, Set.indicator_of_mem hxA, this]
      · simp [hg_def, Set.indicator_of_notMem hxA]
    have h3 : ‖hg_mem.toLp g‖ ≤ μ.real A := by
      rw [Lp.norm_toLp, measureReal_def]
      refine ENNReal.toReal_mono hAfin.ne ?_
      rw [hg_def, eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet]
      refine (eLpNorm_le_of_ae_bound (C := 1)
        (aestronglyMeasurable_extremal (Lp.aestronglyMeasurable u) 1).restrict
        (ae_of_all _ fun x => norm_extremal_one_le _ x)).trans ?_
      rw [Measure.restrict_apply_univ, hp1, ENNReal.toReal_one, inv_one, ENNReal.rpow_one,
        ENNReal.ofReal_one, mul_one]
    calc ∫ x in A, ‖u x‖ ∂μ = ‖toDualCLM 𝕜 p ∞ μ u (hg_mem.toLp g)‖ := by
          rw [h2, RCLike.norm_ofReal, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      _ ≤ ‖toDualCLM 𝕜 p ∞ μ u‖ * ‖hg_mem.toLp g‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖toDualCLM 𝕜 p ∞ μ u‖ * μ.real A := by gcongr
  · exact norm_toDualCLM_apply_of_ne_top hq u

variable (𝕜 p q μ) in
/-- Let $\mu$ be a $\sigma$-finite measure and let $p, q \in [1, \infty]$ be conjugate exponents.
The pairing $u \mapsto (f \mapsto \int u f \, d\mu)$ is a linear isometry $L^q(\mu; \mathbb{K})
\to L^p(\mu; \mathbb{K})^*$. This is the map $T$ of Theorems 4.11 and 4.14 of
[brezis2011functional]. -/
def toDual [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] :
    Lp 𝕜 q μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 p μ) where
  toLinearMap := toDualCLM 𝕜 p q μ
  norm_map' := norm_toDualCLM_apply

/-- The continuous linear map that underlies `MeasureTheory.Lp.toDual` is
`MeasureTheory.Lp.toDualCLM`. -/
@[simp]
theorem coe_toDual [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (u : Lp 𝕜 q μ) : (toDual 𝕜 p q μ u : StrongDual 𝕜 (Lp 𝕜 p μ)) = toDualCLM 𝕜 p q μ u :=
  rfl

/-- For $u \in L^q(\mu)$ and $f \in L^p(\mu)$, the value of `MeasureTheory.Lp.toDual` at $u$ and $f$
is $\int u(x) f(x) \, d\mu(x)$. -/
theorem toDual_apply [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (u : Lp 𝕜 q μ) (f : Lp 𝕜 p μ) : toDual 𝕜 p q μ u f = ∫ x, u x * f x ∂μ :=
  toDualCLM_apply u f

end Lp

/-! ### Surjectivity, the identification $(L^p)^* = L^q$, and reflexivity -/

namespace Lp

variable [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- **The Riesz representation theorem.** Let $\mu$ be a $\sigma$-finite measure, and let
$1 \le p < \infty$ and $q$ be conjugate exponents. The pairing $L^q(\mu; \mathbb{K}) \to
L^p(\mu; \mathbb{K})^*$, $u \mapsto (f \mapsto \int u f \, d\mu)$, is onto. This is Theorem 4.11
of [brezis2011functional] for $1 < p < \infty$ and Theorem 4.14 for $p = 1$.

Since the pairing is an isometry (`MeasureTheory.Lp.toDual`), every continuous linear functional
$\varphi$ on $L^p$ is $f \mapsto \int u f \, d\mu$ for a unique $u \in L^q$, and
$\|u\|_q = \|\varphi\|$. The complex case follows from the real case
`MeasureTheory.Lp.exists_forall_eq_integral`, applied to the real and imaginary parts of
$\varphi$ on real functions. -/
theorem toDual_surjective (hp : p ≠ ∞) : Function.Surjective (toDual 𝕜 p q μ) := by
  intro φ
  -- real-valued functions inside `Lp 𝕜`, and the real and imaginary parts
  let oP : Lp ℝ p μ →L[ℝ] Lp 𝕜 p μ := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLpL p μ
  let oQ : Lp ℝ q μ →L[ℝ] Lp 𝕜 q μ := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLpL q μ
  let reP : Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ := (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).compLpL p μ
  let imP : Lp 𝕜 p μ →L[ℝ] Lp ℝ p μ := (RCLike.imCLM : 𝕜 →L[ℝ] ℝ).compLpL p μ
  have hoP : ∀ g : Lp ℝ p μ, ⇑(oP g) =ᵐ[μ] fun x => ((g x : ℝ) : 𝕜) := fun g =>
    ContinuousLinearMap.coeFn_compLpL _ _
  have hoQ : ∀ v : Lp ℝ q μ, ⇑(oQ v) =ᵐ[μ] fun x => ((v x : ℝ) : 𝕜) := fun v =>
    ContinuousLinearMap.coeFn_compLpL _ _
  have hreP : ∀ f : Lp 𝕜 p μ, ⇑(reP f) =ᵐ[μ] fun x => RCLike.re (f x) := fun f =>
    ContinuousLinearMap.coeFn_compLpL _ _
  have himP : ∀ f : Lp 𝕜 p μ, ⇑(imP f) =ᵐ[μ] fun x => RCLike.im (f x) := fun f =>
    ContinuousLinearMap.coeFn_compLpL _ _
  -- the real representatives of `re ∘ φ` and `im ∘ φ` on real-valued functions
  obtain ⟨uᵣ, huᵣ⟩ := exists_forall_eq_integral (μ := μ) (q := q) hp
    ((RCLike.reCLM : 𝕜 →L[ℝ] ℝ) ∘L (φ.restrictScalars ℝ) ∘L oP)
  obtain ⟨uᵢ, huᵢ⟩ := exists_forall_eq_integral (μ := μ) (q := q) hp
    ((RCLike.imCLM : 𝕜 →L[ℝ] ℝ) ∘L (φ.restrictScalars ℝ) ∘L oP)
  refine ⟨oQ uᵣ + (RCLike.I : 𝕜) • oQ uᵢ, ?_⟩
  have hint : ∀ v : Lp ℝ q μ, ∀ g : Lp ℝ p μ, Integrable (fun x => v x * g x) μ := fun v g =>
    memLp_one_iff_integrable.1
      ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1 (Lp.memLp v) (Lp.memLp g))
  -- agreement on real-valued functions
  have hA : ∀ g : Lp ℝ p μ,
      toDual 𝕜 p q μ (oQ uᵣ + (RCLike.I : 𝕜) • oQ uᵢ) (oP g) = φ (oP g) := by
    intro g
    have h1 := huᵣ g
    have h2 := huᵢ g
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      RCLike.reCLM_apply, RCLike.imCLM_apply] at h1 h2
    rw [toDual_apply, ← RCLike.re_add_im (φ (oP g)), h1, h2]
    calc ∫ x, (oQ uᵣ + (RCLike.I : 𝕜) • oQ uᵢ) x * (oP g) x ∂μ
        = ∫ x, (((uᵣ x * g x : ℝ) : 𝕜) + ((uᵢ x * g x : ℝ) : 𝕜) * RCLike.I) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hoP g, Lp.coeFn_add (oQ uᵣ) ((RCLike.I : 𝕜) • oQ uᵢ),
            Lp.coeFn_smul (RCLike.I : 𝕜) (oQ uᵢ), hoQ uᵣ, hoQ uᵢ] with x h1 h2 h3 h4 h5
          rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5, smul_eq_mul]
          push_cast
          ring
      _ = ((∫ x, uᵣ x * g x ∂μ : ℝ) : 𝕜) + ((∫ x, uᵢ x * g x ∂μ : ℝ) : 𝕜) * RCLike.I := by
          rw [integral_add (hint uᵣ g).ofReal ((hint uᵢ g).ofReal.mul_const _),
            integral_mul_const, integral_ofReal, integral_ofReal]
  -- every `f` is `re f + I • im f`
  refine ContinuousLinearMap.ext fun f => ?_
  have hf : f = oP (reP f) + (RCLike.I : 𝕜) • oP (imP f) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (oP (reP f)) ((RCLike.I : 𝕜) • oP (imP f)),
      Lp.coeFn_smul (RCLike.I : 𝕜) (oP (imP f)), hoP (reP f), hoP (imP f), hreP f, himP f]
      with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, h5, h6, smul_eq_mul, mul_comm,
      RCLike.re_add_im]
  rw [hf, (toDual 𝕜 p q μ _).map_add, (toDual 𝕜 p q μ _).map_smul, φ.map_add, φ.map_smul, hA, hA]

variable (𝕜 p q μ) in
/-- Let $\mu$ be a $\sigma$-finite measure, and let $1 \le p < \infty$ and $q$ be conjugate
exponents. The **identification $(L^p)^* = L^q$** is the pairing
$u \mapsto (f \mapsto \int u f \, d\mu)$ as a linear isometric equivalence $L^q(\mu; \mathbb{K})
\to L^p(\mu; \mathbb{K})^*$. This is Remarks 4 and 5 in Chapter 4 of [brezis2011functional]. -/
def dualEquiv (hp : p ≠ ∞) : Lp 𝕜 q μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 p μ) :=
  LinearIsometryEquiv.ofSurjective (toDual 𝕜 p q μ) (toDual_surjective hp)

/-- The continuous linear map that underlies `MeasureTheory.Lp.dualEquiv` is
`MeasureTheory.Lp.toDualCLM`. -/
@[simp]
theorem coe_dualEquiv (hp : p ≠ ∞) (u : Lp 𝕜 q μ) :
    (dualEquiv 𝕜 p q μ hp u : StrongDual 𝕜 (Lp 𝕜 p μ)) = toDualCLM 𝕜 p q μ u :=
  rfl

/-- For $u \in L^q(\mu)$ and $f \in L^p(\mu)$, the value of `MeasureTheory.Lp.dualEquiv` at $u$ and
$f$ is $\int u(x) f(x) \, d\mu(x)$. -/
theorem dualEquiv_apply (hp : p ≠ ∞) (u : Lp 𝕜 q μ) (f : Lp 𝕜 p μ) :
    dualEquiv 𝕜 p q μ hp u f = ∫ x, u x * f x ∂μ :=
  toDualCLM_apply u f

end Lp

/-- If $p \ge 1$, then the conjugate exponent `ENNReal.conjExponent p` of $p$ is at least $1$. The
result is a `Fact`, for use as a local instance in the pairing of $L^p$ with $L^{p'}$. -/
theorem _root_.ENNReal.fact_one_le_conjExponent [Fact (1 ≤ p)] :
    Fact (1 ≤ ENNReal.conjExponent p) :=
  ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩

namespace Lp

variable (𝕜) in
/-- **$L^p$ is reflexive for $1 < p < \infty$.** Let $\mu$ be a $\sigma$-finite measure and let
$1 < p < \infty$. Then $L^p(\mu; \mathbb{K})$ is reflexive. This is part of Theorem 4.10 of
[brezis2011functional].

The hypotheses are explicit arguments. The proof is a formal consequence of the two surjections
$L^q \to (L^p)^*$ and $L^p \to (L^q)^*$ of the Riesz representation theorem, and it does not use
uniform convexity. -/
theorem isReflexive_of_one_lt_of_ne_top [SigmaFinite μ] [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ∞) : NormedSpace.IsReflexive 𝕜 (Lp 𝕜 p μ) := by
  -- the conjugate exponent
  have hpq : p.HolderConjugate (1 - p⁻¹)⁻¹ := ENNReal.HolderConjugate.inv_one_sub_inv' hp1.le
  set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hq_def
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp1.ne'
  refine ⟨fun ξ => ?_⟩
  -- the functional `ξ ∘ toDual` on `L^q` is represented by some `h ∈ L^p`
  obtain ⟨h, hh⟩ := toDual_surjective (𝕜 := 𝕜) (p := q) (q := p) (μ := μ) hq
    (ξ ∘L (toDual 𝕜 p q μ).toContinuousLinearMap)
  refine ⟨h, ContinuousLinearMap.ext fun ψ => ?_⟩
  obtain ⟨v, rfl⟩ := toDual_surjective (𝕜 := 𝕜) (p := p) (q := q) (μ := μ) hp ψ
  have := congrArg (fun F => F v) hh
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap] at this
  rw [NormedSpace.dual_def, ← this, toDual_apply, toDual_apply]
  simp_rw [mul_comm]

/-- **$L^p$ is reflexive for $1 < p < \infty$**, for a $\sigma$-finite measure, as an instance under
the hypotheses `[Fact (1 < p)] [Fact (p ≠ ∞)]`. This is part of Theorem 4.10 of
[brezis2011functional]. -/
instance instIsReflexive [SigmaFinite μ] [Fact (1 < p)] [Fact (p ≠ ∞)] :
    NormedSpace.IsReflexive 𝕜 (Lp 𝕜 p μ) :=
  isReflexive_of_one_lt_of_ne_top 𝕜 Fact.out Fact.out

end Lp

/-! ### The dual of $L^\infty$ is strictly larger than $L^1$ -/

section Top

variable {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]

omit [OpensMeasurableSpace G] in
/-- Let $\mu$ be a measure on a topological space $G$, and let $x_0 \in G$ be a point such that
every neighbourhood of $x_0$ has positive measure. If a property $P$ holds $\mu$-almost
everywhere and the set where $P$ fails is open, then $P(x_0)$ holds. -/
theorem of_ae_of_isOpen_of_forall_mem_nhds_measure_pos {μ : Measure G} {x₀ : G}
    (hx₀ : ∀ U ∈ 𝓝 x₀, 0 < μ U) {P : G → Prop} (hP : IsOpen {x | ¬ P x})
    (h : ∀ᵐ x ∂μ, P x) : P x₀ := by
  by_contra hx
  exact (hx₀ _ (hP.mem_nhds hx)).ne' (ae_iff.1 h)

/-- Let $G$ be a topological space in which open sets are measurable, let $\nu$ be a measure on $G$
that is positive on nonempty open sets, and let $\Omega \subseteq G$ be open. If a property $P$
holds $\nu$-almost everywhere on $\Omega$ and the set where $P$ fails is open, then $P$ holds at
every point of $\Omega$. -/
theorem forall_of_ae_restrict_of_isOpen {ν : Measure G} [ν.IsOpenPosMeasure] {Ω : Set G}
    (hΩ : IsOpen Ω) {P : G → Prop} (hP : IsOpen {x | ¬ P x}) (h : ∀ᵐ x ∂ν.restrict Ω, P x) :
    ∀ x ∈ Ω, P x := by
  rw [ae_restrict_iff' hΩ.measurableSet, ae_iff] at h
  have hset : {x | ¬ (x ∈ Ω → P x)} = Ω ∩ {x | ¬ P x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, not_imp]
  rw [hset, (hΩ.inter hP).measure_eq_zero_iff ν] at h
  intro x hx
  by_contra hPx
  exact Set.eq_empty_iff_forall_notMem.1 h x ⟨hx, hPx⟩

end Top

namespace Lp

/-- Let $G$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, let $\mu$ be
a $\sigma$-finite measure on $G$ for which every singleton is null, and let $x_0 \in G$. Let
$\varphi$ be a continuous linear functional on $L^\infty(\mu; \mathbb{R})$ with
$\varphi(f) = f(x_0)$ for every smooth compactly supported $f \colon G \to \mathbb{R}$. Then
$\varphi$ is not of the form $f \mapsto \int u f \, d\mu$ for any $u \in L^1(\mu)$.

Such a $u$ would vanish almost everywhere outside $\{x_0\}$, by
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, and hence almost everywhere. But
$\varphi$ has the value $1$ at a bump function at $x_0$. -/
theorem toDual_ne_of_forall_contDiff_apply_eq {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [NullSingletonClass μ] [SigmaFinite μ] {x₀ : G} (φ : StrongDual ℝ (Lp ℝ ∞ μ))
    (hφ : ∀ (f : G → ℝ) (hf : MemLp f ∞ μ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      φ (hf.toLp f) = f x₀) (u : Lp ℝ 1 μ) : toDual ℝ ∞ 1 μ u ≠ φ := by
  intro hu
  have hmem : ∀ f : G → ℝ, Continuous f → HasCompactSupport f → MemLp f ∞ μ := fun f hf hs => by
    obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hs
    exact memLp_top_of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  -- a bump at `x₀`, on which `φ` is `1`
  let ψ : ContDiffBump x₀ := ⟨1, 2, one_pos, one_lt_two⟩
  have hψ : MemLp ψ ∞ μ := hmem ψ ψ.continuous ψ.hasCompactSupport
  have hφψ : φ (hψ.toLp ψ) = 1 := by
    rw [hφ ψ hψ ψ.contDiff ψ.hasCompactSupport]
    exact ψ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
  -- `u = 0` a.e. off `x₀`
  have hu0 : ∀ᵐ x ∂μ, x ∈ ({x₀}ᶜ : Set G) → u x = 0 := by
    have huint : Integrable u μ := memLp_one_iff_integrable.1 (Lp.memLp u)
    refine isClosed_singleton.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (huint.locallyIntegrable.locallyIntegrableOn _) fun g hg hgs hgΩ => ?_
    have hgL : MemLp g ∞ μ := hmem g hg.continuous hgs
    have h1 : φ (hgL.toLp g) = 0 := by
      rw [hφ g hgL hg hgs]
      exact image_eq_zero_of_notMem_tsupport fun h => (hgΩ h) rfl
    rw [← hu, toDual_apply] at h1
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [hgL.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul, mul_comm]
  -- hence `u = 0` and `φ = 0`, contradicting `φ ψ = 1`
  have hu' : u = 0 := by
    have hx₀' : ∀ᵐ x ∂μ, x ≠ x₀ := by
      rw [ae_iff]
      simp
    have huμ : ∀ᵐ x ∂μ, u x = 0 := by
      filter_upwards [hu0, hx₀'] with x hx hx'
      exact hx hx'
    apply Lp.ext
    filter_upwards [huμ, Lp.coeFn_zero ℝ 1 μ] with x hx hx0
    rw [hx0, hx]
    rfl
  rw [hu', map_zero] at hu
  rw [← hu] at hφψ
  simp at hφψ

/-- **A functional on $L^\infty$ that does not come from $L^1$**, the functional of the study of
$L^\infty$ in §4.3 of [brezis2011functional], in a general form. Let $G$ be a finite-dimensional
real normed space with its Borel $\sigma$-algebra, let $\mu$ be a $\sigma$-finite measure on $G$
for which every singleton is null, and let $x_0 \in G$ be a point such that every neighbourhood
of $x_0$ has positive measure. Then there is a continuous linear functional $\varphi$ on
$L^\infty(\mu; \mathbb{R})$ such that

* $\varphi(f) = f(x_0)$ for every continuous compactly supported $f \colon G \to \mathbb{R}$,
  and
* $\varphi$ is not of the form $f \mapsto \int u f \, d\mu$ for any $u \in L^1(\mu)$.

The functional $\varphi$ is a Hahn–Banach extension of the evaluation at $x_0$, which is bounded
by the norm of $L^\infty$ on the classes of continuous compactly supported functions. The second
property is `MeasureTheory.Lp.toDual_ne_of_forall_contDiff_apply_eq`. -/
theorem exists_strongDual_top_apply_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [NullSingletonClass μ] [SigmaFinite μ] {x₀ : G} (hx₀ : ∀ U ∈ 𝓝 x₀, 0 < μ U) :
    ∃ φ : StrongDual ℝ (Lp ℝ ∞ μ),
      (∀ (f : G → ℝ) (hf : MemLp f ∞ μ), Continuous f → HasCompactSupport f →
        φ (hf.toLp f) = f x₀) ∧
      ∀ u : Lp ℝ 1 μ, toDual ℝ ∞ 1 μ u ≠ φ := by
  -- continuous compactly supported functions lie in `L^∞`
  have hmem : ∀ f : G → ℝ, Continuous f → HasCompactSupport f → MemLp f ∞ μ := fun f hf hs => by
    obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hs
    exact memLp_top_of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  -- an a.e. property with an open exceptional set holds at `x₀`
  have hall : ∀ {P : G → Prop}, IsOpen {x | ¬ P x} → (∀ᵐ x ∂μ, P x) → P x₀ :=
    fun hP h => of_ae_of_isOpen_of_forall_mem_nhds_measure_pos hx₀ hP h
  -- the subspace of `L^∞` of classes of continuous compactly supported functions
  let M : Submodule ℝ (Lp ℝ ∞ μ) :=
    { carrier := {g | ∃ f : G → ℝ, Continuous f ∧ HasCompactSupport f ∧ ⇑g =ᵐ[μ] f}
      add_mem' := fun {g₁ g₂} ⟨f₁, hf₁, hs₁, h₁⟩ ⟨f₂, hf₂, hs₂, h₂⟩ =>
        ⟨f₁ + f₂, hf₁.add hf₂, hs₁.add hs₂, (Lp.coeFn_add g₁ g₂).trans (h₁.add h₂)⟩
      zero_mem' := ⟨0, continuous_zero, HasCompactSupport.zero, Lp.coeFn_zero ℝ ∞ μ⟩
      smul_mem' := fun c {g} ⟨f, hf, hs, h⟩ =>
        ⟨c • f, hf.const_smul c, hs.smul_left, (Lp.coeFn_smul c g).trans (h.const_smul c)⟩ }
  choose F hFc hFs hF using fun g : M => g.2
  have hFeq : ∀ (g : M) (f : G → ℝ), Continuous f → ⇑(g : Lp ℝ ∞ μ) =ᵐ[μ] f → F g x₀ = f x₀ :=
    fun g f hf hgf => hall (isOpen_ne_fun (hFc g) hf) ((hF g).symm.trans hgf)
  -- point evaluation at `x₀` on `M`, bounded by the `L^∞` norm
  let δ : M →ₗ[ℝ] ℝ :=
    { toFun := fun g => F g x₀
      map_add' := fun g₁ g₂ => hFeq (g₁ + g₂) (F g₁ + F g₂) ((hFc g₁).add (hFc g₂)) (by
        rw [Submodule.coe_add]
        exact (Lp.coeFn_add _ _).trans ((hF g₁).add (hF g₂)))
      map_smul' := fun c g => hFeq (c • g) (c • F g) ((hFc g).const_smul c) (by
        rw [Submodule.coe_smul]
        exact (Lp.coeFn_smul c _).trans ((hF g).const_smul c)) }
  have hδ : ∀ g : M, ‖δ g‖ ≤ 1 * ‖g‖ := fun g => by
    rw [one_mul]
    refine hall (P := fun x => ‖F g x‖ ≤ ‖g‖)
      (by simp only [not_le]; exact isOpen_lt continuous_const (hFc g).norm) ?_
    filter_upwards [hF g, ae_norm_le_norm_top (g : Lp ℝ ∞ μ)] with x hx hx'
    rw [← hx]
    exact hx'
  obtain ⟨φ, hφM, -⟩ := exists_extension_norm_eq M (δ.mkContinuous 1 hδ)
  have hφeval : ∀ (f : G → ℝ) (hf : MemLp f ∞ μ), Continuous f → HasCompactSupport f →
      φ (hf.toLp f) = f x₀ := fun f hf hfc hfs => by
    have hfM : hf.toLp f ∈ M := ⟨f, hfc, hfs, hf.coeFn_toLp⟩
    rw [hφM ⟨_, hfM⟩]
    exact hFeq ⟨_, hfM⟩ f hfc hf.coeFn_toLp
  exact ⟨φ, hφeval, fun u => toDual_ne_of_forall_contDiff_apply_eq φ
    (fun f hf hfc hfs => hφeval f hf hfc.continuous hfs) u⟩

/-- **The dual of $L^\infty$ is strictly larger than $L^1$.** Let $G$ be a finite-dimensional real
normed space with its Borel $\sigma$-algebra, let $\nu$ be a $\sigma$-finite measure on $G$ that
is positive on nonempty open sets and for which every singleton is null, for example the
Lebesgue measure, or any Haar measure on a nontrivial $G$. Let $\Omega \subseteq G$ be a
nonempty open set. Then the pairing $L^1(\Omega) \to L^\infty(\Omega)^*$ is not onto. This is
the study of $L^\infty$ in §4.3 of [brezis2011functional].

The spaces are for the restricted measure `ν.restrict Ω`. The proof applies
`MeasureTheory.Lp.exists_strongDual_top_apply_eq` to this measure at a point $x_0 \in \Omega$.
Every neighbourhood of $x_0$ meets $\Omega$ in a nonempty open set. -/
theorem not_surjective_toDual_top {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G)
    [ν.IsOpenPosMeasure] [NullSingletonClass ν] [SigmaFinite ν] {Ω : Set G} (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) : ¬ Function.Surjective (toDual ℝ ∞ 1 (ν.restrict Ω)) := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨φ, -, hφ⟩ := exists_strongDual_top_apply_eq (ν.restrict Ω) (x₀ := x₀) fun U hU => by
    rw [Measure.restrict_apply' hΩ.measurableSet]
    exact Measure.measure_pos_of_mem_nhds ν (inter_mem hU (hΩ.mem_nhds hx₀))
  exact fun hsurj => let ⟨u, hu⟩ := hsurj φ; hφ u hu

end Lp

/-- **The pairing of $L^p$ and $L^q$ is jointly continuous.** Let $\mu$ be a measure and let
$p, q \in [1, \infty]$ be conjugate exponents. The map
$$L^p(\mu; \mathbb{R}) \times L^q(\mu; \mathbb{R}) \to \mathbb{R}, \qquad (f, g) \mapsto \int f
  g \, d\mu,$$
is continuous.

The proof is Hölder's inequality, through Mathlib's `ContinuousLinearMap.lpPairing` in the form
`MeasureTheory.Lp.toDualCLM`. -/
theorem continuous_integral_mul_prod {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] :
    Continuous fun x : Lp ℝ p μ × Lp ℝ q μ ↦ ∫ y, x.1 y * x.2 y ∂μ :=
  (Lp.toDualCLM ℝ q p μ).continuous₂.congr fun x ↦ Lp.toDualCLM_apply x.1 x.2

/-- **Hölder's inequality** in the form needed for powers of a norm. Let $1 \le p < \infty$, let $G$
and $G'$ be normed groups, and let $f \colon X \to G$ and $g \colon X \to G'$ be in $L^p(\mu)$.
Then
$$\int \|f\|^{p - 1} \|g\| \, d\mu \le \|f\|_p^{p - 1} \, \|g\|_p.$$
For $p = 1$ both sides are $\|g\|_1$. -/
theorem integral_norm_rpow_sub_one_mul_norm_le {X G G' : Type*}
    [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup G] [NormedAddCommGroup G']
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {f : X → G} {g : X → G'} (hf : MemLp f p μ)
    (hg : MemLp g p μ) :
    ∫ x, ‖f x‖ ^ (p.toReal - 1) * ‖g x‖ ∂μ
      ≤ (eLpNorm f p μ).toReal ^ (p.toReal - 1) * (eLpNorm g p μ).toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hP0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hfP := hf.eLpNorm_eq_integral_rpow_norm hp0 hp
  have hgP := hg.eLpNorm_eq_integral_rpow_norm hp0 hp
  rw [hfP, hgP, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rcases (Fact.out : (1 : ℝ≥0∞) ≤ p).eq_or_lt with h1 | h1
  · -- `p = 1`: both sides are `∫ ‖g‖`
    subst h1
    simp only [ENNReal.toReal_one, sub_self, Real.rpow_zero, one_mul, inv_one, Real.rpow_one]
    exact le_rfl
  · -- `1 < p`: Hölder with the exponents `p/(p−1)` and `p`
    have hP1 : 1 < p.toReal := by
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 h1
    have hP1' : 0 < p.toReal - 1 := by linarith
    have hconj : (Real.conjExponent p.toReal).HolderConjugate p.toReal :=
      (Real.HolderConjugate.conjExponent hP1).symm
    have hq : Real.conjExponent p.toReal = p.toReal / (p.toReal - 1) := rfl
    have hfq : MemLp (fun x ↦ ‖f x‖ ^ (p.toReal - 1))
        (ENNReal.ofReal (Real.conjExponent p.toReal)) μ := by
      have h := hf.norm_rpow_div (ENNReal.ofReal (p.toReal - 1))
      rw [ENNReal.toReal_ofReal hP1'.le] at h
      convert h using 1
      rw [hq, ENNReal.ofReal_div_of_pos hP1', ENNReal.ofReal_toReal hp]
    have hgq : MemLp (fun x ↦ ‖g x‖) (ENNReal.ofReal p.toReal) μ := by
      rw [ENNReal.ofReal_toReal hp]
      exact hg.norm
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
      (.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) (.of_forall fun x ↦ norm_nonneg _)
      hfq hgq
    refine hH.trans (le_of_eq ?_)
    have e1 : ∀ x, (‖f x‖ ^ (p.toReal - 1)) ^ Real.conjExponent p.toReal = ‖f x‖ ^ p.toReal := by
      intro x
      rw [← Real.rpow_mul (norm_nonneg _), hq, mul_div_cancel₀ _ hP1'.ne']
    simp_rw [e1]
    rw [← Real.rpow_mul (integral_nonneg fun x ↦ by positivity), one_div, one_div, hq, inv_div,
      inv_mul_eq_div]

end MeasureTheory
