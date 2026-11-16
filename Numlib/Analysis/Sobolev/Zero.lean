/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Cutoff.lean` and `Numlib/Analysis/Sobolev/Calculus.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Lp.PiLpDual
import Numlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.Analysis.Sobolev.Calculus
import Numlib.Analysis.Sobolev.Embedding
import Numlib.Analysis.Sobolev.Extension
import Numlib.Analysis.Sobolev.Poincare
import Numlib.Analysis.Sobolev.RemovableSingularity
import Numlib.MeasureTheory.Function.LpSpace.Convergence

/-!
# The Sobolev space $W_0^{1,p}(\Omega)$

Let $\Omega$ be an open subset of $\mathbb{R}^N$, or more generally of a finite-dimensional real
normed space $E$ with an additive Haar measure $\mu$ and a basis $(b_i)_{i \in \iota}$, and let
$1 \le p \le \infty$. The space $W_0^{1,p}(\Omega)$ is the closure of the test functions in
$W^{1,p}(\Omega)$. This module proves the properties and characterizations of $W_0^{1,p}(\Omega)$ in
§9.4 of [brezis2011functional]. The extension by zero $\bar u$ of $u \in W_0^{1,p}(\Omega)$ lies in
$W^{1,p}$ of the whole space, with $\partial_i \bar u = \overline{\partial_i u}$, on every open set
(Proposition 9.18, (i) ⇒ (iii)). It is an isometric extension operator, so the Sobolev inequality
holds on $W_0^{1,p}(\Omega)$ for every open $\Omega$, and Poincaré's inequality holds when $\Omega$
has finite measure (Remarks 20 and 21). On an open set of class $C^1$ and for $p < \infty$, a
function of $W^{1,p}(\Omega)$ that is continuous on $\bar\Omega$ lies in $W_0^{1,p}(\Omega)$ if and
only if it vanishes on $\partial\Omega$ (Theorem 9.17), and a function lies in $W_0^{1,p}(\Omega)$
if and only if its extension by zero lies in $W^{1,p}(\mathbb{R}^N)$ (Proposition 9.18). Further
results are the stability of $W_0^{1,p}(\Omega)$ under $u \mapsto G(u)$ and $u \mapsto u^+$, the
equalities $W_0^{1,p} = W^{1,p}$ on $\mathbb{R}^N$ and on $\mathbb{R}^N \setminus \{0\}$ (Remark
17), the representation of the dual $W^{-1,p'}(\Omega)$ (Proposition 9.20), and the dense inclusions
$H_0^1(\Omega) \subset L^2(\Omega) \subset H^{-1}(\Omega)$.

Below, $\bar u = \mathbf{1}_\Omega u$ is the extension of $u$ by zero outside $\Omega$, and
$\partial_i$ is the weak derivative along $b_i$ (along the standard basis vector $e_i$ on
$\mathbb{R}^N$). The norm of $W^{1,p}(\Omega)$ is the $\ell^p$ sum of the $L^p(\Omega)$ norms of $u$
and of the $\partial_i u$, and $\|\nabla u\|_{L^p(\Omega)}$ is the $\ell^p$ sum of the $L^p(\Omega)$
norms of the $\partial_i u$. For $N = d + 1$, $Q = \{(x', x_N) : |x'| < 1, |x_N| < 1\}$ is the unit
cylinder, $Q_+ = Q \cap \{x_N > 0\}$ and $Q_0 = Q \cap \{x_N = 0\}$. For $1 \le p < N$, the Sobolev
exponent $p^*$ is given by $1/p^* = 1/p - 1/N$.

## Main definitions

* `SobolevEuclideanZero.extendZeroL`: the extension by zero
  $W_0^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$, as a bounded linear map.
* `SobolevEuclideanZero.toDualL2`: the inclusion $L^2(\Omega) \to H^{-1}(\Omega)$,
  $f \mapsto (v \mapsto \int_\Omega f v)$.
* `SobolevEuclideanZero.toDualOfL2`: the inclusion $L^2(\Omega) \to W^{-1,p'}(\Omega)$ along a given
  bounded linear map $W_0^{1,p}(\Omega) \to L^2(\Omega)$.
* `pointCutoff`: the averaged cut-off $\eta_n(x) = (n+1)^{-1} \sum_{k \le n} \eta(3^k x)$ at the
  origin.

## Main results

* `SobolevMultiIndexZero.indicator_memSobolevMultiIndex`: for $u \in W_0^{1,p}(\Omega)$ on any open
  $\Omega \subseteq E$, the extension by zero $\bar u$ lies in $W^{1,p}(E)$, with
  $\partial_i \bar u = \overline{\partial_i u}$.
* `SobolevEuclideanZero.norm_extendZeroL_apply`: the extension by zero is an isometry
  $W_0^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$.
* `SobolevEuclideanZero.hasSobolevExtensionOn`: on every open $\Omega \subseteq \mathbb{R}^N$, the
  subspace $W_0^{1,p}(\Omega)$ has a Sobolev extension operator.
* `SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_eq`: the Sobolev inequality
  $\|u\|_{L^{p^*}(\Omega)} \le C \|\nabla u\|_{L^p(\Omega)}$ on $W_0^{1,p}(\Omega)$ for
  $1 \le p < N$ and every open $\Omega$.
* `SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_measure_ne_top`: Poincaré's inequality on
  $W_0^{1,p}(\Omega)$ for $N \ge 2$, $p < \infty$ and $\Omega$ of finite measure.
* `SobolevEuclideanZero.eq_top`: $W_0^{1,p}(\mathbb{R}^N) = W^{1,p}(\mathbb{R}^N)$ for $p < \infty$.
* `SobolevEuclidean.mem_zero_of_contDiff_hasCompactSupport`: for $p < \infty$, a $C^k$ function with
  compact support in $\Omega$ lies in $W_0^{k,p}(\Omega)$ (Remark 18).
* `SobolevEuclideanZero.abs_integral_fn_smul_fderiv_le`: for $u \in W_0^{1,p}(\Omega)$,
  $|\int_\Omega u \, \partial_i \varphi| \le \|\partial_i u\|_{L^p(\Omega)}
  \|\varphi\|_{L^{p'}(\Omega)}$ for every $\varphi \in C_c^1(\mathbb{R}^N)$.
* `SobolevEuclidean.indicator_memSobolev_of_forall_abs_integral_le`: for $1 < p \le \infty$, if
  $u \in L^p(\Omega)$ satisfies such a bound with some constant, then
  $\bar u \in W^{1,p}(\mathbb{R}^N)$.
* `SobolevEuclideanZero.mem_of_indicator_memSobolev`: on an open set of class $C^1$ and for
  $p < \infty$, a function whose extension by zero lies in $W^{1,p}(\mathbb{R}^N)$ lies in
  $W_0^{1,p}(\Omega)$.
* `SobolevMultiIndexZero.contDiff_comp_mem` and `SobolevEuclideanZero.posPart_mem`:
  $W_0^{1,p}(\Omega)$ is stable under $u \mapsto G \circ u$ for $G \in C^1$ with $G(0) = 0$ and
  bounded $G'$, and under $u \mapsto u^+$.
* `SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`: on any open $\Omega$, a
  function of $W^{1,p}(\Omega)$, $p < \infty$, that is continuous on $\bar\Omega$ and vanishes on
  $\partial\Omega$ lies in $W_0^{1,p}(\Omega)$.
* `SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure`: on an open set of class $C^1$, a
  function of $W_0^{1,p}(\Omega)$, $p < \infty$, that is continuous on $\bar\Omega$ vanishes on
  $\partial\Omega$.
* `SobolevMultiIndexZero.mem_of_mem_restrict`, `SobolevMultiIndexZero.mul_contDiff_mem` and
  `SobolevMultiIndexZero.compDiffeoL_mem`: membership in $W_0^{1,p}$ passes from an open subset,
  under a smooth compactly supported factor, and along a $C^1$ change of variables.
* `SobolevEuclideanZero.eq_top_of_compl_singleton`: $W_0^{1,p}(\mathbb{R}^N \setminus \{0\}) =
  W^{1,p}(\mathbb{R}^N \setminus \{0\})$ for $N \ge 2$ and $1 \le p \le N$.
* `SobolevEuclideanZero.exists_dual_repr`: for $p < \infty$, every continuous linear functional $F$
  on $W_0^{1,p}(\Omega)$ is $v \mapsto \int_\Omega f_0 v + \sum_i \int_\Omega f_i \partial_i v$ with
  $f_\alpha \in L^{p'}(\Omega)$ and $\|f_\alpha\|_{p'} \le \|F\|$.
* `SobolevEuclideanZero.exists_dual_repr_of_isBounded`: on a bounded $\Omega$ one can take
  $f_0 = 0$.
* `SobolevEuclideanZero.gelfandTriple`: the inclusions $H_0^1(\Omega) \subset L^2(\Omega) \subset
  H^{-1}(\Omega)$ are injective with dense range.
* `SobolevEuclideanZero.gelfandTriple_of_forall_ae_eq`: the same for $W_0^{1,p}(\Omega) \subset
  L^2(\Omega) \subset W^{-1,p'}(\Omega)$, $1 < p < \infty$, along any bounded inclusion
  $W_0^{1,p}(\Omega) \to L^2(\Omega)$.
* `SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero`: for $N \ge 1$ and $p < \infty$, an element of
  $W_0^{1,p}(\Omega)$ with vanishing gradient is zero.
* `SobolevEuclideanZero.mem_of_nonneg_of_le`: on an open set of class $C^1$ with bounded boundary,
  if $v \in H^1(\Omega)$ and $0 \le v \le w$ for some $w \in H_0^1(\Omega)$, then
  $v \in H_0^1(\Omega)$.

## Proof outline

The extension by zero does not use the Riesz representation, as the source does: the extensions by
zero of approximating test functions are test functions on the whole space, and the weak derivative
is closed under $L^p$ limits. For Theorem 9.17, (i) ⇒ (ii), the truncations $G(nu)/n$ are shown to
be a Cauchy sequence in $W^{1,p}(\Omega)$ whose gradients converge to
$\mathbf{1}_{\{u \neq 0\}} \nabla u$. The converse and Proposition 9.18, (iii) ⇒ (i), reduce by
local charts and a partition of unity to computations on $Q_+$: the strip inequality $\int_{\{x_N <
\varepsilon\}} |u| \le \varepsilon \int_{\{x_N < \varepsilon\}} |\partial_N u|$ on $W_0^{1,p}(Q_+)$,
and one-sided mollifiers. On the punctured space, a point has zero capacity for $p \le N$: the
gradients of the averaged cut-offs tend to $0$ in $L^p$.

## Implementation notes

* Statements about the predicate `MemSobolevMultiIndex` and about
  `SobolevMultiIndexZero F b k p Ω μ` are over a finite-dimensional real normed space $E$ with an
  additive Haar measure and an arbitrary basis $b$. Statements on $\mathbb{R}^N$ use
  `SobolevEuclideanZero N 1 p Ω`, which is `SobolevMultiIndexZero` for the standard basis and
  Lebesgue measure.
* The extension by zero follows the pattern of `Numlib.Analysis.Sobolev.Cutoff`: membership and the
  identities are proved for functions, and the element of the space is then obtained from
  `MemSobolevMultiIndex.exists_sobolevMultiIndex` and identified by
  `SobolevMultiIndex.ext_of_fn_ae_eq`.
* The bounded inclusion $W_0^{1,p}(\Omega) \to L^2(\Omega)$ of Remark 20 is in
  `Numlib.Analysis.Sobolev.EmbeddingDomain`, which imports this module. The Gelfand triple for
  general $p$ therefore takes the inclusion as a parameter, with the hypothesis
  `SobolevEuclideanZero.IsFnInclusion`.
* Poincaré's inequality on a set of finite measure is stated for $N \ge 2$. For $N = 1$ it is false
  on unbounded open sets of finite measure.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal NNReal Pointwise Topology

noncomputable section

/-! ### The weak derivative along a tuple is closed under $L^p$ limits -/

section Closed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {μ : Measure E}
  {p : ℝ≥0∞} {n : ℕ} {y : Fin n → E} {f w : E → F}

/-- Let $1 \le p \le \infty$, let $\Omega \subseteq E$ be open, and let $\mu$ be a measure on $E$
for which the constant $1$ is locally integrable on $\Omega$. Let $y$ be a tuple of directions.
Suppose that $u_i$ is a weak derivative of $g_i$ along $y$ on $\Omega$ for every
$i \in \mathbb{N}$, that $f$ and $w$ are locally integrable on $\Omega$, and that $g_i \to f$
and $u_i \to w$ in $L^p(\Omega)$. Then $w$ is a weak derivative of $f$ along $y$ on $\Omega$.

This is the form along one tuple of `hasWeakIteratedFDerivOn_of_tendsto_eLpNorm`, the closedness
clause of Remark 4 (i) in Chapter 9 of [brezis2011functional]. The proof is the same: by
Hölder's inequality, the pairing with a fixed test function is continuous on $L^p(\Omega)$. -/
theorem hasWeakIteratedLineDerivOn_of_tendsto_eLpNorm
    (hμ : LocallyIntegrableOn (fun _ : E ↦ (1 : ℝ)) Ω μ) (hp : 1 ≤ p) {g u : ℕ → E → F}
    (hg : ∀ i, HasWeakIteratedLineDerivOn y (g i) (u i) Ω μ)
    (hfl : LocallyIntegrableOn f Ω μ) (hwl : LocallyIntegrableOn w Ω μ)
    (h1 : Tendsto (fun i ↦ eLpNorm (g i - f) p (μ.restrict (Ω : Set E))) atTop (𝓝 0))
    (h2 : Tendsto (fun i ↦ eLpNorm (u i - w) p (μ.restrict (Ω : Set E))) atTop (𝓝 0)) :
    HasWeakIteratedLineDerivOn y f w Ω μ where
  locallyIntegrableOn := hfl
  locallyIntegrableOn_weakDeriv := hwl
  integral_smul_eq φ := by
    have : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
      ENNReal.HolderConjugate.conjExponent hp
    set q := ENNReal.conjExponent p with hq
    set a : 𝓓(Ω, ℝ) := φ.iteratedFDerivApply n y with hadef
    have haq : eLpNorm a q (μ.restrict (Ω : Set E)) ≠ ⊤ :=
      (a.memLp_restrict_of_locallyIntegrableOn_one hμ q).eLpNorm_ne_top
    have hφq : eLpNorm φ q (μ.restrict (Ω : Set E)) ≠ ⊤ :=
      (φ.memLp_restrict_of_locallyIntegrableOn_one hμ q).eLpNorm_ne_top
    -- the left-hand sides converge
    have hIg : ∀ i, IntegrableOn (fun x ↦ a x • g i x) (Ω : Set E) μ := fun i ↦
      ((hg i).integrable_smul a).integrableOn
    have hIf : IntegrableOn (fun x ↦ a x • f x) (Ω : Set E) μ :=
      (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hfl a.contDiff.continuous
        a.hasCompactSupport a.tsupport_subset).integrableOn
    have hA : Tendsto (fun i ↦ ∫ x in (Ω : Set E), a x • g i x ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), a x • f x ∂μ)) := by
      rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_enorm_tendsto_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (?_ : Tendsto (fun i ↦ eLpNorm a q (μ.restrict (Ω : Set E)) *
          eLpNorm (g i - f) p (μ.restrict (Ω : Set E))) atTop (𝓝 0))
        (fun _ ↦ zero_le) (fun i ↦ ?_)
      · simpa using ENNReal.Tendsto.const_mul h1 (Or.inr haq)
      · rw [← integral_sub (hIg i) hIf]
        have heq : (fun x ↦ a x • g i x - a x • f x) = fun x ↦ a x • (g i - f) x :=
          funext fun x ↦ by simp [smul_sub]
        rw [heq]
        exact enorm_integral_smul_le_eLpNorm_mul_eLpNorm (p := q) (q := p)
    -- the right-hand sides converge
    have hIu : ∀ i, IntegrableOn (fun x ↦ φ x • u i x) (Ω : Set E) μ := fun i ↦
      ((hg i).integrable_smul_weakDeriv φ).integrableOn
    have hIw : IntegrableOn (fun x ↦ φ x • w x) (Ω : Set E) μ :=
      (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hwl φ.contDiff.continuous
        φ.hasCompactSupport φ.tsupport_subset).integrableOn
    have hB : Tendsto (fun i ↦ ∫ x in (Ω : Set E), φ x • u i x ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), φ x • w x ∂μ)) := by
      rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_enorm_tendsto_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (?_ : Tendsto (fun i ↦ eLpNorm φ q (μ.restrict (Ω : Set E)) *
          eLpNorm (u i - w) p (μ.restrict (Ω : Set E))) atTop (𝓝 0))
        (fun _ ↦ zero_le) (fun i ↦ ?_)
      · simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hφq)
      · rw [← integral_sub (hIu i) hIw]
        have heq : (fun x ↦ φ x • u i x - φ x • w x) = fun x ↦ φ x • (u i - w) x :=
          funext fun x ↦ by simp [smul_sub]
        rw [heq]
        exact enorm_integral_smul_le_eLpNorm_mul_eLpNorm (p := q) (q := p)
    have hAB : ∀ i, (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • g i x ∂μ)
        = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • u i x ∂μ := fun i ↦
      (hg i).integral_smul_eq φ
    have hax : ∀ x, a x = iteratedFDeriv ℝ n (φ : E → ℝ) x y := fun _ ↦ rfl
    have hA' : Tendsto (fun i ↦ (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • u i x ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x ∂μ)) := by
      simpa only [hax, hAB] using hA
    exact tendsto_nhds_unique hA' (hB.const_smul ((-1 : ℝ) ^ n))

end Closed

/-!
### Dominated convergence in $L^p$, and convergence in $W^{1,p}(\Omega)$ component by component
-/

section Dominated

/-- **Dominated convergence in $L^p$.** Let $0 < p < \infty$, and let $f_n$, $g$ be almost
everywhere strongly measurable functions on a measure space with values in a normed group. If
$f_n \to g$ almost everywhere and $\|f_n\| \le h$ almost everywhere for every $n$, for a fixed
$h \in L^p$, then $\|f_n - g\|_{L^p} \to 0$.

The proof applies the dominated convergence theorem to the integrals $\int \|f_n - g\|^p$, which
are dominated by $(2h)^p$. -/
theorem MeasureTheory.tendsto_eLpNorm_sub_of_tendsto_ae {X G : Type*} [MeasurableSpace X]
    {ν : Measure X} [NormedAddCommGroup G] {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤)
    {f : ℕ → X → G} {g : X → G} {bound : X → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) ν) (hg : AEStronglyMeasurable g ν)
    (hbound : MemLp bound p ν) (hfb : ∀ n, ∀ᵐ x ∂ν, ‖f n x‖ ≤ bound x)
    (hfg : ∀ᵐ x ∂ν, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p ν) atTop (𝓝 0) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have hgb : ∀ᵐ x ∂ν, ‖g x‖ ≤ bound x := by
    filter_upwards [ae_all_iff.2 hfb, hfg] with x hx hlim
    exact le_of_tendsto hlim.norm (Eventually.of_forall hx)
  have hle : ∀ {a : G} {b : ℝ}, ‖a‖ ≤ b → ‖a‖ₑ ≤ ‖b‖ₑ := fun {a b} h ↦ by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (h.trans (Real.le_norm_self _))
  have hB : ∫⁻ x, (2 * ‖bound x‖ₑ) ^ p.toReal ∂ν ≠ ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp hp' hbound.eLpNorm_lt_top
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le (by simp))]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (by simp)) this.ne
  have key : Tendsto (fun n ↦ ∫⁻ x, ‖(f n - g) x‖ₑ ^ p.toReal ∂ν) atTop
      (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂ν)) := by
    refine tendsto_lintegral_of_dominated_convergence' _
      (fun n ↦ ((hf n).sub hg).enorm.pow_const _) (fun n ↦ ?_) hB ?_
    · filter_upwards [hfb n, hgb] with x hxn hxg
      refine ENNReal.rpow_le_rpow ?_ hp0.le
      calc ‖(f n - g) x‖ₑ = ‖f n x - g x‖ₑ := rfl
        _ ≤ ‖f n x‖ₑ + ‖g x‖ₑ := enorm_sub_le
        _ ≤ ‖bound x‖ₑ + ‖bound x‖ₑ := add_le_add (hle hxn) (hle hxg)
        _ = 2 * ‖bound x‖ₑ := (two_mul _).symm
    · filter_upwards [hfg] with x hx
      have h0 : Tendsto (fun n ↦ ‖(f n - g) x‖ₑ) atTop (𝓝 0) := by
        rw [← tendsto_sub_nhds_zero_iff] at hx
        exact tendsto_zero_iff_enorm_tendsto_zero.1 hx
      have := ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp h0
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp0] using this
  simp only [lintegral_zero] at key
  have := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp key
  simp only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.2 hp0)] at this
  refine this.congr fun n ↦ ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' ((hf n).sub hg)]

end Dominated

section Components

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- Let $u_n \to u$ in $W^{k,p}(\Omega)$. Then $\partial^\alpha u_n \to \partial^\alpha u$ in
$L^p(\Omega)$ for every multi-index $\alpha$ with $|\alpha| \le k$. -/
theorem tendsto_eLpNorm_weakDeriv_sub {w : ℕ → SobolevMultiIndex F b k p Ω μ}
    {u : SobolevMultiIndex F b k p Ω μ} (hw : Tendsto w atTop (𝓝 u)) (α : MultiIndexLE ι k) :
    Tendsto (fun n ↦ eLpNorm ((weakDeriv (w n) α : E → F) - (weakDeriv u α : E → F)) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
  have ht := ((weakDerivL F b k p Ω μ α).continuous.tendsto u).comp hw
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at ht
  simpa only [Function.comp_def, weakDerivL_apply] using ht

/-- Let $u_n \to u$ in $W^{k,p}(\Omega)$. Then $u_n \to u$ in $L^p(\Omega)$. -/
theorem tendsto_eLpNorm_fn_sub {w : ℕ → SobolevMultiIndex F b k p Ω μ}
    {u : SobolevMultiIndex F b k p Ω μ} (hw : Tendsto w atTop (𝓝 u)) :
    Tendsto (fun n ↦ eLpNorm (fn (w n) - fn u) p (μ.restrict (Ω : Set E))) atTop (𝓝 0) :=
  tendsto_eLpNorm_weakDeriv_sub hw 0

/-- **Convergence in $W^{k,p}(\Omega)$ from the convergence of the components.** Let
$u_n, u \in W^{k,p}(\Omega)$. If $\partial^\alpha u_n \to \partial^\alpha u$ in $L^p(\Omega)$
for every multi-index $\alpha$ with $|\alpha| \le k$, then $u_n \to u$ in $W^{k,p}(\Omega)$. -/
theorem tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub {w : ℕ → SobolevMultiIndex F b k p Ω μ}
    {u : SobolevMultiIndex F b k p Ω μ}
    (h : ∀ α : MultiIndexLE ι k, Tendsto (fun n ↦
      eLpNorm ((weakDeriv (w n) α : E → F) - (weakDeriv u α : E → F)) p (μ.restrict (Ω : Set E)))
        atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hα : ∀ α : MultiIndexLE ι k, Tendsto (fun n ↦ ‖weakDeriv (w n - u) α‖) atTop (𝓝 0) := by
    intro α
    have e : ∀ n, ‖weakDeriv (w n - u) α‖
        = (eLpNorm ((weakDeriv (w n) α : E → F) - (weakDeriv u α : E → F)) p
            (μ.restrict (Ω : Set E))).toReal := fun n ↦ by
      have e' : weakDeriv (w n - u) α = weakDeriv (w n) α - weakDeriv u α := rfl
      rw [Lp.norm_def, e']
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae (Lp.coeFn_sub _ _))
    simp_rw [e]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (h α)
    simpa [Function.comp_def] using this
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ norm_le_sum_norm_weakDeriv (w n - u)) ?_
  simpa using tendsto_finsetSum Finset.univ fun α _ ↦ hα α

end SobolevMultiIndex

end Components

/-! ### The extension by zero of a $W_0^{1,p}(\Omega)$ function -/

section ZeroExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndexZero

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- Let $u \in W^{k,p}(\Omega)$. Then the extension by zero $\mathbf{1}_\Omega u$ of its function
lies in $L^p(E)$. -/
theorem memLp_indicator_fn {k : ℕ} (u : SobolevMultiIndex F b k p Ω μ) :
    MemLp ((Ω : Set E).indicator (SobolevMultiIndex.fn u)) p μ :=
  (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).2
    (SobolevMultiIndex.memLp u)

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- Let $u \in W^{k,p}(\Omega)$ and let $\alpha$ be a multi-index with $|\alpha| \le k$. Then the
extension by zero $\mathbf{1}_\Omega \partial^\alpha u$ lies in $L^p(E)$. -/
theorem memLp_indicator_weakDeriv {k : ℕ} (u : SobolevMultiIndex F b k p Ω μ)
    (α : MultiIndexLE ι k) :
    MemLp ((Ω : Set E).indicator (SobolevMultiIndex.weakDeriv u α)) p μ :=
  (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).2 (Lp.memLp _)

omit [FiniteDimensional ℝ E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- Let $u \in W_0^{k,p}(\Omega)$. Then there are elements $w_n \in W^{k,p}(\Omega)$ and test
functions $\varphi_n$ on $\Omega$ such that the function of $w_n$ equals $\varphi_n$ almost
everywhere on $\Omega$ and $w_n \to u$ in $W^{k,p}(\Omega)$. -/
theorem exists_seq_testFunction_tendsto {k : ℕ} {u : SobolevMultiIndex F b k p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero F b k p Ω μ) :
    ∃ (w : ℕ → SobolevMultiIndex F b k p Ω μ) (φ : ℕ → 𝓓(Ω, F)),
      (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[μ.restrict (Ω : Set E)] φ n) ∧
        Tendsto w atTop (𝓝 u) := by
  have hmem : u ∈ closure (SobolevMultiIndex.testFunctions F b k p Ω μ : Set _) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hu
  obtain ⟨w, hwT, hw⟩ := mem_closure_iff_seq_limit.1 hmem
  choose φ hφ using hwT
  exact ⟨w, φ, hφ, hw⟩

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- Let $w \in W^{k,p}(\Omega)$, and let $\varphi$ be a test function on $\Omega$ that equals the
function of $w$ almost everywhere on $\Omega$. Then $\mathbf{1}_\Omega w = \varphi$ almost
everywhere on $E$. -/
theorem indicator_fn_ae_eq_testFunction {k : ℕ} {w : SobolevMultiIndex F b k p Ω μ}
    {φ : 𝓓(Ω, F)} (hφ : SobolevMultiIndex.fn w =ᵐ[μ.restrict (Ω : Set E)] φ) :
    (Ω : Set E).indicator (SobolevMultiIndex.fn w) =ᵐ[μ] φ := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1 hφ
  refine h.trans (Eventually.of_forall fun x ↦ ?_)
  exact congrFun (Set.indicator_eq_self.2 (Function.support_subset_iff'.2 fun x hx ↦
    φ.eq_zero_of_notMem hx)) x

omit [Fact (1 ≤ p)] in
/-- Let $w \in W^{1,p}(\Omega)$, and let $\varphi$ be a test function on $\Omega$ that equals the
function of $w$ almost everywhere on $\Omega$. Then $\partial_i w = D\varphi(x)\, b_i$ for
almost every $x \in \Omega$, for every $i$. -/
theorem weakDeriv_single_ae_eq_testFunction {w : SobolevMultiIndex F b 1 p Ω μ}
    {φ : 𝓓(Ω, F)} (hφ : SobolevMultiIndex.fn w =ᵐ[μ.restrict (Ω : Set E)] φ) (i : ι) :
    SobolevMultiIndex.weakDeriv w (MultiIndexLE.single i) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ fderiv ℝ φ x (b i) := by
  refine (SobolevMultiIndex.weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq w φ.contDiff hφ
    (MultiIndexLE.single i)).trans (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [MultiIndexLE.coe_single, φ.contDiff.iteratedFDeriv_congr_perm
    (multiIndexTuple_single_perm (b : ι → E) i) x, iteratedFDeriv_one_apply,
    Matrix.cons_val_zero]

omit [Fact (1 ≤ p)] in
/-- Let $w \in W^{1,p}(\Omega)$, and let $\varphi$ be a test function on $\Omega$ that equals the
function of $w$ almost everywhere on $\Omega$. Then $\mathbf{1}_\Omega \partial_i w =
D\varphi(x)\, b_i$ for almost every $x \in E$, for every $i$. -/
theorem indicator_weakDeriv_single_ae_eq_testFunction {w : SobolevMultiIndex F b 1 p Ω μ}
    {φ : 𝓓(Ω, F)} (hφ : SobolevMultiIndex.fn w =ᵐ[μ.restrict (Ω : Set E)] φ) (i : ι) :
    (Ω : Set E).indicator (SobolevMultiIndex.weakDeriv w (MultiIndexLE.single i))
      =ᵐ[μ] fun x ↦ fderiv ℝ φ x (b i) := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1
    (weakDeriv_single_ae_eq_testFunction hφ i)
  refine h.trans (Eventually.of_forall fun x ↦ ?_)
  exact congrFun (Set.indicator_eq_self.2 (Function.support_subset_iff'.2 fun x hx ↦
    (φ.fderivApply (b i)).eq_zero_of_notMem hx)) x

/-- **The extension by zero of a $W_0^{1,p}(\Omega)$ function has the extension by zero of its
partial derivative as weak derivative.** Let $\Omega \subseteq E$ be open, let
$1 \le p \le \infty$ and let $u \in W_0^{1,p}(\Omega)$. Then, for every $i$, the function
$\overline{\partial_i u} = \mathbf{1}_\Omega \partial_i u$ is a weak derivative of
$\bar u = \mathbf{1}_\Omega u$ along $b_i$ on the whole space $E$.

This is the identity $\partial \bar u / \partial x_i = \overline{\partial u / \partial x_i}$ of
Proposition 9.18 (iii) of [brezis2011functional], here for every open $\Omega$. The proof does
not use the Riesz representation, as the source does. Test functions $\varphi_n \to u$ in
$W^{1,p}(\Omega)$ are test functions on $E$ with classical derivative $\partial_i \varphi_n$.
Then $\varphi_n \to \bar u$ and $\partial_i \varphi_n \to \overline{\partial_i u}$ in $L^p(E)$,
and `hasWeakIteratedLineDerivOn_of_tendsto_eLpNorm` concludes. -/
theorem hasWeakIteratedLineDerivOn_indicator {u : SobolevMultiIndex F b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero F b 1 p Ω μ) (i : ι) :
    HasWeakIteratedLineDerivOn ![b i] ((Ω : Set E).indicator (SobolevMultiIndex.fn u))
      ((Ω : Set E).indicator (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i))) ⊤ μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨w, φ, hφ, hw⟩ := exists_seq_testFunction_tendsto hu
  have hμ : LocallyIntegrableOn (fun _ : E ↦ (1 : ℝ)) (⊤ : Opens E) μ :=
    (locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _
  -- convergence of the components, in `L^p(E)`
  have hconv : ∀ α : MultiIndexLE ι 1, Tendsto (fun n ↦ eLpNorm
      ((Ω : Set E).indicator (SobolevMultiIndex.weakDeriv (w n) α)
        - (Ω : Set E).indicator (SobolevMultiIndex.weakDeriv u α)) p μ) atTop (𝓝 0) := by
    intro α
    refine (SobolevMultiIndex.tendsto_eLpNorm_weakDeriv_sub hw α).congr fun n ↦ ?_
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet,
        ← Set.indicator_sub']
  refine hasWeakIteratedLineDerivOn_of_tendsto_eLpNorm hμ hp (g := fun n ↦ (φ n : E → F))
    (u := fun n x ↦ fderiv ℝ (φ n) x (b i)) (fun n ↦ ?_) ?_ ?_ ?_ ?_
  · have h := (ContDiffOn.hasWeakIteratedFDerivOn (Ω := ⊤) (μ := μ) (φ n).contDiff.contDiffOn
      (m := 1) (by simp)).lineDeriv ![b i]
    exact h.congr_ae (Filter.EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ by
      simp [iteratedFDeriv_one_apply])
  · exact ((memLp_indicator_fn u).locallyIntegrable hp).locallyIntegrableOn _
  · exact ((memLp_indicator_weakDeriv u _).locallyIntegrable hp).locallyIntegrableOn _
  · refine (hconv 0).congr fun n ↦ ?_
    simp only [Measure.restrict_coe_top]
    exact eLpNorm_congr_ae ((indicator_fn_ae_eq_testFunction (hφ n)).sub
      (Filter.EventuallyEq.refl _ _))
  · refine (hconv (MultiIndexLE.single i)).congr fun n ↦ ?_
    simp only [Measure.restrict_coe_top]
    exact eLpNorm_congr_ae ((indicator_weakDeriv_single_ae_eq_testFunction (hφ n) i).sub
      (Filter.EventuallyEq.refl _ _))

/-- Let $\Omega \subseteq E$ be open, let $1 \le p \le \infty$ and let $u \in W_0^{1,p}(\Omega)$.
Then the extension by zero $\bar u = \mathbf{1}_\Omega u$ lies in $W^{1,p}(E)$, with
$\partial_i \bar u = \overline{\partial_i u}$
(`SobolevMultiIndexZero.hasWeakIteratedLineDerivOn_indicator`). This is Proposition 9.18, (i) ⇒
(iii), of [brezis2011functional], together with Remark 20: "the canonical extension by 0 outside
$\Omega$, which is valid for arbitrary domains".

The conclusion is the predicate `MemSobolevMultiIndex` on the whole space `⊤`. -/
theorem indicator_memSobolevMultiIndex {u : SobolevMultiIndex F b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero F b 1 p Ω μ) :
    MemSobolevMultiIndex b ((Ω : Set E).indicator (SobolevMultiIndex.fn u)) 1 p ⊤ μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  refine ⟨by simpa only [Measure.restrict_coe_top] using memLp_indicator_fn u, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      (((memLp_indicator_fn u).locallyIntegrable hp).locallyIntegrableOn _),
      by simpa only [Measure.restrict_coe_top] using memLp_indicator_fn u⟩
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    exact ⟨_, (hasWeakIteratedLineDerivOn_indicator hu i).of_perm
      (multiIndexTuple_single_perm (b : ι → E) i).symm,
      by simpa only [Measure.restrict_coe_top] using memLp_indicator_weakDeriv u _⟩

end SobolevMultiIndexZero

end ZeroExtension


/-! ### The extension by zero $W_0^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ -/

section Typed

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

namespace SobolevEuclideanZero

/-- The **extension by zero** of $u \in W_0^{1,p}(\Omega)$, for an open
$\Omega \subseteq \mathbb{R}^N$: the element $\bar u$ of $W^{1,p}(\mathbb{R}^N)$ whose function
is $\mathbf{1}_\Omega u$.

It exists by `SobolevMultiIndexZero.indicator_memSobolevMultiIndex`, and it is chosen with
`Exists.choose`. -/
def extendZero (u : SobolevEuclideanZero N 1 p Ω) : SobolevEuclidean N 1 p ⊤ :=
  (SobolevMultiIndexZero.indicator_memSobolevMultiIndex u.2).exists_sobolevMultiIndex.choose

/-- For $u \in W_0^{1,p}(\Omega)$, the function of the extension by zero $\bar u$ equals
$\mathbf{1}_\Omega u$ almost everywhere on $\mathbb{R}^N$. -/
theorem fn_extendZero (u : SobolevEuclideanZero N 1 p Ω) :
    SobolevMultiIndex.fn (extendZero u) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) := by
  have h : SobolevMultiIndex.fn (extendZero u)
      =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _)]
        (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
          (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) :=
    (SobolevMultiIndexZero.indicator_memSobolevMultiIndex u.2).exists_sobolevMultiIndex.choose_spec
  simpa only [Measure.restrict_coe_top] using h

/-- For $u \in W_0^{1,p}(\Omega)$, the function of the extension by zero $\bar u$ equals the
function of $u$ almost everywhere on $\Omega$. -/
theorem fn_extendZero_restrict (u : SobolevEuclideanZero N 1 p Ω) :
    SobolevMultiIndex.fn (extendZero u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) :=
  Filter.EventuallyEq.trans (ae_restrict_of_ae (fn_extendZero u))
    (indicator_ae_eq_restrict Ω.isOpen.measurableSet.nullMeasurableSet)

/-- For $u \in W_0^{1,p}(\Omega)$ and every $i$, the partial derivative of the extension by zero is
the extension by zero of the partial derivative: $\partial_i \bar u = \mathbf{1}_\Omega
\partial_i u$ almost everywhere on $\mathbb{R}^N$. This is the identity of Proposition 9.18
(iii) of [brezis2011functional]. -/
theorem weakDeriv_extendZero_single (u : SobolevEuclideanZero N 1 p Ω) (i : Fin N) :
    (SobolevMultiIndex.weakDeriv (extendZero u) (MultiIndexLE.single i) :
      EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)) := by
  have h1 := ((SobolevMultiIndex.hasWeakIteratedLineDerivOn (extendZero u)
    (MultiIndexLE.single i)).of_perm (multiIndexTuple_single_perm
      ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → _) i)).congr_ae
    (by simpa only [Measure.restrict_coe_top] using fn_extendZero u)
    (Filter.EventuallyEq.refl _ _)
  have h2 := SobolevMultiIndexZero.hasWeakIteratedLineDerivOn_indicator u.2 i
  filter_upwards [h1.ae_eq h2] with x hx using hx (mem_univ x)

/-- The extension by zero is additive: $\overline{u + v} = \bar u + \bar v$ for
$u, v \in W_0^{1,p}(\Omega)$. -/
theorem extendZero_add (u v : SobolevEuclideanZero N 1 p Ω) :
    extendZero (u + v) = extendZero u + extendZero v := by
  refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
  have h1 : SobolevMultiIndex.fn (extendZero u + extendZero v) =ᵐ[volume]
      SobolevMultiIndex.fn (extendZero u) + SobolevMultiIndex.fn (extendZero v) := by
    simpa only [Measure.restrict_coe_top] using
      SobolevMultiIndex.fn_add (extendZero u) (extendZero v)
  have h2 : (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
      (SobolevMultiIndex.fn ((u : SobolevEuclidean N 1 p Ω) + (v : SobolevEuclidean N 1 p Ω)))
        =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)
          + SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω)) :=
    (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1
      (SobolevMultiIndex.fn_add (u : SobolevEuclidean N 1 p Ω) v)
  simp only [Measure.restrict_coe_top]
  refine (fn_extendZero (u + v)).trans (h2.trans (Filter.EventuallyEq.trans ?_ h1.symm))
  rw [Set.indicator_add']
  exact (fn_extendZero u).symm.add (fn_extendZero v).symm

/-- The extension by zero is homogeneous: $\overline{c u} = c \bar u$ for $c \in \mathbb{R}$ and
$u \in W_0^{1,p}(\Omega)$. -/
theorem extendZero_smul (c : ℝ) (u : SobolevEuclideanZero N 1 p Ω) :
    extendZero (c • u) = c • extendZero u := by
  refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
  have h1 : SobolevMultiIndex.fn (c • extendZero u) =ᵐ[volume]
      c • SobolevMultiIndex.fn (extendZero u) := by
    simpa only [Measure.restrict_coe_top] using SobolevMultiIndex.fn_smul c (extendZero u)
  have h2 : (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
      (SobolevMultiIndex.fn (c • (u : SobolevEuclidean N 1 p Ω))) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (c • SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) :=
    (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1
      (SobolevMultiIndex.fn_smul c (u : SobolevEuclidean N 1 p Ω))
  simp only [Measure.restrict_coe_top]
  refine (fn_extendZero (c • u)).trans (h2.trans (Filter.EventuallyEq.trans ?_ h1.symm))
  have h3 : (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
      (c • SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω))
      = c • (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) := by
    funext x
    exact congrFun (Set.indicator_const_smul (Ω : Set (EuclideanSpace ℝ (Fin N))) c
      (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω))) x
  rw [h3]
  exact (fn_extendZero u).symm.const_smul c

/-- For $u \in W_0^{1,p}(\Omega)$ and every multi-index $\alpha$ with $|\alpha| \le 1$,
$\|\partial^\alpha \bar u\|_{L^p(\mathbb{R}^N)} = \|\partial^\alpha u\|_{L^p(\Omega)}$: the
integrals over $\mathbb{R}^N$ of the extensions by zero are the integrals over $\Omega$. -/
theorem norm_weakDeriv_extendZero (u : SobolevEuclideanZero N 1 p Ω)
    (α : MultiIndexLE (Fin N) 1) :
    ‖SobolevMultiIndex.weakDeriv (extendZero u) α‖
      = ‖SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) α‖ := by
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
  · rw [Lp.norm_def, Lp.norm_def]
    simp only [Measure.restrict_coe_top]
    rw [eLpNorm_congr_ae (f := (SobolevMultiIndex.weakDeriv (extendZero u) 0 : _ → ℝ))
      (fn_extendZero u),
      eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet]
    rfl
  · rw [Lp.norm_def, Lp.norm_def]
    simp only [Measure.restrict_coe_top]
    rw [eLpNorm_congr_ae (weakDeriv_extendZero_single u i),
      eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet]

/-- **The extension by zero is an isometry**: $\|\bar u\|_{W^{1,p}(\mathbb{R}^N)} =
\|u\|_{W^{1,p}(\Omega)}$ for $u \in W_0^{1,p}(\Omega)$.

The norm is the $\ell^p$ sum of the $L^p$ norms of the components, and each of them is unchanged
(`SobolevEuclideanZero.norm_weakDeriv_extendZero`). -/
theorem norm_extendZero (u : SobolevEuclideanZero N 1 p Ω) :
    ‖extendZero u‖ = ‖(u : SobolevEuclidean N 1 p Ω)‖ := by
  rcases eq_or_ne p ⊤ with rfl | hp'
  · rw [SobolevMultiIndex.norm_eq_ciSup, SobolevMultiIndex.norm_eq_ciSup]
    exact iSup_congr (norm_weakDeriv_extendZero u)
  · rw [SobolevMultiIndex.norm_eq_sum hp', SobolevMultiIndex.norm_eq_sum hp']
    congr 1
    exact Finset.sum_congr rfl fun α _ ↦ by rw [norm_weakDeriv_extendZero]

variable (N p Ω) in
/-- The extension by zero $u \mapsto \bar u$, as a linear map
$W_0^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$. -/
def extendZeroₗ : SobolevEuclideanZero N 1 p Ω →ₗ[ℝ] SobolevEuclidean N 1 p ⊤ where
  toFun := extendZero
  map_add' := extendZero_add
  map_smul' := extendZero_smul

variable (N p Ω) in
/-- The **extension by zero** $u \mapsto \bar u$, as a bounded linear map
$W_0^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$, for every open $\Omega \subseteq \mathbb{R}^N$
and $1 \le p \le \infty$. The function of $\bar u$ is $\mathbf{1}_\Omega u$
(`SobolevEuclideanZero.fn_extendZeroL`), its partial derivatives are
$\partial_i \bar u = \overline{\partial_i u}$
(`SobolevEuclideanZero.weakDeriv_extendZeroL_single`), and the map is an isometry
(`SobolevEuclideanZero.norm_extendZeroL_apply`).

This is Proposition 9.18, (i) ⇒ (iii), of [brezis2011functional], together with Remark 20: "the
canonical extension by 0 outside $\Omega$, which is valid for arbitrary domains". -/
def extendZeroL : SobolevEuclideanZero N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤ :=
  (extendZeroₗ N p Ω).mkContinuous 1 fun u ↦ by
    rw [one_mul, ← Submodule.norm_coe]
    exact (norm_extendZero u).le

/-- The bounded linear map `SobolevEuclideanZero.extendZeroL` sends $u$ to
`SobolevEuclideanZero.extendZero u`. -/
@[simp]
theorem extendZeroL_apply (u : SobolevEuclideanZero N 1 p Ω) :
    extendZeroL N p Ω u = extendZero u :=
  rfl

/-- For $u \in W_0^{1,p}(\Omega)$, the function of $\bar u$ equals $\mathbf{1}_\Omega u$ almost
everywhere on $\mathbb{R}^N$. This is the statement $\bar u \in W^{1,p}(\mathbb{R}^N)$ of
Proposition 9.18 (iii) of [brezis2011functional]. -/
theorem fn_extendZeroL (u : SobolevEuclideanZero N 1 p Ω) :
    SobolevMultiIndex.fn (extendZeroL N p Ω u) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω)) :=
  fn_extendZero u

/-- For $u \in W_0^{1,p}(\Omega)$, the function of $\bar u$ equals the function of $u$ almost
everywhere on $\Omega$. -/
theorem fn_extendZeroL_restrict (u : SobolevEuclideanZero N 1 p Ω) :
    SobolevMultiIndex.fn (extendZeroL N p Ω u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) :=
  fn_extendZero_restrict u

/-- For $u \in W_0^{1,p}(\Omega)$ and every $i$, $\partial_i \bar u = \mathbf{1}_\Omega \partial_i
u$ almost everywhere on $\mathbb{R}^N$. This is the identity $\partial \bar u / \partial x_i =
\overline{\partial u / \partial x_i}$ of Proposition 9.18 (iii) of [brezis2011functional]. -/
theorem weakDeriv_extendZeroL_single (u : SobolevEuclideanZero N 1 p Ω) (i : Fin N) :
    (SobolevMultiIndex.weakDeriv (extendZeroL N p Ω u) (MultiIndexLE.single i) :
      EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)) :=
  weakDeriv_extendZero_single u i

/-- The extension by zero is an isometry: $\|\bar u\|_{W^{1,p}(\mathbb{R}^N)} =
\|u\|_{W^{1,p}(\Omega)}$ for $u \in W_0^{1,p}(\Omega)$. -/
theorem norm_extendZeroL_apply (u : SobolevEuclideanZero N 1 p Ω) :
    ‖extendZeroL N p Ω u‖ = ‖u‖ := by
  rw [extendZeroL_apply, norm_extendZero, Submodule.norm_coe]

/-- The operator norm of the extension by zero $W_0^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ is at
most $1$. -/
theorem norm_extendZeroL_le : ‖extendZeroL N p Ω‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- For every open $\Omega \subseteq \mathbb{R}^N$ and $1 \le p \le \infty$, the subspace
$W_0^{1,p}(\Omega)$ of $W^{1,p}(\Omega)$ has a Sobolev extension operator: the extension by zero
is a bounded linear map into $W^{1,p}(\mathbb{R}^N)$ whose values equal $u$ almost everywhere on
$\Omega$. This is Remark 20 in Chapter 9 of [brezis2011functional].

The conclusion is `HasSobolevExtensionOn`. Every consequence of that predicate, such as the
embeddings of Corollary 9.14 and the compactness of Theorem 9.16, therefore holds on
$W_0^{1,p}(\Omega)$ with no regularity of $\Omega$. -/
theorem hasSobolevExtensionOn : HasSobolevExtensionOn (SobolevEuclideanZero N 1 p Ω) :=
  ⟨extendZeroL N p Ω, fun u ↦ fn_extendZeroL_restrict u⟩

end SobolevEuclideanZero

end Typed

/-! ### Remarks 20 and 21: the Sobolev and Poincaré inequalities on $W_0^{1,p}(\Omega)$ -/

section Remark20

variable {N : ℕ} {p p' : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

namespace SobolevEuclideanZero

/-- **The Sobolev inequality on $W_0^{1,p}(\Omega)$**, sum form. Let $\Omega \subseteq \mathbb{R}^N$
be open, let $1 \le p < N$, and let $p^*$ satisfy $1/p^* = 1/p - 1/N$. Then for every
$u \in W_0^{1,p}(\Omega)$,
$$\|u\|_{L^{p^*}(\Omega)} \le C(p, N) \sum_i \|\partial_i u\|_{L^p(\Omega)},$$
where $C(p, N)$ is `SobolevEuclidean.gnsConst N p`. This is Remark 20 in Chapter 9 of
[brezis2011functional]: "it can also be deduced from Theorem 9.9 that …".

The proof applies Theorem 9.9 (`SobolevEuclidean.eLpNorm_fn_le_of_eq`) to the extension by zero
`SobolevEuclideanZero.extendZeroL`, whose partial derivatives have the $L^p$ norms of those of
$u$. The exponents $p$ and $p^*$ are `p` and `p'`, of type `ℝ≥0`. -/
theorem eLpNorm_fn_le_sum_of_eq (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclideanZero N 1 p Ω) :
    eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) (p' : ℝ≥0∞)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ SobolevEuclidean.gnsConst N p
        * ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
          (MultiIndexLE.single i)‖ := by
  have h := SobolevEuclidean.eLpNorm_fn_le_of_eq hpN hp' (extendZeroL N p Ω u)
  rw [eLpNorm_congr_ae (fn_extendZeroL u),
    eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet] at h
  simp only [extendZeroL_apply, norm_weakDeriv_extendZero] at h
  exact h

/-- **The Sobolev inequality on $W_0^{1,p}(\Omega)$.** Let $\Omega \subseteq \mathbb{R}^N$ be open,
let $1 \le p < N$, and let $p^*$ satisfy $1/p^* = 1/p - 1/N$. Then for every
$u \in W_0^{1,p}(\Omega)$,
$$\|u\|_{L^{p^*}(\Omega)} \le N \, C(p, N) \, \|\nabla u\|_{L^p(\Omega)},$$
where $C(p, N)$ is `SobolevEuclidean.gnsConst N p`. No regularity of $\Omega$ is needed, because
the extension by zero is an extension operator on $W_0^{1,p}(\Omega)$. This is Remark 20 in
Chapter 9 of [brezis2011functional].

The exponent $p^*$ is `p'`, and the gradient norm is `SobolevMultiIndex.gradNorm`. The sum form is
`SobolevEuclideanZero.eLpNorm_fn_le_sum_of_eq`. -/
theorem eLpNorm_fn_le_gradNorm_of_eq (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclideanZero N 1 p Ω) :
    eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) (p' : ℝ≥0∞)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N
          * gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
  refine (eLpNorm_fn_le_sum_of_eq hpN hp' u).trans ?_
  have hsum : ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
      ≤ N * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
    calc ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
        ≤ ∑ _i : Fin N, ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) :=
          Finset.sum_le_sum fun i _ ↦
            ENNReal.ofReal_le_ofReal (norm_weakDeriv_single_le_gradNorm _ i)
      _ = N * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc SobolevEuclidean.gnsConst N p
        * ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
      ≤ SobolevEuclidean.gnsConst N p
          * (N * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω))) :=
        mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N
          * gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal, mul_assoc]

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $1 \le p < N$, and let $p^*$ satisfy
$1/p^* = 1/p - 1/N$. Then $W_0^{1,p}(\Omega) \subseteq L^{p^*}(\Omega)$: the function of every
$u \in W_0^{1,p}(\Omega)$ lies in $L^{p^*}(\Omega)$. This is part of Remark 20 in Chapter 9 of
[brezis2011functional].

The exponent $p^*$ is `p'`. The memberships in the other spaces $L^q(\Omega)$ are
`SobolevEuclideanZero.memLp_fn_of_le`, `SobolevEuclideanZero.memLp_fn_of_lt` and
`SobolevEuclideanZero.memLp_fn_of_eq` in `Numlib.Analysis.Sobolev.EmbeddingDomain`. -/
theorem memLp_fn_sobolevConj (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclideanZero N 1 p Ω) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) (p' : ℝ≥0∞)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  memLp_iff.2 ((eLpNorm_fn_le_gradNorm_of_eq hpN hp' u).trans_lt ENNReal.ofReal_lt_top)

end SobolevEuclideanZero

end Remark20

section Remark21

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

namespace SobolevEuclideanZero

/-- Let $u \in W_0^{1,p}(\Omega)$ for an open $\Omega \subseteq \mathbb{R}^N$. Then the extension by
zero $\bar u$ has a weak derivative $w : \mathbb{R}^N \to (\mathbb{R}^N)^*$ on $\mathbb{R}^N$
such that $w(x) = 0$ for every $x \notin \Omega$, $w \in L^p(\mathbb{R}^N)$ and
$$\|w\|_{L^p(\mathbb{R}^N)} \le \sum_i \|\partial_i u\|_{L^p(\Omega)}.$$

The weak derivative is `HasWeakFDerivOn` on the whole space. The proof takes
$w = \mathbf{1}_\Omega w_0$ for a weak derivative $w_0$ of $\bar u$. The function $w_0$ vanishes
almost everywhere outside $\Omega$, because its values on the basis vectors are the extensions
by zero of the $\partial_i u$. -/
theorem exists_hasWeakFDerivOn_indicator (u : SobolevEuclideanZero N 1 p Ω) :
    ∃ w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
      HasWeakFDerivOn ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        (fn (u : SobolevEuclidean N 1 p Ω))) w ⊤ volume ∧
      (∀ x, x ∉ (Ω : Set (EuclideanSpace ℝ (Fin N))) → w x = 0) ∧
      MemLp w p volume ∧
      eLpNorm w p volume ≤ ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
        (MultiIndexLE.single i)‖ := by
  classical
  obtain ⟨w, hw, hwp, hwi, -⟩ := exists_hasWeakFDerivOn_fn (extendZeroL N p Ω u)
  simp only [Opens.coe_top, Measure.restrict_univ] at hwp hwi
  -- `w` vanishes almost everywhere off `Ω`
  have hzero : ∀ᵐ x ∂volume, x ∉ (Ω : Set (EuclideanSpace ℝ (Fin N))) → w x = 0 := by
    have hall : ∀ᵐ x ∂volume, ∀ i, w x ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis i)
        = (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
          (weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)) x :=
      ae_all_iff.2 fun i ↦ (hwi i).trans (weakDeriv_extendZeroL_single u i)
    filter_upwards [hall] with x hx hxΩ
    refine ContinuousLinearMap.ext fun ξ ↦ ?_
    rw [← (EuclideanSpace.basisFun (Fin N) ℝ).toBasis.sum_repr ξ, map_sum]
    simp only [map_smul, hx, Set.indicator_of_notMem hxΩ, smul_zero, Finset.sum_const_zero,
      zero_apply]
  have hae : w =ᵐ[volume] (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator w := by
    filter_upwards [hzero] with x hx
    by_cases hxΩ : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
    · rw [Set.indicator_of_mem hxΩ]
    · rw [Set.indicator_of_notMem hxΩ, hx hxΩ]
  refine ⟨(Ω : Set (EuclideanSpace ℝ (Fin N))).indicator w, ?_,
    fun x hx ↦ Set.indicator_of_notMem hx _, hwp.ae_eq hae, ?_⟩
  · unfold HasWeakFDerivOn
    refine HasWeakIteratedFDerivOn.congr_ae hw ?_ ?_
    · simpa only [Opens.coe_top, Measure.restrict_univ] using fn_extendZeroL u
    · simp only [Opens.coe_top, Measure.restrict_univ]
      filter_upwards [hae] with x hx
      rw [hx]
  · rw [← eLpNorm_congr_ae hae]
    exact (SobolevEuclidean.eLpNorm_le_sum_of_hasWeakFDerivOn (extendZeroL N p Ω u) hw).trans
      (le_of_eq (Finset.sum_congr rfl fun i _ ↦ by
        rw [extendZeroL_apply, norm_weakDeriv_extendZero]))

/-- For real numbers $0 < a \le 1$ and $0 < b < 1$ there is $c$ with $a \le c \le a + b$ and
$b < c \le 1$. This is the choice of exponents in the proof of
`SobolevEuclideanZero.exists_eLpNorm_fn_le_sum_of_measure_ne_top`. -/
theorem exists_exponent_aux {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b < 1) :
    ∃ c : ℝ, a ≤ c ∧ c ≤ a + b ∧ b < c ∧ c ≤ 1 :=
  ⟨min 1 (max a (b + a / 2)), le_min ha1 (le_max_left _ _),
    (min_le_right _ _).trans (max_le (by linarith) (by linarith)),
    lt_min hb1 ((lt_max_of_lt_right (by linarith))), min_le_left _ _⟩

/-- **Poincaré's inequality on an open set of finite measure**, sum form. Let $N \ge 2$, let
$1 \le p < \infty$, and let $\Omega \subseteq \mathbb{R}^N$ be open with finite measure. Then
there is a constant $C < \infty$ such that for every $u \in W_0^{1,p}(\Omega)$,
$$\|u\|_{L^p(\Omega)} \le C \sum_i \|\partial_i u\|_{L^p(\Omega)}.$$
This is the first clause of Remark 21 in Chapter 9 of [brezis2011functional]: "Poincaré's
inequality remains true if $\Omega$ has finite measure". For $N = 1$ the statement is false on
unbounded open sets of finite measure.

The constant $C$ is in `ℝ≥0∞`. The proof chooses an exponent $1 \le q \le p$ with $q < N$ and
$p \le q^*$, which is possible for $N \ge 2$. On $\Omega$, which has finite measure,
$L^p(\Omega) \subseteq L^q(\Omega)$. So the extension by zero $\bar u$ and its weak gradient
$w$, which vanishes outside $\Omega$, lie in $L^q(\mathbb{R}^N)$. Theorem 9.9 at the exponent
$q$ (`HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq`) gives $\|u\|_{q^*} \le C \|w\|_q$.
Hölder's inequalities $\|u\|_p \le |\Omega|^{1/p - 1/q^*} \|u\|_{q^*}$ and $\|w\|_q \le
|\Omega|^{1/q - 1/p} \|w\|_p \le |\Omega|^{1/q - 1/p} \sum_i \|\partial_i u\|_p$ conclude.
-/
theorem exists_eLpNorm_fn_le_sum_of_measure_ne_top (hp' : p ≠ ⊤) (hN : 2 ≤ N)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : SobolevEuclideanZero N 1 p Ω,
      eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) p (volume.restrict (Ω : Set _))
        ≤ C * ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
          (MultiIndexLE.single i)‖ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hΩm := Ω.isOpen.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    isFiniteMeasure_restrict.2 hΩ
  have hP1 : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hP0 : 0 < p.toReal := zero_lt_one.trans_le hP1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (zero_lt_two.trans_le hN)
  have hN1 : (N : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; exact_mod_cast (one_lt_two.trans_le hN)
  obtain ⟨c, hac, hcab, hbc, hc1⟩ := exists_exponent_aux (inv_pos.2 hP0) (inv_le_one_of_one_le₀ hP1)
    (inv_pos.2 hN0) hN1
  have hc0 : 0 < c := (inv_pos.2 hN0).trans hbc
  have hcb0 : 0 < c - (N : ℝ)⁻¹ := sub_pos.2 hbc
  -- the exponents `q = 1/c` and `q* = 1/(c - 1/N)`
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = c⁻¹ :=
    ⟨Real.toNNReal c⁻¹, Real.coe_toNNReal _ (inv_pos.2 hc0).le⟩
  obtain ⟨q', hq'⟩ : ∃ q' : ℝ≥0, (q' : ℝ) = (c - (N : ℝ)⁻¹)⁻¹ :=
    ⟨Real.toNNReal _, Real.coe_toNNReal _ (inv_pos.2 hcb0).le⟩
  have hq1 : 1 ≤ q := by
    rw [← NNReal.coe_le_coe, hq, NNReal.coe_one]
    exact one_le_inv₀ hc0 |>.2 hc1
  have hqN : q < N := by
    rw [← NNReal.coe_lt_coe, hq, NNReal.coe_natCast]
    rw [inv_lt_comm₀ hc0 hN0]
    exact hbc
  have hqq' : (q' : ℝ)⁻¹ = q⁻¹ - (N : ℝ)⁻¹ := by
    rw [hq', NNReal.coe_inv, hq, inv_inv, inv_inv]
  have hqp : (q : ℝ≥0∞) ≤ p := by
    rw [← ENNReal.ofReal_toReal hp', ← ENNReal.ofReal_coe_nnreal, hq]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_le_comm₀ hc0 hP0]
    exact hac
  have hpq' : p ≤ (q' : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hp', ← ENNReal.ofReal_coe_nnreal, hq']
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_inv_comm₀ hP0 hcb0]
    linarith
  -- the two powers of the measure of `Ω`
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
    ^ (1 / p.toReal - 1 / (q' : ℝ≥0∞).toReal) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
    ^ (1 / (q : ℝ≥0∞).toReal - 1 / p.toReal) := ⟨_, rfl⟩
  have hA' : A ≠ ⊤ := by
    rw [hA]
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hΩ
    rw [ENNReal.coe_toReal, hq', one_div, one_div, inv_inv, sub_nonneg]
    linarith
  have hB' : B ≠ ⊤ := by
    rw [hB]
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hΩ
    rw [ENNReal.coe_toReal, hq, one_div, one_div, inv_inv, sub_nonneg]
    exact hac
  refine ⟨SobolevEuclidean.gnsConst N q * B * A,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hB') hA', fun u ↦ ?_⟩
  obtain ⟨w, hw, hw0, hwp, hwle⟩ := exists_hasWeakFDerivOn_indicator u
  have hwae : w =ᵐ[volume] (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator w :=
    Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hw0 x hx]
  have hum : AEStronglyMeasurable (fn (u : SobolevEuclidean N 1 p Ω))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := (memLp _).aestronglyMeasurable
  -- memberships at the exponent `q`
  have hūq : MemLp ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
      (fn (u : SobolevEuclidean N 1 p Ω))) q volume :=
    (memLp_indicator_iff_restrict hΩm.nullMeasurableSet).2 ((memLp _).mono_exponent hqp)
  have hwq : MemLp w q volume := by
    refine ((memLp_indicator_iff_restrict hΩm.nullMeasurableSet).2 ?_).ae_eq hwae.symm
    exact (hwp.restrict _).mono_exponent hqp
  -- Theorem 9.9 at the exponent `q`
  have hN' : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  have hGNS := hw.eLpNorm_le_eLpNorm_weakFDeriv_of_eq hq1 (by rw [hN']; exact_mod_cast hqN)
    (by rw [hN']; exact hqq') hūq hwq
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hΩm.nullMeasurableSet] at hGNS
  -- the two Hölder steps on the finite-measure set `Ω`
  have hH1 : eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) p (volume.restrict (Ω : Set _))
      ≤ eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) (q' : ℝ≥0∞) (volume.restrict (Ω : Set _))
        * A := by
    rw [hA, ← Measure.restrict_apply_univ (μ := volume) (Ω : Set (EuclideanSpace ℝ (Fin N)))]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq' hum
  have hH2 : eLpNorm w (q : ℝ≥0∞) volume
      ≤ eLpNorm w p volume * B := by
    have e1 : eLpNorm w (q : ℝ≥0∞) volume
        = eLpNorm w q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      rw [eLpNorm_congr_ae hwae, eLpNorm_indicator_eq_eLpNorm_restrict hΩm.nullMeasurableSet]
    have e2 : eLpNorm w p volume
        = eLpNorm w p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      rw [eLpNorm_congr_ae hwae, eLpNorm_indicator_eq_eLpNorm_restrict hΩm.nullMeasurableSet]
    rw [e1, e2, hB,
      ← Measure.restrict_apply_univ (μ := volume) (Ω : Set (EuclideanSpace ℝ (Fin N)))]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp (hwp.restrict _).aestronglyMeasurable
  calc eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) p (volume.restrict (Ω : Set _))
      ≤ eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) (q' : ℝ≥0∞) (volume.restrict (Ω : Set _)) * A :=
        hH1
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ volume q * eLpNorm w (q : ℝ≥0∞) volume) * A :=
        mul_le_mul' hGNS le_rfl
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ volume q * (eLpNorm w p volume * B)) * A :=
        mul_le_mul' (mul_le_mul' le_rfl hH2) le_rfl
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ volume q
          * ((∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
            (MultiIndexLE.single i)‖) * B)) * A :=
        mul_le_mul' (mul_le_mul' le_rfl (mul_le_mul' hwle le_rfl)) le_rfl
    _ = SobolevEuclidean.gnsConst N q * B * A
          * ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω)
            (MultiIndexLE.single i)‖ := by
        rw [SobolevEuclidean.gnsConst]; ring

/-- **Poincaré's inequality on an open set of finite measure.** Let $N \ge 2$, let
$1 \le p < \infty$, and let $\Omega \subseteq \mathbb{R}^N$ be open with finite measure. Then
there is a constant $C < \infty$ such that for every $u \in W_0^{1,p}(\Omega)$,
$$\|u\|_{L^p(\Omega)} \le C \|\nabla u\|_{L^p(\Omega)}.$$
This is the first clause of Remark 21 in Chapter 9 of [brezis2011functional]. For $N = 1$ the
statement is false on unbounded open sets of finite measure.

The constant $C$ is in `ℝ≥0∞`, and the gradient norm is `SobolevMultiIndex.gradNorm`. The sum
form is `SobolevEuclideanZero.exists_eLpNorm_fn_le_sum_of_measure_ne_top`. The clause of Remark
21 for an open set of bounded projection is `SobolevEuclideanZero.eLpNorm_fn_le_of_subset_slab`
in `Numlib.Analysis.Sobolev.Poincare`. -/
theorem eLpNorm_fn_le_gradNorm_of_measure_ne_top (hp' : p ≠ ⊤) (hN : 2 ≤ N)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : SobolevEuclideanZero N 1 p Ω,
      eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) p (volume.restrict (Ω : Set _))
        ≤ C * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
  obtain ⟨C, hC, h⟩ := exists_eLpNorm_fn_le_sum_of_measure_ne_top (Ω := Ω) hp' hN hΩ
  refine ⟨C * N, ENNReal.mul_ne_top hC (ENNReal.natCast_ne_top N), fun u ↦ ?_⟩
  refine (h u).trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  calc ∑ i, ENNReal.ofReal ‖weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
      ≤ ∑ _i : Fin N, ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) :=
        Finset.sum_le_sum fun i _ ↦
          ENNReal.ofReal_le_ofReal (norm_weakDeriv_single_le_gradNorm _ i)
    _ = N * ENNReal.ofReal (gradNorm (u : SobolevEuclidean N 1 p Ω)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end SobolevEuclideanZero

end Remark21

/-!
### Remarks 17 and 18: $C_c^k(\Omega) \subseteq W_0^{k,p}(\Omega)$, and the whole space

This section proves $C_c^k(\Omega) \subseteq W_0^{k,p}(\Omega)$ and $W_0^{1,p}(\mathbb{R}^N) =
W^{1,p}(\mathbb{R}^N)$ for $1 \le p < \infty$.
-/

section Remarks

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Lemma 9.5 for a function with compact support in $\Omega$.** Let $1 \le p < \infty$ and let
$u \in W^{k,p}(\Omega)$. Suppose that the function of $u$ equals, almost everywhere on $\Omega$,
a function $v$ with compact support such that $\operatorname{supp} v \subseteq \Omega$. Then
$u \in W_0^{k,p}(\Omega)$.

The proof is `SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact` with
$K = \operatorname{supp} v$, the closed support `tsupport v`. -/
theorem SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset (hp' : p ≠ ⊤)
    (u : SobolevMultiIndex F b k p Ω μ) {v : E → F} (hvc : HasCompactSupport v)
    (hvΩ : tsupport v ⊆ Ω) (hu : SobolevMultiIndex.fn u =ᵐ[μ.restrict (Ω : Set E)] v) :
    u ∈ SobolevMultiIndexZero F b k p Ω μ :=
  SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact hp' u hvc hvΩ
    (hu.mono fun x hx hxK ↦ by rw [hx]; exact image_eq_zero_of_notMem_tsupport hxK)

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $1 \le p < \infty$, and let $v$ be a $C^k$
function on $\mathbb{R}^N$ with compact support such that
$\operatorname{supp} v \subseteq \Omega$. Then there is $u \in W_0^{k,p}(\Omega)$ whose function
equals $v$ almost everywhere on $\Omega$. This is Remark 18 of [brezis2011functional], together
with Remark 22 for $k \ge 2$.

So the closure of $C_c^k(\Omega)$ in $W^{k,p}(\Omega)$, which the source uses to define
$W_0^{k,p}(\Omega)$, is contained in the closure `SobolevEuclideanZero N k p Ω` of
$C_c^\infty(\Omega)$, and the two closures agree: "$C_c^\infty(\Omega)$ could equally well have
been used instead of $C_c^1(\Omega)$ in the definition of $W_0^{1,p}(\Omega)$". The proof uses
Lemma 9.5 and Remark 2. -/
theorem SobolevEuclidean.mem_zero_of_contDiff_hasCompactSupport {N : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (hp' : p ≠ ⊤) {v : EuclideanSpace ℝ (Fin N) → ℝ}
    (hv : ContDiff ℝ k v) (hvc : HasCompactSupport v) (hvΩ : tsupport v ⊆ Ω) :
    ∃ u ∈ SobolevEuclideanZero N k p Ω,
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v :=
  let ⟨u, hu⟩ := hv.exists_sobolevMultiIndex_of_hasCompactSupport'
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p) (Ω := Ω) (μ := volume) hvc
  ⟨u, SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset hp' u hvc hvΩ hu, hu⟩

/-- For $1 \le p < \infty$, $W_0^{1,p}(\mathbb{R}^N) = W^{1,p}(\mathbb{R}^N)$. This is the first
sentence of Remark 17 in Chapter 9 of [brezis2011functional].

The proof uses the density of $C_c^\infty(\mathbb{R}^N)$ in $W^{1,p}(\mathbb{R}^N)$ (Theorem
9.2), in the form
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn` with
the identity as extension operator. The approximants are test functions on $\mathbb{R}^N$. -/
theorem SobolevEuclideanZero.eq_top {N : ℕ} (hp' : p ≠ ⊤) :
    SobolevEuclideanZero N 1 p ⊤ = ⊤ := by
  refine top_unique fun u _ ↦ ?_
  have hS : HasSobolevExtensionOn (⊤ : Submodule ℝ (SobolevEuclidean N 1 p ⊤)) :=
    ⟨(⊤ : Submodule ℝ (SobolevEuclidean N 1 p ⊤)).subtypeL, fun _ ↦ Filter.EventuallyEq.rfl⟩
  obtain ⟨v, hvs, hvc, w, hw, hwt⟩ :=
    SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp' hS
      ⟨u, trivial⟩
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hwt (Eventually.of_forall fun n ↦ ?_)
  exact SobolevMultiIndexZero.testFunctions_le ⟨⟨v n, hvs n, hvc n, subset_univ _⟩, hw n⟩

end Remarks

/-! ### Proposition 9.18: the extension by zero and the distributional derivative -/

section Characterization

variable {N : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Integration by parts of a test function on $\Omega$ against a $C^1$ function.** Let
$\Omega \subseteq \mathbb{R}^N$ be open, let $\psi \in C^1(\mathbb{R}^N)$, let $\varphi$ be a
test function on $\Omega$, and let $v \in \mathbb{R}^N$. Then
$$\int_\Omega \varphi \, D\psi(x) v \, dx = -\int_\Omega D\varphi(x) v \, \psi \, dx.$$
Both integrals are over $\Omega$, because $\varphi$ vanishes outside $\Omega$. -/
theorem TestFunction.setIntegral_mul_fderiv_eq_neg {ψ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (φ : 𝓓(Ω, ℝ)) (v : EuclideanSpace ℝ (Fin N)) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x * fderiv ℝ ψ x v
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), fderiv ℝ φ x v * ψ x := by
  have h : ∫ x, fderiv ℝ φ x v * ψ x = -∫ x, φ x * fderiv ℝ ψ x v := by
    have := integral_fderiv_smul_eq_neg_integral_smul_apply (Ω := ⊤) (μ := volume)
      (hψ.continuous.locallyIntegrable.locallyIntegrableOn _)
      ((hψ.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
      (fun x _ ↦ (hψ.differentiable one_ne_zero x).hasFDerivAt) v
    simp only [smul_eq_mul] at this
    exact this
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [φ.eq_zero_of_notMem hx, zero_mul],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [← φ.fderivApply_apply v x, (φ.fderivApply v).eq_zero_of_notMem hx, zero_mul],
    h, neg_neg]

namespace SobolevEuclideanZero

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $1 \le p \le \infty$ and let $q$ be its
conjugate exponent. Let $u \in W_0^{1,p}(\Omega)$, and let $\varphi \in C^1(\mathbb{R}^N)$ have
compact support in $\mathbb{R}^N$ (not necessarily in $\Omega$). Then for every $i$,
$$\Big| \int_\Omega u \, \partial_i \varphi \Big| \le \|\partial_i u\|_{L^p(\Omega)}
  \|\varphi\|_{L^q(\Omega)}.$$
This is Proposition 9.18, (i) ⇒ (ii), of [brezis2011functional].

The proof takes test functions $u_n \to u$ in $W^{1,p}(\Omega)$. Then $\int_\Omega u_n
\partial_i \varphi = -\int_\Omega (\partial_i u_n) \varphi$ by integration by parts
(`TestFunction.setIntegral_mul_fderiv_eq_neg`). Hölder's inequality bounds this by
$\|\partial_i u_n\|_p \|\varphi\|_q$, and both sides pass to the limit. -/
theorem abs_integral_fn_smul_fderiv_le [p.HolderConjugate q] (u : SobolevEuclideanZero N 1 p Ω)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (i : Fin N) :
    |∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) x
          * fderiv ℝ φ x (EuclideanSpace.single i 1)|
      ≤ ‖SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
        * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
  obtain ⟨w, ψ, hψ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto u.2
  have hφq : MemLp φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict _
  have hdφ : MemLp (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφc.fderiv_apply ℝ _)).restrict _
  -- the inequality for each approximant
  have hn : ∀ n, |∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      SobolevMultiIndex.fn (w n) x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
      ≤ ‖SobolevMultiIndex.weakDeriv (w n) (MultiIndexLE.single i)‖
        * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
    intro n
    have e1 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        SobolevMultiIndex.fn (w n) x * fderiv ℝ φ x (EuclideanSpace.single i 1)
        = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) * φ x := by
      rw [← TestFunction.setIntegral_mul_fderiv_eq_neg hφ (ψ n)]
      exact integral_congr_ae ((hψ n).mono fun x hx ↦ by dsimp only; rw [hx])
    have e2 : eLpNorm (fun x ↦ fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)) p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        = eLpNorm (SobolevMultiIndex.weakDeriv (w n) (MultiIndexLE.single i)) p
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      refine (eLpNorm_congr_ae ?_).symm
      rw [← EuclideanSpace.basisFun_toBasis_apply i]
      exact SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction (hψ n) i
    have hH := enorm_integral_smul_le_eLpNorm_mul_eLpNorm
      (ν := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) (p := p) (q := q)
      (a := fun x ↦ fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)) (h := φ)
    simp only [smul_eq_mul] at hH
    rw [e2] at hH
    rw [e1, abs_neg, ← Real.norm_eq_abs, ← toReal_enorm, Lp.norm_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _) hφq.eLpNorm_ne_top) hH
  -- the limit
  have hL : Tendsto (fun n ↦ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      SobolevMultiIndex.fn (w n) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) atTop
      (𝓝 (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) x
          * fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    have ht := ((SobolevMultiIndex.fnL ℝ _ 1 p Ω volume).continuous.tendsto _).comp hw
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at ht
    have := tendsto_integral_mul_of_tendsto_eLpNorm (p := p) (q := q)
      (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      (a := fun n ↦ SobolevMultiIndex.fn (w n))
      (a₀ := SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω))
      (b := fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
      (fun n ↦ SobolevMultiIndex.memLp (w n)) (SobolevMultiIndex.memLp _) hdφ ht
    simp only [mul_comm] at this
    exact this
  have hR : Tendsto (fun n ↦ ‖SobolevMultiIndex.weakDeriv (w n) (MultiIndexLE.single i)‖
      * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) atTop
      (𝓝 (‖SobolevMultiIndex.weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i)‖
        * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) :=
    ((((SobolevMultiIndex.weakDerivL ℝ _ 1 p Ω volume (MultiIndexLE.single i)).continuous.tendsto
      _).comp hw).norm).mul_const _
  exact le_of_tendsto_of_tendsto' hL.abs hR hn

end SobolevEuclideanZero

omit [Fact (1 ≤ p)] in
/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $1 < p \le \infty$ and let $q < \infty$ be its
conjugate exponent. Let $u \in L^p(\Omega)$ and $C \in \mathbb{R}$, and suppose that for every
$\varphi \in C^1(\mathbb{R}^N)$ with compact support and every $i$,
$$\Big| \int_\Omega u \, \partial_i \varphi \Big| \le C \|\varphi\|_{L^q(\Omega)}.$$
Then the extension by zero $\bar u = \mathbf{1}_\Omega u$ lies in $W^{1,p}(\mathbb{R}^N)$. This
is Proposition 9.18, (ii) ⇒ (iii), of [brezis2011functional].

Since $\int_{\mathbb{R}^N} \bar u \, \partial_i \varphi = \int_\Omega u \, \partial_i \varphi$
and $\|\varphi\|_{L^q(\Omega)} \le \|\varphi\|_{L^q(\mathbb{R}^N)}$, the statement follows from
Proposition 9.3, (ii) ⇒ (i), on $\mathbb{R}^N$
(`MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le`). -/
theorem SobolevEuclidean.indicator_memSobolev_of_forall_abs_integral_le [p.HolderConjugate q]
    (hq : q ≠ ⊤) {u : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : MemLp u p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) {C : ℝ}
    (h : ∀ φ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ i : Fin N,
      |∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
        ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator u) 1 p ⊤ volume := by
  have hΩm := Ω.isOpen.measurableSet
  refine MemSobolev.memSobolevMultiIndex (MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le
    hq ?_ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (C := fun _ ↦ ENNReal.ofReal (max C 0))
    (fun _ ↦ ENNReal.ofReal_ne_top) fun φ i ↦ ?_)
  · simpa only [Measure.restrict_coe_top] using
      (memLp_indicator_iff_restrict hΩm.nullMeasurableSet).2 hu
  · have hφq : eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≠ ⊤ :=
      ((φ.memLp q volume).restrict _).eLpNorm_ne_top
    have hint : ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _),
        fderiv ℝ φ x ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis i)
          • (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator u x
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            u x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      simp only [Opens.coe_top, Measure.restrict_univ, EuclideanSpace.basisFun_toBasis_apply,
        smul_eq_mul]
      rw [← integral_indicator hΩm]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
      · simp [hx, mul_comm]
      · simp [hx]
    rw [hint, Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
        ≤ ENNReal.ofReal (max C 0 *
            (eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) := by
          refine ENNReal.ofReal_le_ofReal
            ((h φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport i).trans ?_)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg
      _ = ENNReal.ofReal (max C 0)
            * eLpNorm φ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
          rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_toReal hφq]
      _ ≤ ENNReal.ofReal (max C 0)
            * eLpNorm φ q (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _)) := by
          simp only [Opens.coe_top, Measure.restrict_univ]
          exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)

end Characterization

/-! ### The chain rule and the positive part preserve $W_0^{1,p}(\Omega)$ -/

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndexZero

omit [Fact (1 ≤ p)] in
/-- Let $u, v \in W^{1,p}(\Omega)$ be real-valued, and let $G \in C^1(\mathbb{R})$ with
$|G'| \le M$. If the function of $v$ equals $G \circ u$ almost everywhere on $\Omega$, then for
every $i$, $\partial_i v = G'(u) \, \partial_i u$ almost everywhere on $\Omega$.

The proof combines the chain rule `HasWeakIteratedLineDerivOn.contDiff_comp'` with the
uniqueness of the weak derivative. -/
theorem _root_.SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp
    {u v : SobolevMultiIndex ℝ b 1 p Ω μ} {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ}
    (hM : ∀ t, |deriv G t| ≤ M)
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ G (SobolevMultiIndex.fn u x))
    (i : ι) :
    (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ deriv G (SobolevMultiIndex.fn u x)
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x := by
  have h2 := ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).contDiff_comp' hG hM
  exact SobolevMultiIndex.weakDeriv_single_ae_eq_of_hasWeakIteratedLineDerivOn hv i h2

/-- **The chain rule preserves $W_0^{1,p}(\Omega)$.** Let $1 \le p < \infty$, let
$u \in W_0^{1,p}(\Omega)$ be real-valued, and let $G \in C^1(\mathbb{R})$ with $G(0) = 0$ and
$|G'| \le M$. Then every $v \in W^{1,p}(\Omega)$ whose function equals $G \circ u$ almost
everywhere on $\Omega$ lies in $W_0^{1,p}(\Omega)$. Such a $v$ exists by Proposition 9.5
(`MemSobolevMultiIndex.contDiff_comp`). This is the content of footnotes 35, 37 and 38 of §9.7
of [brezis2011functional]: "if $u \in H^1_0(\Omega)$ the assumption $u \in C(\bar\Omega)$ can be
removed".

The proof takes test functions $u_n \to u$ in $W^{1,p}(\Omega)$. Each $G \circ u_n$ is $C^1$
with compact support in $\Omega$, hence lies in $W_0^{1,p}(\Omega)$ by Lemma 9.5. Then
$G \circ u_n \to G \circ u$ in $L^p(\Omega)$, because $|G(a) - G(b)| \le M |a - b|$. Along a
subsequence on which $u_n \to u$ almost everywhere, $\nabla (G \circ u_n) = G'(u_n) \nabla u_n
\to G'(u) \nabla u$ in $L^p(\Omega)$, by the splitting $G'(u_n)(\nabla u_n - \nabla u) +
(G'(u_n) - G'(u)) \nabla u$: the first term is bounded by $M \|\nabla u_n - \nabla u\|_p$, and
the second tends to $0$ by dominated convergence. The closed subspace $W_0^{1,p}(\Omega)$
contains the limit. -/
theorem contDiff_comp_mem (hp' : p ≠ ⊤) {u : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (hG0 : G 0 = 0) {M : ℝ} (hM : ∀ t, |deriv G t| ≤ M) {v : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ G (SobolevMultiIndex.fn u x)) :
    v ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hG' : Continuous (deriv G) := hG.continuous_deriv le_rfl
  obtain ⟨w, φ, hφ, hw⟩ := exists_seq_testFunction_tendsto hu
  -- the test functions converge to `u` in `L^p(Ω)`, and almost everywhere along a subsequence
  have hφu : Tendsto (fun n ↦ eLpNorm ((φ n : E → ℝ) - SobolevMultiIndex.fn u) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) :=
    (SobolevMultiIndex.tendsto_eLpNorm_fn_sub hw).congr fun n ↦
      eLpNorm_congr_ae ((hφ n).sub (Filter.EventuallyEq.refl _ _))
  obtain ⟨ns, hns, -, -, hae, -⟩ := exists_subseq_tendsto_ae_ae_le_of_tendsto_eLpNorm
    (fun n ↦ ((φ n).memLp p μ).restrict _) (SobolevMultiIndex.memLp u) hφu
  -- `G ∘ φ n` lies in `W_0^{1,p}(Ω)`
  have hGφ : ∀ n, ContDiff ℝ 1 fun x ↦ G (φ n x) := fun n ↦
    hG.comp ((φ n).contDiff.of_le (by simp))
  have hGφc : ∀ n, HasCompactSupport fun x ↦ G (φ n x) := fun n ↦
    (φ n).hasCompactSupport.comp_left hG0
  have hGφΩ : ∀ n, tsupport (fun x ↦ G (φ n x)) ⊆ Ω := fun n ↦
    (tsupport_comp_subset hG0 (φ n : E → ℝ)).trans (φ n).tsupport_subset
  choose V hV using fun n ↦ (hGφ n).exists_sobolevMultiIndex_of_hasCompactSupport'
    (b := b) (p := p) (Ω := Ω) (μ := μ) (hGφc n)
  have hVmem : ∀ n, V n ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := fun n ↦
    SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset hp' (V n) (hGφc n) (hGφΩ n) (hV n)
  -- `V (ns k) → v` in `W^{1,p}(Ω)`
  refine isClosed.mem_of_tendsto (f := fun k ↦ V (ns k)) (b := atTop) ?_
    (Eventually.of_forall fun k ↦ hVmem _)
  refine SobolevMultiIndex.tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun α ↦ ?_
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
  · -- the functions: `|G(φ_n) − G(u)| ≤ M |φ_n − u|`
    have hbd : ∀ k, eLpNorm ((SobolevMultiIndex.weakDeriv (V (ns k)) 0 : E → ℝ)
        - (SobolevMultiIndex.weakDeriv v 0 : E → ℝ)) p (μ.restrict (Ω : Set E))
        ≤ ENNReal.ofReal M * eLpNorm ((φ (ns k) : E → ℝ) - SobolevMultiIndex.fn u) p
          (μ.restrict (Ω : Set E)) := by
      intro k
      have heq : ((SobolevMultiIndex.weakDeriv (V (ns k)) 0 : E → ℝ)
          - (SobolevMultiIndex.weakDeriv v 0 : E → ℝ)) =ᵐ[μ.restrict (Ω : Set E)]
          fun x ↦ G (φ (ns k) x) - G (SobolevMultiIndex.fn u x) := (hV (ns k)).sub hv
      rw [eLpNorm_congr_ae heq]
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x ↦ ?_) p
      · exact (hGφ _).continuous.aestronglyMeasurable.sub
          (hG.continuous.comp_aestronglyMeasurable (SobolevMultiIndex.memLp u).aestronglyMeasurable)
      · simp only [Real.norm_eq_abs, Pi.sub_apply]
        exact abs_sub_le_mul_of_abs_deriv_le hG hM _ _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
    simpa using ENNReal.Tendsto.const_mul (hφu.comp hns.tendsto_atTop)
      (Or.inr ENNReal.ofReal_ne_top)
  · -- the derivatives: `G'(φ_n) ∂_i φ_n → G'(u) ∂_i u`
    have hdV : ∀ k, (SobolevMultiIndex.weakDeriv (V k) (MultiIndexLE.single i) : E → ℝ)
        =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ deriv G (φ k x)
          * SobolevMultiIndex.weakDeriv (w k) (MultiIndexLE.single i) x := fun k ↦ by
      refine (SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp (u := w k) hG hM
        ((hV k).trans ((hφ k).mono fun x hx ↦ by dsimp only; rw [hx])) i).trans ?_
      filter_upwards [hφ k] with x hx
      rw [hx]
    have hdv := SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp hG hM hv i
    have hsplit : ∀ k, ((SobolevMultiIndex.weakDeriv (V (ns k)) (MultiIndexLE.single i) : E → ℝ)
        - (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ))
        =ᵐ[μ.restrict (Ω : Set E)]
          (fun x ↦ deriv G (φ (ns k) x)
            * (SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) x
              - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x))
          + fun x ↦ (deriv G (φ (ns k) x) - deriv G (SobolevMultiIndex.fn u x))
            * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x := by
      intro k
      filter_upwards [hdV (ns k), hdv] with x h1 h2
      simp only [Pi.sub_apply, Pi.add_apply, h1, h2]
      ring
    have hA : Tendsto (fun k ↦ eLpNorm (fun x ↦ deriv G (φ (ns k) x)
        * (SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) x
          - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)) p
        (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
      have hbd : ∀ k, eLpNorm (fun x ↦ deriv G (φ (ns k) x)
          * (SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) x
            - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)) p
          (μ.restrict (Ω : Set E))
          ≤ ENNReal.ofReal M * eLpNorm
            ((SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) : E → ℝ)
              - (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : E → ℝ)) p
            (μ.restrict (Ω : Set E)) := fun k ↦ by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x ↦ ?_) p
        · exact (hG'.comp_aestronglyMeasurable (φ _).contDiff.continuous.aestronglyMeasurable).mul
            ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
        · simp only [norm_mul, Real.norm_eq_abs, Pi.sub_apply]
          exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le)
        hbd
      simpa using ENNReal.Tendsto.const_mul
        ((SobolevMultiIndex.tendsto_eLpNorm_weakDeriv_sub hw (MultiIndexLE.single i)).comp
          hns.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
    have hB : Tendsto (fun k ↦ eLpNorm ((fun x ↦
        (deriv G (φ (ns k) x) - deriv G (SobolevMultiIndex.fn u x))
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x) - (0 : E → ℝ)) p
        (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
      refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp' (g := 0)
        (bound := fun x ↦ 2 * M * ‖SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x‖)
        (fun k ↦ ?_) aestronglyMeasurable_zero ((Lp.memLp _).norm.const_mul _)
        (fun k ↦ Eventually.of_forall fun x ↦ ?_) ?_
      · exact ((hG'.comp_aestronglyMeasurable (φ _).contDiff.continuous.aestronglyMeasurable).sub
          (hG'.comp_aestronglyMeasurable (SobolevMultiIndex.memLp u).aestronglyMeasurable)).mul
          (Lp.aestronglyMeasurable _)
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [Real.norm_eq_abs, two_mul]
        exact (abs_sub _ _).trans (add_le_add (hM _) (hM _))
      · filter_upwards [hae] with x hx
        have := (((hG'.tendsto _).comp hx).sub
          (tendsto_const_nhds (x := deriv G (SobolevMultiIndex.fn u x)))).mul_const
          (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)
        simpa [Function.comp_def] using this
    have hbd : ∀ k, eLpNorm ((SobolevMultiIndex.weakDeriv (V (ns k)) (MultiIndexLE.single i) :
        E → ℝ) - (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ)) p
        (μ.restrict (Ω : Set E))
        ≤ eLpNorm (fun x ↦ deriv G (φ (ns k) x)
            * (SobolevMultiIndex.weakDeriv (w (ns k)) (MultiIndexLE.single i) x
              - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)) p
            (μ.restrict (Ω : Set E))
          + eLpNorm ((fun x ↦ (deriv G (φ (ns k) x) - deriv G (SobolevMultiIndex.fn u x))
            * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x) - (0 : E → ℝ)) p
            (μ.restrict (Ω : Set E)) := fun k ↦ by
      rw [eLpNorm_congr_ae (hsplit k), sub_zero]
      exact eLpNorm_add_le hp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
    simpa using hA.add hB

end SobolevMultiIndexZero

end ChainRule

section PosPart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndexZero

omit [Fact (1 ≤ p)] in
/-- Let $u, v \in W^{1,p}(\Omega)$ be real-valued. If the function of $v$ equals $u^+ = \max(u, 0)$
almost everywhere on $\Omega$, then for every $i$, $\partial_i v = \mathbf{1}_{\{u > 0\}}
\partial_i u$ almost everywhere on $\Omega$.

The proof combines `HasWeakIteratedLineDerivOn.posPart` with the uniqueness of the weak
derivative. -/
theorem _root_.SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart
    {u v : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ max (SobolevMultiIndex.fn u x) 0) (i : ι) :
    (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
      {x | 0 < SobolevMultiIndex.fn u x}.indicator
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)) := by
  have h2 := ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).posPart
  exact SobolevMultiIndex.weakDeriv_single_ae_eq_of_hasWeakIteratedLineDerivOn hv i h2

/-- **The positive part preserves $W_0^{1,p}(\Omega)$.** Let $1 \le p < \infty$ and let
$u \in W_0^{1,p}(\Omega)$ be real-valued. Then every $v \in W^{1,p}(\Omega)$ whose function
equals $u^+ = \max(u, 0)$ almost everywhere on $\Omega$ lies in $W_0^{1,p}(\Omega)$. Such a $v$
exists by `MemSobolevMultiIndex.posPart`.

The proof uses the $C^1$ approximations $G_\varepsilon(s) = \sqrt{(\max(s, 0))^2 +
\varepsilon^2} - \varepsilon$ of the positive part. By the chain rule
(`SobolevMultiIndexZero.contDiff_comp_mem`), $G_\varepsilon(u) \in W_0^{1,p}(\Omega)$. As
$\varepsilon \to 0$, $G_\varepsilon(u) \to u^+$ in $W^{1,p}(\Omega)$ by dominated convergence,
with $|G_\varepsilon(u)| \le |u|$ and $|G_\varepsilon'(u) \, \partial_i u| \le |\partial_i u|$.
The argument is that of Kinderlehrer and Stampacchia, *An Introduction to Variational
Inequalities and Their Applications*, Theorem II.A.1. The result makes the obstacle set
$\{v \in H^1_0(\Omega) : v \ge \psi\}$ nonempty. -/
theorem posPart_mem (hp' : p ≠ ⊤) {u : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ) {v : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ max (SobolevMultiIndex.fn u x) 0) :
    v ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hum : AEStronglyMeasurable (SobolevMultiIndex.fn u) (μ.restrict (Ω : Set E)) :=
    (SobolevMultiIndex.memLp u).aestronglyMeasurable
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun n : ℕ ↦ 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by rw [hεdef]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := hεdef ▸ tendsto_one_div_add_atTop_nhds_zero_nat
  -- the approximants `G_{ε n}(u)`, in `W_0^{1,p}(Ω)`
  have hGn : ∀ n, MemSobolevMultiIndex b (fun x ↦ posPartApprox (ε n) (SobolevMultiIndex.fn u x))
      1 p Ω μ := fun n ↦ (SobolevMultiIndex.memSobolevMultiIndex u).contDiff_comp hp
    (contDiff_posPartApprox (hεpos n)) (posPartApprox_zero (hεpos n).le)
    (abs_deriv_posPartApprox_le (hεpos n))
  choose V hV using fun n ↦ (hGn n).exists_sobolevMultiIndex
  have hVmem : ∀ n, V n ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := fun n ↦
    contDiff_comp_mem hp' hu (contDiff_posPartApprox (hεpos n)) (posPartApprox_zero (hεpos n).le)
      (abs_deriv_posPartApprox_le (hεpos n)) (hV n)
  -- `V n → v` in `W^{1,p}(Ω)`
  refine isClosed.mem_of_tendsto (f := V) (b := atTop) ?_ (Eventually.of_forall hVmem)
  refine SobolevMultiIndex.tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun α ↦ ?_
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
  · -- the functions: `G_ε(u) → u⁺`, dominated by `|u|`
    have heq : ∀ n, ((SobolevMultiIndex.weakDeriv (V n) 0 : E → ℝ)
        - (SobolevMultiIndex.weakDeriv v 0 : E → ℝ)) =ᵐ[μ.restrict (Ω : Set E)]
        (fun x ↦ posPartApprox (ε n) (SobolevMultiIndex.fn u x))
          - fun x ↦ max (SobolevMultiIndex.fn u x) 0 := fun n ↦ (hV n).sub hv
    refine (tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp'
      (bound := fun x ↦ ‖SobolevMultiIndex.fn u x‖) (fun n ↦ ?_) ?_ (SobolevMultiIndex.memLp u).norm
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)).congr
      fun n ↦ (eLpNorm_congr_ae (heq n)).symm
    · exact (contDiff_posPartApprox (hεpos n)).continuous.comp_aestronglyMeasurable hum
    · exact (continuous_id.max continuous_const).comp_aestronglyMeasurable hum
    · exact (abs_posPartApprox_le (hεpos n).le _).trans (Real.norm_eq_abs _).symm.le
    · exact (tendsto_posPartApprox _).comp hεt
  · -- the derivatives: `G_ε'(u) ∂_i u → {u > 0}.indicator (∂_i u)`, dominated by `|∂_i u|`
    have hdV : ∀ n, (SobolevMultiIndex.weakDeriv (V n) (MultiIndexLE.single i) : E → ℝ)
        =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ deriv (posPartApprox (ε n)) (SobolevMultiIndex.fn u x)
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x := fun n ↦
      SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp (contDiff_posPartApprox (hεpos n))
        (abs_deriv_posPartApprox_le (hεpos n)) (hV n) i
    have hdv := SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart hv i
    have heq : ∀ n, ((SobolevMultiIndex.weakDeriv (V n) (MultiIndexLE.single i) : E → ℝ)
        - (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ))
        =ᵐ[μ.restrict (Ω : Set E)]
        (fun x ↦ deriv (posPartApprox (ε n)) (SobolevMultiIndex.fn u x)
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x)
          - {x | 0 < SobolevMultiIndex.fn u x}.indicator
            (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)) := fun n ↦ (hdV n).sub hdv
    have hind : ∀ x, {x | 0 < SobolevMultiIndex.fn u x}.indicator
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)) x
        = (if 0 < SobolevMultiIndex.fn u x then 1 else 0)
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x := fun x ↦ by
      by_cases hx : 0 < SobolevMultiIndex.fn u x <;> simp [Set.indicator, hx]
    refine (tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp'
      (bound := fun x ↦ ‖SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x‖) (fun n ↦ ?_) ?_
      (Lp.memLp _).norm (fun n ↦ Eventually.of_forall fun x ↦ ?_)
      (Eventually.of_forall fun x ↦ ?_)).congr fun n ↦ (eLpNorm_congr_ae (heq n)).symm
    · exact (((contDiff_posPartApprox (hεpos n)).continuous_deriv le_rfl).comp_aestronglyMeasurable
        hum).mul (Lp.aestronglyMeasurable _)
    · exact aestronglyMeasurable_indicator_pos hum (Lp.aestronglyMeasurable _)
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_deriv_posPartApprox_le (hεpos n) _)
    · have e : ∀ n, deriv (posPartApprox (ε n)) (SobolevMultiIndex.fn u x)
          = max (SobolevMultiIndex.fn u x) 0 / √(posSq (SobolevMultiIndex.fn u x) + ε n ^ 2) :=
        fun n ↦ deriv_posPartApprox (hεpos n) _
      simp_rw [e, hind x]
      exact ((tendsto_deriv_posPartApprox _).comp hεt).mul_const _

end SobolevMultiIndexZero

/-- **The positive part preserves $W_0^{1,p}(\Omega)$** on an open $\Omega \subseteq \mathbb{R}^N$.
Let $1 \le p < \infty$, let $u \in W_0^{1,p}(\Omega)$, and let $v \in W^{1,p}(\Omega)$ have the
function $u^+ = \max(u, 0)$ almost everywhere on $\Omega$. Then $v \in W_0^{1,p}(\Omega)$.

This is `SobolevMultiIndexZero.posPart_mem` on `SobolevEuclideanZero`. Together with
`MemSobolevMultiIndex.posPart`, which gives the existence of $v$, it makes the obstacle set $\{v
\in H^1_0(\Omega) : v \ge \psi \text{ a.e.}\}$ nonempty when $\psi \in H^1(\Omega)$ has
$\psi^+ \in H^1_0(\Omega)$ (Kinderlehrer and Stampacchia, *An Introduction to Variational
Inequalities and Their Applications*, Theorem II.A.1). -/
theorem SobolevEuclideanZero.posPart_mem {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (hp' : p ≠ ⊤) (u : SobolevEuclideanZero N 1 p Ω) {v : SobolevEuclidean N 1 p Ω}
    (hv : SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ max (SobolevMultiIndex.fn (u : SobolevEuclidean N 1 p Ω) x) 0) :
    v ∈ SobolevEuclideanZero N 1 p Ω :=
  SobolevMultiIndexZero.posPart_mem hp' u.2 hv

end PosPart

/-!
### Theorem 9.17, (i) ⇒ (ii): a continuous function vanishing on the boundary is in $W_0^{1,p}$

The proof uses the truncation $G(t) = t \, s(t^2 - 1)$ of the proof in the source, where $s$ is
`Real.smoothTransition`. It is smooth, has bounded derivative, and satisfies $G(t) = 0$ for
$|t| \le 1$ and $G(t) = t$ for $|t| \ge 2$ (in fact for $|t| \ge \sqrt 2$).
-/

section StepTruncation

/-- The **truncation** $G(t) = t \, s(t^2 - 1)$ of the proof of Theorem 9.17 of
[brezis2011functional], where $s$ is `Real.smoothTransition`, a smooth function equal to $0$ on
$(-\infty, 0]$ and to $1$ on $[1, \infty)$.

The function $G$ is smooth, $G(t) = 0$ for $|t| \le 1$, $G(t) = t$ for $|t| \ge 2$,
$|G(t)| \le |t|$, and $G'$ is bounded. -/
def stepTruncation (t : ℝ) : ℝ := t * Real.smoothTransition (t ^ 2 - 1)

/-- The truncation $G$ is smooth. -/
theorem contDiff_stepTruncation : ContDiff ℝ ∞ stepTruncation :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp ((contDiff_id.pow 2).sub contDiff_const))

/-- The truncation satisfies $G(0) = 0$. -/
theorem stepTruncation_zero : stepTruncation 0 = 0 := by simp [stepTruncation]

/-- The truncation satisfies $G(t) = 0$ for $|t| \le 1$. -/
theorem stepTruncation_of_abs_le {t : ℝ} (ht : |t| ≤ 1) : stepTruncation t = 0 := by
  have h : t ^ 2 - 1 ≤ 0 := by nlinarith [abs_nonneg t, sq_abs t]
  simp [stepTruncation, Real.smoothTransition.zero_of_nonpos h]

/-- The truncation satisfies $G(t) = t$ for $|t| \ge 2$. -/
theorem stepTruncation_of_two_le {t : ℝ} (ht : 2 ≤ |t|) : stepTruncation t = t := by
  have h : 1 ≤ t ^ 2 - 1 := by nlinarith [sq_abs t]
  simp [stepTruncation, Real.smoothTransition.one_of_one_le h]

/-- The truncation satisfies $|G(t)| \le |t|$ for every $t$. -/
theorem abs_stepTruncation_le (t : ℝ) : |stepTruncation t| ≤ |t| := by
  rw [stepTruncation, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.le_one _)

/-- The derivative of the truncation satisfies $G'(t) = 0$ for $|t| < 1$. -/
theorem deriv_stepTruncation_of_abs_lt {t : ℝ} (ht : |t| < 1) : deriv stepTruncation t = 0 := by
  have hev : stepTruncation =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) :=
    Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds ht)
      fun s hs ↦ stepTruncation_of_abs_le hs.le
  rw [hev.deriv_eq, deriv_const]

/-- The derivative of the truncation satisfies $G'(t) = 1$ for $|t| > 2$. -/
theorem deriv_stepTruncation_of_two_lt {t : ℝ} (ht : 2 < |t|) : deriv stepTruncation t = 1 := by
  have hev : stepTruncation =ᶠ[𝓝 t] id :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_abs).mem_nhds ht)
      fun s hs ↦ stepTruncation_of_two_le hs.le
  rw [hev.deriv_eq, deriv_id]

/-- The derivative of the truncation is bounded: there is $M \ge 0$ with $|G'(t)| \le M$ for every
$t$. The derivative is continuous, and it equals $1$ outside $[-2, 2]$. -/
theorem exists_abs_deriv_stepTruncation_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv stepTruncation t| ≤ M := by
  have hc : Continuous (deriv stepTruncation) := contDiff_stepTruncation.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, zero_le_one.trans (le_max_right _ _), fun t ↦ ?_⟩
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · exact (Real.norm_eq_abs _).symm.le.trans ((hC t ht).trans (le_max_left _ _))
  · have h2 : 2 < |t| := by
      rw [lt_abs]
      rcases not_and_or.1 ht with h | h
      · right; linarith [not_le.1 h]
      · left; exact not_le.1 h
    rw [deriv_stepTruncation_of_two_lt h2, abs_one]
    exact le_max_right _ _

/-- For $c \neq 0$, the scaled truncation $G_c(s) = c^{-1} G(sc)$ has the derivative $G'(tc)$ at
every $t \in \mathbb{R}$.

For $c > 0$, $G_c$ vanishes for $|s| \le 1/c$ and is the identity for $|s| \ge 2/c$. -/
theorem hasDerivAt_scaled_stepTruncation {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (fun s ↦ c⁻¹ * stepTruncation (s * c)) (deriv stepTruncation (t * c)) t := by
  have h := ((contDiff_stepTruncation.differentiable (by simp)) (t * c)).hasDerivAt.comp t
    (hasDerivAt_mul_const c)
  have := h.const_mul c⁻¹
  convert this using 1
  · rfl
  · field_simp

end StepTruncation

section ContinuousBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndex

/-- **A continuous function with bounded support that vanishes on the boundary lies in
$W_0^{1,p}(\Omega)$.** Let $\Omega \subseteq E$ be open, let $1 \le p < \infty$, and let
$u \in W^{1,p}(\Omega)$ be real-valued. Suppose that the function of $u$ equals, almost
everywhere on $\Omega$, a function $\tilde u$ that is continuous on $\bar\Omega$, vanishes on
$\partial\Omega$, and vanishes for $\|x\| > R$. Then $u \in W_0^{1,p}(\Omega)$. This is Theorem
9.17, (i) ⇒ (ii), of [brezis2011functional], for a function of bounded support.

The proof follows the source with one change. With the truncations $G_n(t) = G(nt)/n$ of
`stepTruncation`, $u_n = G_n \circ u$ lies in $W^{1,p}(\Omega)$ by Proposition 9.5. Its support
lies in $\{|\tilde u| \ge 1/n\}$, which is a compact subset of $\Omega$: it is closed and
bounded in $\bar\Omega$ and does not meet $\partial\Omega$, where $\tilde u = 0$. So
$u_n \in W_0^{1,p}(\Omega)$ by Lemma 9.5. The source concludes "$u_n \to u$ in $W^{1,p}$ by
dominated convergence", which needs $\nabla u = 0$ almost everywhere on $\{u = 0\}$. Here
instead $u_n \to \tilde u$ and $\nabla u_n = G_n'(\tilde u) \nabla u \to \mathbf{1}_{\{\tilde u
\neq 0\}} \nabla u$ in $L^p(\Omega)$ by dominated convergence, since $G_n'(0) = 0$ and
$G_n'(t) = 1$ for $n |t| > 2$. So $(u_n)$ is a Cauchy sequence in $W^{1,p}(\Omega)$. Its limit
lies in the closed subspace $W_0^{1,p}(\Omega)$ and has the function $\tilde u$, so it is $u$. -/
theorem mem_zero_of_continuousOn_closure_of_eqOn_frontier_of_forall_eq_zero (hp' : p ≠ ⊤)
    (u : SobolevMultiIndex ℝ b 1 p Ω μ) {ũ : E → ℝ} (hu : fn u =ᵐ[μ.restrict (Ω : Set E)] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (h0 : EqOn ũ 0 (frontier Ω)) {R : ℝ}
    (hR : ∀ x, R < ‖x‖ → ũ x = 0) : u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hΩm := Ω.isOpen.measurableSet
  have hum : AEStronglyMeasurable ũ (μ.restrict (Ω : Set E)) :=
    (memLp u).aestronglyMeasurable.congr hu
  have hũp : MemLp ũ p (μ.restrict (Ω : Set E)) := (memLp u).ae_eq hu
  obtain ⟨M, -, hM⟩ := exists_abs_deriv_stepTruncation_le
  -- the scaled truncations `G_n(t) = G((n+1) t)/(n+1)`
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℝ → ℝ,
      G = fun (n : ℕ) (t : ℝ) ↦ ((n : ℝ) + 1)⁻¹ * stepTruncation (t * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have hcpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n ↦ by positivity
  have hGd : ∀ n t, HasDerivAt (G n) (deriv stepTruncation (t * ((n : ℝ) + 1))) t := fun n t ↦ by
    rw [hGdef]
    exact hasDerivAt_scaled_stepTruncation (hcpos n).ne' t
  have hGc : ∀ n, ContDiff ℝ 1 (G n) := fun n ↦ by
    rw [hGdef]
    exact contDiff_const.mul
      ((contDiff_stepTruncation.of_le (by simp)).comp (contDiff_id.mul contDiff_const))
  have hG0 : ∀ n, G n 0 = 0 := fun n ↦ by simp [hGdef, stepTruncation_zero]
  have hGderiv : ∀ n t, deriv (G n) t = deriv stepTruncation (t * ((n : ℝ) + 1)) :=
    fun n t ↦ (hGd n t).deriv
  have hGM : ∀ n t, |deriv (G n) t| ≤ M := fun n t ↦ by rw [hGderiv]; exact hM _
  have hGle : ∀ n t, |G n t| ≤ M * |t| := fun n t ↦ by
    simpa [hG0 n] using abs_sub_le_mul_of_abs_deriv_le (hGc n) (hGM n) t 0
  have hGzero : ∀ (n : ℕ) (t : ℝ), |t| * ((n : ℝ) + 1) ≤ 1 → G n t = 0 := fun n t ht ↦ by
    simp only [hGdef]
    rw [stepTruncation_of_abs_le (by rwa [abs_mul, abs_of_pos (hcpos n)]), mul_zero]
  have hGid : ∀ (n : ℕ) (t : ℝ), 2 ≤ |t| * ((n : ℝ) + 1) → G n t = t := fun n t ht ↦ by
    simp only [hGdef]
    rw [stepTruncation_of_two_le (by rwa [abs_mul, abs_of_pos (hcpos n)])]
    field_simp
  have hGd0 : ∀ n, deriv (G n) 0 = 0 := fun n ↦ by
    rw [hGderiv, zero_mul]
    exact deriv_stepTruncation_of_abs_lt (by simp)
  have hGd1 : ∀ (n : ℕ) (t : ℝ), 2 < |t| * ((n : ℝ) + 1) → deriv (G n) t = 1 := fun n t ht ↦ by
    rw [hGderiv]
    exact deriv_stepTruncation_of_two_lt (by rwa [abs_mul, abs_of_pos (hcpos n)])
  have hev : ∀ t : ℝ, t ≠ 0 → ∀ n ≥ ⌈2 / |t|⌉₊, 2 < |t| * ((n : ℝ) + 1) := fun t ht n hn ↦ by
    have hpos : 0 < |t| := abs_pos.2 ht
    have h1 : 2 / |t| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [div_le_iff₀ hpos] at h1
    nlinarith
  -- the truncated functions `u_n = G_n ∘ u`, as elements of `W^{1,p}(Ω)`
  choose U hU using fun n ↦
    ((memSobolevMultiIndex u).contDiff_comp hp (hGc n) (hG0 n) (hGM n)).exists_sobolevMultiIndex
  have hUũ : ∀ n, fn (U n) =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ G n (ũ x) := fun n ↦
    (hU n).trans (hu.mono fun x hx ↦ by dsimp only; rw [hx])
  -- (a) each `u_n` has compact support in `Ω`, hence lies in `W_0^{1,p}(Ω)`
  have hUmem : ∀ n, U n ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
    intro n
    have hK1 : IsClosed (closure (Ω : Set E) ∩ (fun x ↦ |ũ x|) ⁻¹' Ici (((n : ℝ) + 1)⁻¹)) :=
      (continuous_abs.comp_continuousOn hc).preimage_isClosed_of_isClosed isClosed_closure
        isClosed_Ici
    have hK : IsCompact (closure (Ω : Set E) ∩ (fun x ↦ |ũ x|) ⁻¹' Ici (((n : ℝ) + 1)⁻¹)
        ∩ closedBall 0 R) :=
      (isCompact_closedBall (0 : E) R).inter_left hK1
    refine mem_zero_of_ae_eq_zero_compl_isCompact hp' (U n) hK ?_ ?_
    · rintro x ⟨⟨hxc, hx⟩, -⟩
      rw [closure_eq_interior_union_frontier, Ω.isOpen.interior_eq] at hxc
      rcases hxc with hxΩ | hxf
      · exact hxΩ
      · exfalso
        have h1 : ((n : ℝ) + 1)⁻¹ ≤ |ũ x| := hx
        rw [h0 hxf, Pi.zero_apply, abs_zero] at h1
        exact absurd h1 (not_le.2 (inv_pos.2 (hcpos n)))
    · filter_upwards [hUũ n, ae_restrict_mem hΩm] with x hx hxΩ hxK
      rw [hx]
      by_cases hxR : R < ‖x‖
      · rw [hR x hxR, hG0]
      · have hxb : x ∈ closedBall (0 : E) R := by
          rw [mem_closedBall_zero_iff]
          exact not_lt.1 hxR
        have hlt : ¬ ((n : ℝ) + 1)⁻¹ ≤ |ũ x| := fun h ↦ hxK ⟨⟨subset_closure hxΩ, h⟩, hxb⟩
        have h1 : |ũ x| ≤ 1 / ((n : ℝ) + 1) := by rw [one_div]; exact (not_le.1 hlt).le
        exact hGzero n _ ((le_div_iff₀ (hcpos n)).1 h1)
  -- (b) `u_n → ũ` in `L^p(Ω)`
  have hL0 : Tendsto (fun n ↦ eLpNorm ((fun x ↦ G n (ũ x)) - ũ) p (μ.restrict (Ω : Set E)))
      atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp' (bound := fun x ↦ M * ‖ũ x‖)
      (fun n ↦ (hGc n).continuous.comp_aestronglyMeasurable hum) hum (hũp.norm.const_mul M)
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · simpa [Real.norm_eq_abs] using hGle n (ũ x)
    · by_cases hx : ũ x = 0
      · simp [hx, hG0]
      · exact tendsto_atTop_of_eventually_const (i₀ := ⌈2 / |ũ x|⌉₊) fun n hn ↦
          hGid n _ (hev _ hx n hn).le
  -- (b') `∇u_n = G_n'(ũ) ∇u → {ũ ≠ 0}.indicator ∇u` in `L^p(Ω)`
  have hdU : ∀ n i, (weakDeriv (U n) (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ deriv (G n) (ũ x) * weakDeriv u (MultiIndexLE.single i) x := fun n i ↦
    (weakDeriv_single_ae_eq_of_fn_ae_eq_comp (hGc n) (hGM n) (hU n) i).trans
      (hu.mono fun x hx ↦ by dsimp only; rw [hx])
  have hind : AEStronglyMeasurable (fun x ↦ if ũ x = 0 then (0 : ℝ) else 1)
      (μ.restrict (Ω : Set E)) := by
    have hm : Measurable fun t : ℝ ↦ if t = 0 then (0 : ℝ) else 1 :=
      Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const
    exact (hm.comp_aemeasurable hum.aemeasurable).aestronglyMeasurable
  have hLi : ∀ i, Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ deriv (G n) (ũ x) * weakDeriv u (MultiIndexLE.single i) x)
        - fun x ↦ (if ũ x = 0 then (0 : ℝ) else 1) * weakDeriv u (MultiIndexLE.single i) x) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
    intro i
    refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp'
      (bound := fun x ↦ M * ‖weakDeriv u (MultiIndexLE.single i) x‖)
      (fun n ↦ (((hGc n).continuous_deriv le_rfl).comp_aestronglyMeasurable hum).mul
        (Lp.aestronglyMeasurable _))
      (hind.mul (Lp.aestronglyMeasurable _)) ((Lp.memLp _).norm.const_mul M)
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hGM n _) (norm_nonneg _)
    · by_cases hx : ũ x = 0
      · simp [hx, hGd0]
      · simp only [hx, ite_false]
        exact tendsto_atTop_of_eventually_const (i₀ := ⌈2 / |ũ x|⌉₊) fun n hn ↦ by
          rw [hGd1 n _ (hev _ hx n hn)]
  -- the limits, as elements of `L^p(Ω)`
  have hHp : ∀ i, MemLp (fun x ↦ (if ũ x = 0 then (0 : ℝ) else 1)
      * weakDeriv u (MultiIndexLE.single i) x) p (μ.restrict (Ω : Set E)) := fun i ↦
    (Lp.memLp (weakDeriv u (MultiIndexLE.single i))).of_le (hind.mul (Lp.aestronglyMeasurable _))
      (Eventually.of_forall fun x ↦ by
        rw [norm_mul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        split_ifs <;> simp)
  have hT0 : Tendsto (fun n ↦ weakDeriv (U n) 0) atTop (𝓝 (hũp.toLp ũ)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
    exact hL0.congr fun n ↦ (eLpNorm_congr_ae ((hUũ n).sub (Filter.EventuallyEq.refl _ _))).symm
  have hTi : ∀ i, Tendsto (fun n ↦ weakDeriv (U n) (MultiIndexLE.single i)) atTop
      (𝓝 ((hHp i).toLp _)) := fun i ↦ by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
    exact (hLi i).congr fun n ↦
      (eLpNorm_congr_ae ((hdU n i).sub (Filter.EventuallyEq.refl _ _))).symm
  -- (c) `(u_n)` is Cauchy in `W^{1,p}(Ω)`
  have hnorm : ∀ n m, ‖U n - U m‖
      ≤ (‖weakDeriv (U n) 0 - hũp.toLp ũ‖
          + ∑ i, ‖weakDeriv (U n) (MultiIndexLE.single i) - (hHp i).toLp _‖)
        + (‖weakDeriv (U m) 0 - hũp.toLp ũ‖
          + ∑ i, ‖weakDeriv (U m) (MultiIndexLE.single i) - (hHp i).toLp _‖) := by
    intro n m
    refine (norm_le_sum_norm_weakDeriv (U n - U m)).trans ?_
    rw [MultiIndexLE.sum_univ_one]
    have e : ∀ α, weakDeriv (U n - U m) α = weakDeriv (U n) α - weakDeriv (U m) α := fun _ ↦ rfl
    simp only [e]
    have key : ∀ (a c z : Lp ℝ p (μ.restrict (Ω : Set E))), ‖a - c‖ ≤ ‖a - z‖ + ‖c - z‖ :=
      fun a c z ↦ by rw [← sub_sub_sub_cancel_right a c z]; exact norm_sub_le _ _
    calc ‖weakDeriv (U n) 0 - weakDeriv (U m) 0‖
          + ∑ i, ‖weakDeriv (U n) (MultiIndexLE.single i) - weakDeriv (U m) (MultiIndexLE.single i)‖
        ≤ (‖weakDeriv (U n) 0 - hũp.toLp ũ‖ + ‖weakDeriv (U m) 0 - hũp.toLp ũ‖)
          + ∑ i, (‖weakDeriv (U n) (MultiIndexLE.single i) - (hHp i).toLp _‖
            + ‖weakDeriv (U m) (MultiIndexLE.single i) - (hHp i).toLp _‖) :=
          add_le_add (key _ _ _) (Finset.sum_le_sum fun i _ ↦ key _ _ _)
      _ = _ := by rw [Finset.sum_add_distrib]; ring
  have he : Tendsto (fun n ↦ ‖weakDeriv (U n) 0 - hũp.toLp ũ‖
      + ∑ i, ‖weakDeriv (U n) (MultiIndexLE.single i) - (hHp i).toLp _‖) atTop (𝓝 0) := by
    have h1 := tendsto_iff_norm_sub_tendsto_zero.1 hT0
    have h2 : ∀ i, Tendsto (fun n ↦ ‖weakDeriv (U n) (MultiIndexLE.single i) - (hHp i).toLp _‖)
        atTop (𝓝 0) := fun i ↦ tendsto_iff_norm_sub_tendsto_zero.1 (hTi i)
    simpa using h1.add (tendsto_finsetSum Finset.univ fun i _ ↦ h2 i)
  have hcauchy : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 he) (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h1 := hN m hm
    have h2 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1 h2
    rw [dist_eq_norm]
    linarith [hnorm m n]
  -- (d) the limit lies in `W_0^{1,p}(Ω)` and is `u`
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hVmem : V ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ :=
    SobolevMultiIndexZero.isClosed.mem_of_tendsto hV (Eventually.of_forall hUmem)
  have hV0 : weakDeriv V 0 = hũp.toLp ũ :=
    tendsto_nhds_unique (((weakDerivL ℝ b 1 p Ω μ 0).continuous.tendsto V).comp hV) hT0
  have hVu : V = u := by
    refine ext_of_fn_ae_eq ?_
    have h1 : (weakDeriv V 0 : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)] ũ := by
      rw [hV0]
      exact hũp.coeFn_toLp
    exact h1.trans hu.symm
  rw [← hVu]
  exact hVmem

/-- **A continuous function that vanishes on the boundary lies in $W_0^{1,p}(\Omega)$.** Let
$\Omega \subseteq E$ be open, let $1 \le p < \infty$, and let $u \in W^{1,p}(\Omega)$ be
real-valued. Suppose that the function of $u$ equals, almost everywhere on $\Omega$, a function
$\tilde u$ that is continuous on $\bar\Omega$ and vanishes on $\partial\Omega$. Then
$u \in W_0^{1,p}(\Omega)$. This is Theorem 9.17, (i) ⇒ (ii), of [brezis2011functional], on any
open set: by Remark 19, this direction needs no smoothness of $\Omega$.

The case of bounded support is
`SobolevMultiIndex.mem_zero_of_continuousOn_closure_of_eqOn_frontier_of_forall_eq_zero`. In
general, $\zeta_n u \to u$ in $W^{1,p}(\Omega)$ for the cut-off sequence $\zeta_n$
(`SobolevMultiIndex.tendsto_cutoff_smul`), each $\zeta_n u$ has the representative
$\zeta_n \tilde u$ of bounded support, and $W_0^{1,p}(\Omega)$ is closed. -/
theorem mem_zero_of_continuousOn_closure_of_eqOn_frontier (hp' : p ≠ ⊤)
    (u : SobolevMultiIndex ℝ b 1 p Ω μ) {ũ : E → ℝ} (hu : fn u =ᵐ[μ.restrict (Ω : Set E)] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (h0 : EqOn ũ 0 (frontier Ω)) :
    u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  obtain ⟨ζ, hζ, hζ1, hζs, hζ01⟩ := exists_contDiff_eqOn_one_closedBall_one E
  obtain ⟨v, hv, -, hvt⟩ :=
    tendsto_cutoff_smul hp' hζ hζ01 hζ1 (hζs.trans ball_subset_closedBall) u
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hvt (Eventually.of_forall fun n ↦ ?_)
  refine mem_zero_of_continuousOn_closure_of_eqOn_frontier_of_forall_eq_zero hp' (v n)
    (ũ := fun x ↦ ζ (((n : ℝ) + 1)⁻¹ • x) * ũ x) ?_ ?_ ?_ (R := 2 * ((n : ℝ) + 1)) ?_
  · exact (hv n).trans (hu.mono fun x hx ↦ by dsimp only; rw [hx])
  · exact (hζ.continuous.comp (continuous_const.smul continuous_id)).continuousOn.mul hc
  · intro x hx
    simp [h0 hx]
  · intro x hx
    have hζx : ζ (((n : ℝ) + 1)⁻¹ • x) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
      have h2 : ‖((n : ℝ) + 1)⁻¹ • x‖ < 2 := by simpa using hζs h
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity),
        inv_mul_lt_iff₀ (by positivity)] at h2
      linarith
    simp [hζx]

end SobolevMultiIndex

/-- **Theorem 9.17, (i) ⇒ (ii)**, on an open set $\Omega \subseteq \mathbb{R}^N$. Let
$1 \le p < \infty$ and let $u \in W^{1,p}(\Omega)$. Suppose that the function of $u$ equals,
almost everywhere on $\Omega$, a function $\tilde u$ that is continuous on $\bar\Omega$ with
$\tilde u = 0$ on $\partial\Omega$. Then $u \in W_0^{1,p}(\Omega)$. No smoothness of $\Omega$ is
needed. This is Theorem 9.17, (i) ⇒ (ii), of [brezis2011functional], together with Remark 19.

This is `SobolevMultiIndex.mem_zero_of_continuousOn_closure_of_eqOn_frontier` on
`SobolevEuclidean`. It places a classical solution of the Dirichlet problem in $H^1_0(\Omega)$
(§9.5, Example 1, Step A). -/
theorem SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier {N : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (hp' : p ≠ ⊤) (u : SobolevEuclidean N 1 p Ω)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (h0 : EqOn ũ 0 (frontier Ω)) :
    u ∈ SobolevEuclideanZero N 1 p Ω :=
  SobolevMultiIndex.mem_zero_of_continuousOn_closure_of_eqOn_frontier hp' u hu hc h0

end ContinuousBoundary








/-! ### Transfer of membership in $W_0^{1,p}$: open subsets and changes of variables -/

section Transfer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Ω Ω' : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndex

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [CompleteSpace F] [Fact (1 ≤ p)]
  [μ.IsAddHaarMeasure] in
/-- Let $\Omega' \subseteq \Omega$ be open, let $g$ vanish outside $\Omega'$, and let $f$ vanish
almost everywhere on $\Omega \setminus \Omega'$. Then $\|g - f\|_{L^p(\Omega)} = \|g -
f\|_{L^p(\Omega')}$. -/
theorem _root_.MeasureTheory.eLpNorm_sub_restrict_eq_of_eq_zero_compl {g f : E → F} (h : Ω' ≤ Ω)
    (hg : ∀ x ∉ (Ω' : Set E), g x = 0)
    (hf : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∉ (Ω' : Set E) → f x = 0) :
    eLpNorm (g - f) p (μ.restrict (Ω : Set E)) = eLpNorm (g - f) p (μ.restrict (Ω' : Set E)) := by
  have e : (g - f) =ᵐ[μ.restrict (Ω : Set E)] (Ω' : Set E).indicator (g - f) := by
    filter_upwards [hf] with x hx
    by_cases hxΩ' : x ∈ (Ω' : Set E)
    · rw [Set.indicator_of_mem hxΩ']
    · rw [Set.indicator_of_notMem hxΩ', Pi.sub_apply, hg x hxΩ', hx hxΩ', sub_zero]
  rw [eLpNorm_congr_ae e,
    eLpNorm_indicator_eq_eLpNorm_restrict Ω'.isOpen.measurableSet.nullMeasurableSet,
    Measure.restrict_restrict Ω'.isOpen.measurableSet, inter_eq_left.2 h]

omit [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- **The weak derivatives of $u \in W^{k,p}(\Omega)$ vanish almost everywhere on an open subset of
$\Omega$ where $u$ does.** Let $V \subseteq \Omega$ be open, and let the function of
$u \in W^{k,p}(\Omega)$ vanish almost everywhere on $V$. Then $\partial^\alpha u = 0$ almost
everywhere on $V$ for every multi-index $\alpha$ with $|\alpha| \le k$.

On $V$, the function $0$ is a weak derivative of the function of $u$, and the weak derivative is
unique. -/
theorem weakDeriv_ae_eq_zero_of_fn_ae_eq_zero {k : ℕ} (u : SobolevMultiIndex F b k p Ω μ)
    {V : Opens E} (hV : V ≤ Ω) (hu : fn u =ᵐ[μ.restrict (V : Set E)] 0) (α : MultiIndexLE ι k) :
    (weakDeriv u α : E → F) =ᵐ[μ.restrict (V : Set E)] 0 := by
  have h1 := ((hasWeakIteratedLineDerivOn u α).mono hV).congr_ae hu (EventuallyEq.refl _ _)
  have h2 : HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) (0 : E → F) 0 V μ :=
    HasWeakIteratedLineDerivOn.zero
  exact (ae_restrict_iff' V.isOpen.measurableSet).2 (h1.ae_eq h2)

omit [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- Let $K \subseteq E$ be closed, and let the function of $u \in W^{k,p}(\Omega)$ vanish almost
everywhere on $\Omega \setminus K$. Then $\partial^\alpha u = 0$ almost everywhere on
$\Omega \setminus K$ for every multi-index $\alpha$ with $|\alpha| \le k$. -/
theorem weakDeriv_ae_eq_zero_of_fn_ae_eq_zero_compl {k : ℕ} (u : SobolevMultiIndex F b k p Ω μ)
    {K : Set E} (hK : IsClosed K) (hu : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∉ K → fn u x = 0)
    (α : MultiIndexLE ι k) :
    ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∉ K → weakDeriv u α x = 0 := by
  obtain ⟨V, hVdef⟩ : ∃ V : Opens E, V = ⟨(Ω : Set E) ∩ Kᶜ, Ω.isOpen.inter hK.isOpen_compl⟩ :=
    ⟨_, rfl⟩
  have hVs : (V : Set E) = (Ω : Set E) ∩ Kᶜ := by rw [hVdef]; rfl
  have hVΩ : V ≤ Ω := by rw [← SetLike.coe_subset_coe, hVs]; exact inter_subset_left
  have hu' : fn u =ᵐ[μ.restrict (V : Set E)] 0 := by
    rw [hVs, inter_comm, ← Measure.restrict_restrict hK.isOpen_compl.measurableSet]
    refine (ae_restrict_iff' hK.isOpen_compl.measurableSet).2 ?_
    filter_upwards [hu] with x hx hxK
    simpa using hx hxK
  have h := weakDeriv_ae_eq_zero_of_fn_ae_eq_zero u hVΩ hu' α
  rw [hVs, inter_comm, ← Measure.restrict_restrict hK.isOpen_compl.measurableSet] at h
  filter_upwards [(ae_restrict_iff' hK.isOpen_compl.measurableSet).1 h] with x hx hxK
  simpa using hx hxK

end SobolevMultiIndex

namespace SobolevMultiIndexZero

open SobolevMultiIndex

/-- **Transfer of membership in $W_0^{k,p}$ from an open subset.** Let $\Omega' \subseteq \Omega$ be
open and let $u \in W^{k,p}(\Omega)$. Suppose that the restriction of $u$ to $\Omega'$ lies in
$W_0^{k,p}(\Omega')$, and that the function of $u$ vanishes almost everywhere on
$\Omega \setminus K$ for a closed set $K$ with $K \cap \Omega \subseteq \Omega'$. Then
$u \in W_0^{k,p}(\Omega)$.

This is the step "extend by zero to $\Omega$" of the reductions by local charts in the proofs of
Theorem 9.17 and Proposition 9.18 of [brezis2011functional]. The restriction is
`SobolevMultiIndex.restrictL`. Test functions on $\Omega'$ that converge to the restriction of
$u$ are test functions on $\Omega$, and they converge to $u$ in $W^{k,p}(\Omega)$, because every
component of the difference vanishes almost everywhere on $\Omega \setminus \Omega'$. The weak
derivatives of $u$ vanish there by
`SobolevMultiIndex.weakDeriv_ae_eq_zero_of_fn_ae_eq_zero_compl`. -/
theorem mem_of_mem_restrict {k : ℕ} (h : Ω' ≤ Ω) {u : SobolevMultiIndex F b k p Ω μ}
    (hu : restrictL F b k p μ h u ∈ SobolevMultiIndexZero F b k p Ω' μ) {K : Set E}
    (hK : IsClosed K) (hKΩ : K ∩ Ω ⊆ Ω')
    (hu0 : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∉ K → fn u x = 0) :
    u ∈ SobolevMultiIndexZero F b k p Ω μ := by
  obtain ⟨w, φ, hφ, hw⟩ := exists_seq_testFunction_tendsto hu
  -- the test functions on `Ω'`, read as test functions on `Ω`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → 𝓓(Ω, F), ∀ n, (ψ n : E → F) = φ n :=
    ⟨fun n ↦ ⟨φ n, (φ n).contDiff, (φ n).hasCompactSupport, (φ n).tsupport_subset.trans h⟩,
      fun _ ↦ rfl⟩
  choose W hWT hW using fun n ↦ (ψ n).exists_mem_sobolevMultiIndex_testFunctions (b := b) (k := k)
    (p := p) (μ := μ)
  -- `u` and its derivatives vanish almost everywhere on `Ω ∖ Ω'`
  have hu0' : ∀ α : MultiIndexLE ι k, ∀ᵐ x ∂μ.restrict (Ω : Set E),
      x ∉ (Ω' : Set E) → weakDeriv u α x = 0 := fun α ↦ by
    filter_upwards [weakDeriv_ae_eq_zero_of_fn_ae_eq_zero_compl u hK hu0 α, ae_restrict_mem
      Ω.isOpen.measurableSet] with x hx hxΩ hxΩ'
    exact hx fun hxK ↦ hxΩ' (hKΩ ⟨hxK, hxΩ⟩)
  refine isClosed.mem_of_tendsto (f := W) (b := atTop) ?_
    (Eventually.of_forall fun n ↦ testFunctions_le (hWT n))
  refine tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun α ↦ ?_
  -- the classical function `c n` carrying the component `α` of `W n` and of `w n`
  set c : ℕ → E → F := fun n x ↦
    iteratedFDeriv ℝ (∑ i, α.1 i) (φ n) x (multiIndexTuple (b : ι → E) α.1) with hcdef
  have hc0 : ∀ n, ∀ x ∉ (Ω' : Set E), c n x = 0 := fun n x hx ↦
    ((φ n).iteratedFDerivApply (∑ i, α.1 i) (multiIndexTuple (b : ι → E) α.1)).eq_zero_of_notMem
      hx
  have hcW : ∀ n, (weakDeriv (W n) α : E → F) =ᵐ[μ.restrict (Ω : Set E)] c n := fun n ↦ by
    have := weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq (W n) (ψ n).contDiff (hW n) α
    rwa [hψ n] at this
  have hcw : ∀ n, (weakDeriv (w n) α : E → F) =ᵐ[μ.restrict (Ω' : Set E)] c n := fun n ↦
    weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq (w n) (φ n).contDiff (hφ n) α
  have key : ∀ n, eLpNorm ((weakDeriv (W n) α : E → F) - (weakDeriv u α : E → F)) p
        (μ.restrict (Ω : Set E))
      = eLpNorm ((weakDeriv (w n) α : E → F) - (weakDeriv (restrictL F b k p μ h u) α : E → F)) p
        (μ.restrict (Ω' : Set E)) := by
    intro n
    rw [eLpNorm_congr_ae ((hcW n).sub (EventuallyEq.refl _ _)),
      eLpNorm_sub_restrict_eq_of_eq_zero_compl h (hc0 n) (hu0' α)]
    exact eLpNorm_congr_ae ((hcw n).symm.sub (weakDeriv_restrictL h u α).symm)
  simp_rw [key]
  exact tendsto_eLpNorm_weakDeriv_sub hw α

/-- **A change of variables preserves $W_0^{1,p}$.** Let $1 \le p < \infty$, let
$H : \Omega' \to \Omega$ be a $C^1$ diffeomorphism between open sets with bounded Jacobians, and
let $u \in W_0^{1,p}(\Omega)$. Then the transfer $u \circ H$ lies in $W_0^{1,p}(\Omega')$.

The hypothesis on $H$ is `IsDiffeoOnWithBoundedJacobian`, and the transfer is
`SobolevMultiIndex.compDiffeoL`. This is the step "transfer along the chart" of the reductions
by local charts in the proofs of Theorem 9.17 and Proposition 9.18 of [brezis2011functional].
Test functions $\varphi_n \to u$ transfer to $\varphi_n \circ H$, which vanish on $\Omega'$
outside the compact set $H^{-1}(\operatorname{supp} \varphi_n)$. So they lie in
$W_0^{1,p}(\Omega')$ by Lemma 9.5 (`SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact`),
and the transfer is continuous. -/
theorem compDiffeoL_mem (hp' : p ≠ ⊤) {H Hinv : E → E} {M : ℝ}
    (hH : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) {u : SobolevMultiIndex F b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero F b 1 p Ω μ) :
    compDiffeoL F b p μ hH u ∈ SobolevMultiIndexZero F b 1 p Ω' μ := by
  obtain ⟨w, φ, hφ, hw⟩ := exists_seq_testFunction_tendsto hu
  have ht : Tendsto (fun n ↦ compDiffeoL F b p μ hH (w n)) atTop
      (𝓝 (compDiffeoL F b p μ hH u)) :=
    ((compDiffeoL F b p μ hH).continuous.tendsto u).comp hw
  refine isClosed.mem_of_tendsto ht (Eventually.of_forall fun n ↦ ?_)
  have hmaps : MapsTo Hinv Ω Ω' := hH.invOn.1.mapsTo hH.bijOn.surjOn
  have hK : IsCompact (Hinv '' tsupport (φ n)) :=
    (φ n).hasCompactSupport.image_of_continuousOn
      (hH.contDiffOn_invFun.continuousOn.mono (φ n).tsupport_subset)
  have hKΩ' : Hinv '' tsupport (φ n) ⊆ Ω' :=
    (image_mono (φ n).tsupport_subset).trans hmaps.image_subset
  refine mem_zero_of_ae_eq_zero_compl_isCompact hp' _ hK hKΩ' ?_
  filter_upwards [fn_compDiffeoL hH (w n), ae_restrict_mem Ω'.isOpen.measurableSet,
    hH.ae_comp_restrict (P := fun x ↦ fn (w n) x = φ n x) (hφ n)] with y hy hyΩ' hyφ hyK
  rw [hy, hyφ]
  by_contra hne
  apply hyK
  refine ⟨H y, subset_tsupport _ hne, hH.invOn.1 hyΩ'⟩

end SobolevMultiIndexZero

end Transfer

/-! ### A smooth compactly supported factor preserves $W_0^{1,p}$ -/

section LpAux

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- **$L^p$ convergence to $0$ is preserved by a bounded factor.** Let $a$ be almost everywhere
strongly measurable with $|a| \le M$, and let $f_n$ be almost everywhere strongly measurable
real functions with $\|f_n\|_{L^p} \to 0$. Then $\|f_n a\|_{L^p} \to 0$. -/
theorem MeasureTheory.tendsto_eLpNorm_mul_of_tendsto {f : ℕ → X → ℝ} {a : X → ℝ}
    (ha : AEStronglyMeasurable a ν) {M : ℝ} (hM : ∀ x, |a x| ≤ M)
    (hfm : ∀ n, AEStronglyMeasurable (f n) ν)
    (hf : Tendsto (fun n ↦ eLpNorm (f n) p ν) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ f n x * a x) p ν) atTop (𝓝 0) := by
  have hbd : ∀ n, eLpNorm (fun x ↦ f n x * a x) p ν ≤ ENNReal.ofReal M * eLpNorm (f n) p ν := by
    intro n
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := fun x ↦ f n x * a x) (g := f n) (c := M)
      ((hfm n).mul ha) (Eventually.of_forall fun x ↦ ?_) p
    change ‖f n x * a x‖ ≤ M * ‖f n x‖
    rw [norm_mul, mul_comm, Real.norm_eq_abs (a x)]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
  simpa using ENNReal.Tendsto.const_mul hf (Or.inr ENNReal.ofReal_ne_top)

/-- Let $1 \le p \le \infty$. Let $a$ and $c$ be almost everywhere strongly measurable with
$|a| \le M$ and $|c| \le M$, and let $f_n$, $g_n$ be almost everywhere strongly measurable real
functions with $\|f_n\|_{L^p} \to 0$ and $\|g_n\|_{L^p} \to 0$. Then
$\|f_n a + g_n c\|_{L^p} \to 0$. -/
theorem MeasureTheory.tendsto_eLpNorm_mul_add_mul_of_tendsto {f g : ℕ → X → ℝ}
    {a c : X → ℝ} (ha : AEStronglyMeasurable a ν) (hc : AEStronglyMeasurable c ν) {M : ℝ}
    (hMa : ∀ x, |a x| ≤ M) (hMc : ∀ x, |c x| ≤ M) (hfm : ∀ n, AEStronglyMeasurable (f n) ν)
    (hgm : ∀ n, AEStronglyMeasurable (g n) ν)
    (hf : Tendsto (fun n ↦ eLpNorm (f n) p ν) atTop (𝓝 0))
    (hg : Tendsto (fun n ↦ eLpNorm (g n) p ν) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ f n x * a x + g n x * c x) p ν) atTop (𝓝 0) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hbd : ∀ n, eLpNorm (fun x ↦ f n x * a x + g n x * c x) p ν
      ≤ eLpNorm (fun x ↦ f n x * a x) p ν + eLpNorm (fun x ↦ g n x * c x) p ν := fun n ↦
    eLpNorm_add_le (f := fun x ↦ f n x * a x) (g := fun x ↦ g n x * c x) hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
  simpa using (tendsto_eLpNorm_mul_of_tendsto ha hMa hfm hf).add
    (tendsto_eLpNorm_mul_of_tendsto hc hMc hgm hg)

end LpAux

section SmulContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Ω Ω' : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

open SobolevMultiIndex

omit [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- **The Leibniz rule for a smooth factor on $W^{1,p}(\Omega)$.** Let $u, v \in W^{1,p}(\Omega)$ be
real-valued, and let $\alpha$ be a smooth real function on $E$. If the function of $v$ equals
$u \alpha$ almost everywhere on $\Omega$, then for every $i$,
$$\partial_i v = (\partial_i u) \, \alpha + u \, D\alpha(x) b_i$$
almost everywhere on $\Omega$.

The proof combines `HasWeakIteratedLineDerivOn.mul_contDiff` with the uniqueness of the weak
derivative. -/
theorem SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_mul_contDiff {α : E → ℝ}
    (hα : ContDiff ℝ ∞ α) {u v : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hv : fn v =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ fn u x * α x) (i : ι) :
    (weakDeriv v (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ weakDeriv u (MultiIndexLE.single i) x * α x + fn u x * fderiv ℝ α x (b i) := by
  have h1 : HasWeakIteratedLineDerivOn ![b i] (fn v) (weakDeriv v (MultiIndexLE.single i)) Ω μ :=
    (hasWeakIteratedLineDerivOn v (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm (b : ι → E) i)
  have h2 := ((hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).mul_contDiff rfl hα
  have h3 : HasWeakIteratedLineDerivOn ![b i] (fn v)
      (fun x ↦ weakDeriv u (MultiIndexLE.single i) x * α x + fn u x * fderiv ℝ α x (b i)) Ω μ := by
    refine h2.congr_ae hv.symm (Eventually.of_forall fun x ↦ ?_)
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h3)

omit [FiniteDimensional ℝ E] [Fact (1 ≤ p)] [μ.IsAddHaarMeasure] in
/-- Let $\Omega' \subseteq \Omega$ be open, let $u, w \in W^{1,p}(\Omega)$ and
$v, z \in W^{1,p}(\Omega')$ be real-valued, and let $\alpha$ be a real function. Let $\varphi$
be a test function on $\Omega$ equal to the function of $w$ almost everywhere on $\Omega$, and
let $\psi = \varphi \alpha$ be a test function on $\Omega'$ equal to the function of $z$ almost
everywhere on $\Omega'$. If the function of $v$ equals $u \alpha$ almost everywhere on
$\Omega'$, then $z - v = (w - u) \alpha$ almost everywhere on $\Omega'$.

This is a step of the proof of `SobolevMultiIndexZero.mul_contDiff_mem`, where $z$ is the $n$-th
approximant. -/
theorem SobolevMultiIndexZero.fn_sub_ae_eq_mul_aux (h : Ω' ≤ Ω) {α : E → ℝ}
    {u w : SobolevMultiIndex ℝ b 1 p Ω μ} {v z : SobolevMultiIndex ℝ b 1 p Ω' μ} {φ : 𝓓(Ω, ℝ)}
    {ψ : 𝓓(Ω', ℝ)} (hφ : fn w =ᵐ[μ.restrict (Ω : Set E)] φ)
    (hψ : (ψ : E → ℝ) = fun x ↦ φ x * α x) (hz : fn z =ᵐ[μ.restrict (Ω' : Set E)] ψ)
    (hv : fn v =ᵐ[μ.restrict (Ω' : Set E)] fun x ↦ fn u x * α x) :
    (weakDeriv z 0 : E → ℝ) - (weakDeriv v 0 : E → ℝ) =ᵐ[μ.restrict (Ω' : Set E)]
      fun x ↦ (fn w x - fn u x) * α x := by
  have hle : μ.restrict (Ω' : Set E) ≤ μ.restrict (Ω : Set E) := Measure.restrict_mono h le_rfl
  filter_upwards [hz, hv, hφ.filter_mono (ae_mono hle)] with x h1 h2 h3
  rw [hψ] at h1
  simp only [Pi.sub_apply, weakDeriv_zero, h1, h2, h3]
  ring

/-- Let $\Omega' \subseteq \Omega$ be open, let $u, w \in W^{1,p}(\Omega)$ and
$v, z \in W^{1,p}(\Omega')$ be real-valued, and let $\alpha$ be a smooth real function. Let
$\varphi$ be a test function on $\Omega$ equal to the function of $w$ almost everywhere on
$\Omega$, and let $\psi = \varphi \alpha$ be a test function on $\Omega'$ equal to the function
of $z$ almost everywhere on $\Omega'$. If the function of $v$ equals $u \alpha$ almost
everywhere on $\Omega'$, then for every $i$,
$$\partial_i z - \partial_i v = (\partial_i w - \partial_i u) \, \alpha + (w - u) \, D\alpha(x)
  b_i$$
almost everywhere on $\Omega'$.

This is a step of the proof of `SobolevMultiIndexZero.mul_contDiff_mem`, where $z$ is the $n$-th
approximant. -/
theorem SobolevMultiIndexZero.weakDeriv_single_sub_ae_eq_mul_aux (h : Ω' ≤ Ω) {α : E → ℝ}
    (hα : ContDiff ℝ ∞ α) {u w : SobolevMultiIndex ℝ b 1 p Ω μ}
    {v z : SobolevMultiIndex ℝ b 1 p Ω' μ} {φ : 𝓓(Ω, ℝ)} {ψ : 𝓓(Ω', ℝ)}
    (hφ : fn w =ᵐ[μ.restrict (Ω : Set E)] φ) (hψ : (ψ : E → ℝ) = fun x ↦ φ x * α x)
    (hz : fn z =ᵐ[μ.restrict (Ω' : Set E)] ψ)
    (hv : fn v =ᵐ[μ.restrict (Ω' : Set E)] fun x ↦ fn u x * α x) (i : ι) :
    (weakDeriv z (MultiIndexLE.single i) : E → ℝ) - (weakDeriv v (MultiIndexLE.single i) : E → ℝ)
      =ᵐ[μ.restrict (Ω' : Set E)] fun x ↦
        (weakDeriv w (MultiIndexLE.single i) x - weakDeriv u (MultiIndexLE.single i) x) * α x
          + (fn w x - fn u x) * fderiv ℝ α x (b i) := by
  have hle : μ.restrict (Ω' : Set E) ≤ μ.restrict (Ω : Set E) := Measure.restrict_mono h le_rfl
  have hu' : fn v =ᵐ[μ.restrict (Ω' : Set E)]
      fun x ↦ fn (restrictL ℝ b 1 p μ h u) x * α x := by
    filter_upwards [hv, fn_restrictL h u] with x h1 h2
    rw [h1, h2]
  have hvD := weakDeriv_single_ae_eq_of_fn_ae_eq_mul_contDiff hα hu' i
  have hzD := SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hz i
  have hwD := (SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hφ i).filter_mono
    (ae_mono hle)
  have hprod : ∀ x, fderiv ℝ (ψ : E → ℝ) x (b i)
      = fderiv ℝ (φ : E → ℝ) x (b i) * α x + φ x * fderiv ℝ α x (b i) := fun x ↦ by
    rw [hψ, fderiv_fun_mul (φ.contDiff.differentiable (by simp) x) (hα.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  filter_upwards [hzD, hvD, hwD, hφ.filter_mono (ae_mono hle), weakDeriv_restrictL h u
    (MultiIndexLE.single i), fn_restrictL h u] with x h1 h2 h3 h4 h5 h6
  simp only [Pi.sub_apply, h1, h2, hprod x, h5, h6, ← h3, ← h4]
  ring

/-- **A smooth compactly supported factor preserves $W_0^{1,p}$**, with restriction to an open
subset. Let $\Omega' \subseteq \Omega$ be open, and let $\alpha$ be a smooth real function with
compact support such that $\operatorname{supp} \alpha \cap \Omega \subseteq \Omega'$. Let
$u \in W_0^{1,p}(\Omega)$ be real-valued, and let $v \in W^{1,p}(\Omega')$ have the function
$u \alpha$ almost everywhere on $\Omega'$. Then $v \in W_0^{1,p}(\Omega')$.

This is the step "$\theta u \in W_0^{1,p}(U \cap \Omega)$" of the reduction by local charts in
the proof of Theorem 9.17, (ii) ⇒ (i), of [brezis2011functional]. For test functions
$\varphi_n \to u$, the test functions $\varphi_n \alpha$ are supported in $\Omega'$ and converge
to $v$ in $W^{1,p}(\Omega')$. Indeed $|(\varphi_n - u) \alpha| \le M |\varphi_n - u|$, and
$\partial_i(\varphi_n \alpha) - \partial_i v = (\partial_i \varphi_n - \partial_i u) \alpha +
(\varphi_n - u) \partial_i \alpha$ by the Leibniz rule
(`SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_mul_contDiff`). -/
theorem SobolevMultiIndexZero.mul_contDiff_mem (h : Ω' ≤ Ω) {α : E → ℝ} (hα : ContDiff ℝ ∞ α)
    (hαc : HasCompactSupport α) (hαΩ : tsupport α ∩ Ω ⊆ Ω') {u : SobolevMultiIndex ℝ b 1 p Ω μ}
    (hu : u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ) {v : SobolevMultiIndex ℝ b 1 p Ω' μ}
    (hv : fn v =ᵐ[μ.restrict (Ω' : Set E)] fun x ↦ fn u x * α x) :
    v ∈ SobolevMultiIndexZero ℝ b 1 p Ω' μ := by
  have hle : μ.restrict (Ω' : Set E) ≤ μ.restrict (Ω : Set E) := Measure.restrict_mono h le_rfl
  -- the bounds on `α` and `∂_i α`
  obtain ⟨M₀, hM₀⟩ := hαc.exists_bound_of_continuous hα.continuous
  obtain ⟨M₁, hM₁⟩ := (hαc.fderiv ℝ).exists_bound_of_continuous (hα.continuous_fderiv (by simp))
  have hMa : ∀ x, |α x| ≤ M₀ + M₁ * ∑ i, ‖b i‖ := fun x ↦ by
    have := hM₀ x
    rw [Real.norm_eq_abs] at this
    have h2 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
    have h3 : 0 ≤ ∑ i, ‖b i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    nlinarith
  have hMd : ∀ i x, |fderiv ℝ α x (b i)| ≤ M₀ + M₁ * ∑ i, ‖b i‖ := fun i x ↦ by
    have h1 : ‖fderiv ℝ α x (b i)‖ ≤ M₁ * ‖b i‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hM₁ x) (norm_nonneg _))
    have h2 : ‖b i‖ ≤ ∑ j, ‖b j‖ :=
      Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun j _ ↦ norm_nonneg _) (Finset.mem_univ i)
    have h3 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
    have h4 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
    rw [← Real.norm_eq_abs]
    nlinarith
  -- the approximating test functions `φ_n α` on `Ω'`
  obtain ⟨w, φ, hφ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hu
  have hψ : ∀ n, ∃ ψ : 𝓓(Ω', ℝ), (ψ : E → ℝ) = fun x ↦ φ n x * α x := fun n ↦
    ⟨⟨fun x ↦ φ n x * α x, (φ n).contDiff.mul hα, (φ n).hasCompactSupport.mul_right,
      fun x hx ↦ hαΩ ⟨tsupport_mul_subset_right hx, (φ n).tsupport_subset
        (tsupport_mul_subset_left hx)⟩⟩, rfl⟩
  choose ψ hψ using hψ
  choose z hzT hz using fun n ↦ (ψ n).exists_mem_sobolevMultiIndex_testFunctions (b := b) (p := p)
    (μ := μ)
  -- `z_n → v` in `W^{1,p}(Ω')`
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto (f := z) (b := atTop) ?_
    (Eventually.of_forall fun n ↦ SobolevMultiIndexZero.testFunctions_le (hzT n))
  refine SobolevMultiIndex.tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun β ↦ ?_
  have hf : Tendsto (fun n ↦ eLpNorm (fun x ↦ fn (w n) x - fn u x) p (μ.restrict (Ω' : Set E)))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_eLpNorm_fn_sub hw)
      (fun _ ↦ zero_le) fun n ↦ eLpNorm_mono_measure _ hle
  have hfm : ∀ n, AEStronglyMeasurable (fun x ↦ fn (w n) x - fn u x) (μ.restrict (Ω' : Set E)) :=
    fun n ↦ ((memLp (w n)).aestronglyMeasurable.sub (memLp u).aestronglyMeasurable).mono_measure
      hle
  rcases MultiIndexLE.eq_zero_or_exists_eq_single β with rfl | ⟨i, rfl⟩
  · refine (tendsto_eLpNorm_mul_of_tendsto hα.continuous.aestronglyMeasurable hMa hfm hf).congr
      fun n ↦ ?_
    exact (eLpNorm_congr_ae (SobolevMultiIndexZero.fn_sub_ae_eq_mul_aux h (hφ n) (hψ n) (hz n)
      hv)).symm
  · have hg : Tendsto (fun n ↦ eLpNorm (fun x ↦ weakDeriv (w n) (MultiIndexLE.single i) x
        - weakDeriv u (MultiIndexLE.single i) x) p (μ.restrict (Ω' : Set E))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_eLpNorm_weakDeriv_sub hw (MultiIndexLE.single i)) (fun _ ↦ zero_le)
        fun n ↦ eLpNorm_mono_measure _ hle
    have hgm : ∀ n, AEStronglyMeasurable (fun x ↦ weakDeriv (w n) (MultiIndexLE.single i) x
        - weakDeriv u (MultiIndexLE.single i) x) (μ.restrict (Ω' : Set E)) := fun n ↦
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)).mono_measure hle
    refine (tendsto_eLpNorm_mul_add_mul_of_tendsto hα.continuous.aestronglyMeasurable
      (((hα.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable) hMa
      (hMd i) hgm hfm hg hf).congr fun n ↦ ?_
    exact (eLpNorm_congr_ae (SobolevMultiIndexZero.weakDeriv_single_sub_ae_eq_mul_aux h hα (hφ n)
      (hψ n) (hz n) hv i)).symm

end SmulContDiff

/-! ### Proposition 9.18, (iii) ⇒ (i): the computation on $Q_+$ -/

section CubePos

variable {d : ℕ}

/-- The upper half cylinder $Q_+$, as an open set of $\mathbb{R}^{d+1}$ of type `Opens`, the type on
which the Sobolev spaces are defined. -/
def unitChartCubePosOpens (d : ℕ) : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨unitChartCubePos d, isOpen_unitChartCubePos⟩

/-- The underlying set of `unitChartCubePosOpens d` is $Q_+$, that is `unitChartCubePos d`. -/
@[simp]
theorem coe_unitChartCubePosOpens : (unitChartCubePosOpens d : Set _) = unitChartCubePos d := rfl

/-- The upper half cylinder lies in the cylinder: $Q_+ \subseteq Q$. -/
theorem unitChartCubePosOpens_le : unitChartCubePosOpens d ≤ unitChartCubeOpens d :=
  unitChartCubePos_subset

/-- The closure of $Q_+$ lies in the closed half space $\{x : x_N \ge 0\}$. -/
theorem closure_unitChartCubePos_subset :
    closure (unitChartCubePos d) ⊆ {x | 0 ≤ x (Fin.last d)} :=
  closure_minimal (fun _ hx ↦ hx.2.le) (isClosed_le continuous_const continuous_apply_last)

/-- **One-sided mollifiers.** In $\mathbb{R}^N$, $N = d + 1$, there are functions $\rho_n$,
$n \in \mathbb{N}$, that are smooth, nonnegative, integrable, with compact support and
$\int \rho_n = 1$, such that
$$\operatorname{supp} \rho_n \subseteq \bar B\big(0, 1/(n+1)\big) \quad\text{and}\quad x_N \ge
  \frac{1}{2(n+1)} \text{ for every } x \in \operatorname{supp} \rho_n.$$
These are the mollifiers of the proof of Proposition 9.18, (iii) ⇒ (i), in §9.4 of
[brezis2011functional], with "$\operatorname{supp} \rho_n \subset \{1/(2n) < x_N < 1/n\}$".

The functions $\rho_n$ are normalized bumps supported in the ball of radius $1/(4(n+1))$ around
$(3/(4(n+1))) e_N$. -/
theorem exists_oneSided_mollifiers :
    ∃ ρ : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      (∀ n, ContDiff ℝ ∞ (ρ n)) ∧ (∀ n x, 0 ≤ ρ n x) ∧ (∀ n, HasCompactSupport (ρ n)) ∧
      (∀ n, Integrable (ρ n) volume) ∧ (∀ n, ∫ x, ρ n x = 1) ∧
      (∀ n, tsupport (ρ n) ⊆ closedBall 0 (1 / ((n : ℝ) + 1))) ∧
      (∀ n x, x ∈ tsupport (ρ n) → 1 / (2 * ((n : ℝ) + 1)) ≤ x (Fin.last d)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → EuclideanSpace ℝ (Fin (d + 1)),
      c = fun n : ℕ ↦ (3 / (4 * ((n : ℝ) + 1))) • EuclideanSpace.single (Fin.last d) (1 : ℝ) :=
    ⟨_, rfl⟩
  have hcnorm : ∀ n, ‖c n‖ = 3 / (4 * ((n : ℝ) + 1)) := fun n ↦ by
    rw [hc]
    simp only [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hclast : ∀ n, c n (Fin.last d) = 3 / (4 * ((n : ℝ) + 1)) := fun n ↦ by
    rw [hc]
    simp
  obtain ⟨φ, hφ⟩ : ∃ φ : (n : ℕ) → ContDiffBump (c n), ∀ n,
      (φ n).rOut = 1 / (4 * ((n : ℝ) + 1)) :=
    ⟨fun n ↦ ⟨1 / (8 * ((n : ℝ) + 1)), 1 / (4 * ((n : ℝ) + 1)), by positivity, by
      rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
      linarith⟩, fun n ↦ rfl⟩
  have htsupp : ∀ n, tsupport ((φ n).normed volume) = closedBall (c n) (1 / (4 * ((n : ℝ) + 1))) :=
    fun n ↦ by rw [(φ n).tsupport_normed_eq, hφ n]
  refine ⟨fun n ↦ (φ n).normed volume, fun n ↦ (φ n).contDiff_normed,
    fun n x ↦ (φ n).nonneg_normed x, fun n ↦ (φ n).hasCompactSupport_normed,
    fun n ↦ (φ n).integrable_normed, fun n ↦ (φ n).integral_normed, fun n ↦ ?_, fun n x hx ↦ ?_⟩
  · rw [htsupp n]
    intro x hx
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ = ‖c n + (x - c n)‖ := by rw [add_sub_cancel]
      _ ≤ ‖c n‖ + ‖x - c n‖ := norm_add_le _ _
      _ ≤ 3 / (4 * ((n : ℝ) + 1)) + 1 / (4 * ((n : ℝ) + 1)) := by
          rw [hcnorm n]
          exact add_le_add le_rfl (mem_closedBall_iff_norm.1 hx)
      _ = 1 / ((n : ℝ) + 1) := by field_simp; ring
  · rw [htsupp n] at hx
    have h1 : |(x - c n) (Fin.last d)| ≤ 1 / (4 * ((n : ℝ) + 1)) :=
      (EuclideanSpace.abs_apply_last_le _).trans (mem_closedBall_iff_norm.1 hx)
    rw [PiLp.sub_apply, hclast n] at h1
    have h2 := (abs_le.1 h1).1
    have e : 1 / (2 * ((n : ℝ) + 1)) = 3 / (4 * ((n : ℝ) + 1)) - 1 / (4 * ((n : ℝ) + 1)) := by
      field_simp; ring
    rw [e]
    linarith

end CubePos

section Prop918

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open SobolevMultiIndex

/-- **Proposition 9.18, (iii) ⇒ (i), the computation on $Q_+$.** Let $1 \le p < \infty$, and let $u$
be a real function such that its extension by zero $\mathbf{1}_{Q_+} u$ lies in $W^{1,p}(Q)$.
Let $\alpha$ be a smooth function with compact support such that
$\operatorname{supp} \alpha \subseteq Q$. Then every $v \in W^{1,p}(Q_+)$ whose function equals
$\alpha u$ almost everywhere on $Q_+$ lies in $W_0^{1,p}(Q_+)$.

The proof follows §9.4 of [brezis2011functional], proof of Proposition 9.18, (iii) ⇒ (i). The
function $g = \alpha \bar u$, extended by zero outside $Q$, lies in $W^{1,p}(\mathbb{R}^N)$
(`MemSobolevMultiIndex.indicator_mul`). With the one-sided mollifiers $\rho_n$ of
`exists_oneSided_mollifiers`, $\rho_n \star g \to g$ in $L^p(\mathbb{R}^N)$ and $\partial_i
(\rho_n \star g) = \rho_n \star \partial_i g \to \partial_i g$ (Lemma 9.1,
`HasWeakIteratedLineDerivOn.convolution_of_integrable` and
`MeasureTheory.tendsto_eLpNorm_convolution_sub_of_tendsto_support`). For $n$ large,
$\operatorname{supp} (\rho_n \star g) \subseteq \operatorname{supp} \rho_n + \operatorname{supp}
g \subseteq Q_+$: the support of $g$ lies in $\operatorname{supp} \alpha \cap \overline{Q_+}$,
and adding a vector with $x_N \ge 1/(2(n+1))$ and norm at most $1/(n+1)$ moves it into
$\{x_N > 0\}$ and keeps it in $Q$. So the $\rho_n \star g$ are smooth with compact support in
$Q_+$ and lie in $W_0^{1,p}(Q_+)$ by Lemma 9.5, and $v$ is their limit in $W^{1,p}(Q_+)$. -/
theorem SobolevEuclidean.mem_zero_of_indicator_memSobolev_unitChartCubePos (hp' : p ≠ ⊤)
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((unitChartCubePos d).indicator u) 1 p (unitChartCubeOpens d) volume)
    {α : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    (hαQ : tsupport α ⊆ unitChartCube d)
    {v : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hv : fn v =ᵐ[volume.restrict (unitChartCubePos d)] fun x ↦ α x * u x) :
    v ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d) := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hQm : MeasurableSet (unitChartCubePos d) := isOpen_unitChartCubePos.measurableSet
  -- the function `g = α ū` on the whole space, in `W^{1,p}(ℝ^N)`
  obtain ⟨g, hgdef⟩ : ∃ g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      g = fun x ↦ α x * (unitChartCubePos d).indicator u x := ⟨_, rfl⟩
  have hcut : IsSobolevCutoff (unitChartCubeOpens d) α :=
    IsSobolevCutoff.of_hasCompactSupport hα hαc hαQ
  have hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis g 1 p ⊤
      volume := by
    refine (hu.indicator_mul hp hcut).congr_ae (Eventually.of_forall fun x ↦ ?_)
    change (unitChartCube d).indicator (fun x ↦ α x • (unitChartCubePos d).indicator u x) x = g x
    by_cases hx : x ∈ unitChartCube d
    · simp only [hgdef, Set.indicator_of_mem hx, smul_eq_mul]
    · have : α x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hαQ h)
      simp [hgdef, Set.indicator_of_notMem hx, this]
  have hgp : MemLp g p volume := by simpa [Measure.restrict_coe_top] using hg.memLp
  have hgc : HasCompactSupport g := by rw [hgdef]; exact hαc.mul_right
  have hgv : g =ᵐ[volume.restrict (unitChartCubePos d)] fn v := by
    filter_upwards [hv, ae_restrict_mem hQm] with x hx hxQ
    simp only [hgdef, hx, Set.indicator_of_mem hxQ]
  have hgsupp : Function.support g ⊆ tsupport α ∩ closure (unitChartCubePos d) := by
    intro x hx
    rw [Function.mem_support, hgdef] at hx
    refine ⟨subset_tsupport _ (left_ne_zero_of_mul hx), subset_closure ?_⟩
    by_contra h
    exact hx (by simp [Set.indicator_of_notMem h])
  -- the weak partial derivatives of `g` on the whole space
  have hw : ∀ i : Fin (d + 1), ∃ w : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] g w ⊤ volume ∧ MemLp w p volume := by
    intro i
    obtain ⟨w, hw, hwp⟩ := hg.2 (Pi.single i 1) (by simp)
    refine ⟨w, ?_, by simpa [Measure.restrict_coe_top] using hwp⟩
    have := hw.of_perm (multiIndexTuple_single_perm
      ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis : Fin (d + 1) → _) i)
    rwa [EuclideanSpace.basisFun_toBasis_apply] at this
  choose w hw hwp using hw
  -- the margin between the support of `α` and the boundary of `Q`
  obtain ⟨V, ε, -, hαV, hε, -, -, hV⟩ :=
    hαc.exists_pos_forall_closedBall_subset isOpen_unitChartCube hαQ
  -- the one-sided mollifiers
  obtain ⟨ρ, hρs, hρ0, hρc, hρi, hρ1, hρt, hρN⟩ := exists_oneSided_mollifiers (d := d)
  have hr : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hρsupp : ∀ n, Function.support (ρ n) ⊆ closedBall 0 (1 / ((n : ℝ) + 1)) :=
    fun n ↦ (subset_tsupport _).trans (hρt n)
  -- the convolutions converge in `L^p(ℝ^N)`, together with their derivatives
  have hL0 : Tendsto (fun n ↦ eLpNorm (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g - g) p volume)
      atTop (𝓝 0) :=
    tendsto_eLpNorm_convolution_sub_of_tendsto_support hρ0 hρi hρ1 hρsupp hr hp hp' hgp
  have hLi : ∀ i, Tendsto (fun n ↦ eLpNorm (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w i - w i)
      p volume) atTop (𝓝 0) := fun i ↦
    tendsto_eLpNorm_convolution_sub_of_tendsto_support hρ0 hρi hρ1 hρsupp hr hp hp' (hwp i)
  -- the convolutions are smooth with compact support, and supported in `Q₊` for `n` large
  have hsm : ∀ n, ContDiff ℝ ∞ (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := fun n ↦
    (hρc n).contDiff_convolution_left _ (hρs n) (hgp.locallyIntegrable hp)
  have hcs : ∀ n, HasCompactSupport (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := fun n ↦
    (hρc n).convolution _ hgc
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 1 / ((n₀ : ℝ) + 1) ≤ ε := by
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
    exact ⟨n₀, hn₀.le⟩
  have hsupp : ∀ n ≥ n₀, tsupport (ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
      ⊆ unitChartCubePos d := by
    intro n hn
    have hnε : 1 / ((n : ℝ) + 1) ≤ ε := by
      refine le_trans ?_ hn₀
      gcongr
    have hS : IsCompact (tsupport (ρ n) + (tsupport α ∩ closure (unitChartCubePos d))) :=
      IsCompact.add (hρc n) (hαc.inter_right isClosed_closure)
    refine (closure_minimal ((support_convolution_subset _).trans
      (add_subset_add (subset_tsupport _) hgsupp)) hS.isClosed).trans ?_
    rintro z ⟨y, hy, x, ⟨hxα, hxQ⟩, rfl⟩
    have hyN := hρN n y hy
    have hxN := closure_unitChartCubePos_subset hxQ
    have hyn : ‖y‖ ≤ 1 / ((n : ℝ) + 1) := mem_closedBall_zero_iff.1 (hρt n hy)
    refine ⟨hV x (hαV hxα) ?_, ?_⟩
    · rw [mem_closedBall_iff_norm, add_sub_cancel_right]
      exact hyn.trans hnε
    · rw [PiLp.add_apply]
      have : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
      exact add_pos_of_pos_of_nonneg (this.trans_le hyN) hxN
  -- the elements of `W^{1,p}(Q₊)` with the convolutions as functions lie in `W_0^{1,p}(Q₊)`
  choose T hT using fun n ↦ (hsm n).exists_sobolevMultiIndex_of_hasCompactSupport
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (p := p)
    (Ω := unitChartCubePosOpens d) (μ := volume) (hcs n)
  simp only [coe_unitChartCubePosOpens] at hT
  have hTmem : ∀ n ≥ n₀, T n ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d) :=
    fun n hn ↦ mem_zero_of_fn_ae_eq_of_tsupport_subset hp' (T n) (hcs n) (hsupp n hn) (hT n)
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto (f := T) (b := atTop) ?_
    ((eventually_ge_atTop n₀).mono hTmem)
  refine tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun β ↦ ?_
  rcases MultiIndexLE.eq_zero_or_exists_eq_single β with rfl | ⟨i, rfl⟩
  · -- the functions
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL0 (fun _ ↦ zero_le)
      fun n ↦ ?_
    rw [weakDeriv_zero, weakDeriv_zero, coe_unitChartCubePosOpens,
      eLpNorm_congr_ae ((hT n).sub hgv.symm)]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  · -- the derivatives: `∂_i (T n) = ρ n ⋆ w i` and `∂_i v = w i` on `Q₊`
    have hTi : ∀ n, (weakDeriv (T n) (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (unitChartCubePos d)]
          ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w i := by
      intro n
      have h1 := (hasWeakIteratedLineDerivOn (T n) (MultiIndexLE.single i)).of_perm
        (multiIndexTuple_single_perm
          ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis : Fin (d + 1) → _) i)
      rw [EuclideanSpace.basisFun_toBasis_apply] at h1
      have h2 := (((hw i).convolution_of_integrable (hρi n) hp hgp (hwp i)).mono
        (le_top : unitChartCubePosOpens d ≤ ⊤)).congr_ae (hT n).symm (EventuallyEq.refl _ _)
      exact (ae_restrict_iff' hQm).2 (h1.ae_eq h2)
    have hvi : (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (unitChartCubePos d)] w i := by
      have h1 := (hasWeakIteratedLineDerivOn v (MultiIndexLE.single i)).of_perm
        (multiIndexTuple_single_perm
          ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis : Fin (d + 1) → _) i)
      rw [EuclideanSpace.basisFun_toBasis_apply] at h1
      have h2 := ((hw i).mono (le_top : unitChartCubePosOpens d ≤ ⊤)).congr_ae hgv
        (EventuallyEq.refl _ _)
      exact (ae_restrict_iff' hQm).2 (h1.ae_eq h2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hLi i) (fun _ ↦ zero_le)
      fun n ↦ ?_
    exact (eLpNorm_congr_ae ((hTi n).sub hvi)).trans_le
      (eLpNorm_mono_measure _ Measure.restrict_le_self)

end Prop918

/-! ### Proposition 9.18, (iii) ⇒ (i): the reduction by local charts -/

section Prop918Chart

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

namespace ContDiffChart

variable (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- **The transfer of $\theta \bar u$ along a chart.** Let $1 \le p \le \infty$ and let $c$ be a
local chart $H : Q \to U$ of class $C^1$ of an open set $\Omega \subseteq \mathbb{R}^N$. Let
$\theta$ be a smooth function with compact support, and let $u$ be a real function whose
extension by zero $\bar u = \mathbf{1}_\Omega u$ lies in $W^{1,p}(\mathbb{R}^N)$. Then the
function $(\theta u) \circ H$ on $Q_+$, extended by zero to $Q$, lies in $W^{1,p}(Q)$.

The chart is a `ContDiffChart` and $H$ is `c.toFun`. The extended function is
$(\theta \bar u) \circ H$, because $H$ sends $Q \setminus Q_+$ outside $\Omega$. It is the
transfer along the chart (Proposition 9.6) of $\theta \bar u \in W^{1,p}(U)$. -/
theorem indicator_comp_toFun_memSobolevMultiIndex {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((unitChartCubePos d).indicator fun y ↦ θ (c.toFun y) * u (c.toFun y)) 1 p
      (unitChartCubeOpens d) volume := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨M, hM⟩ := (IsSobolevCutoff.of_hasCompactSupport (Ω := ⊤) hθ hθc
    (subset_univ _)).exists_bound
  have hw : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun x ↦ θ x * (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u x) 1 p ⊤ volume :=
    hu.contDiff_mul hp hθ hM
  obtain ⟨M', hH⟩ := c.isDiffeoOnWithBoundedJacobian le_rfl
  have hH' : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCubeOpens d : Set _)
    (c.opensU : Set _) M' := hH
  have hwQ := (hw.mono_set (le_top : c.opensU ≤ ⊤)).comp_diffeoOn hH'
  refine hwQ.congr_ae ?_
  filter_upwards [ae_restrict_mem isOpen_unitChartCube.measurableSet] with y hy
  by_cases hyQ : y ∈ unitChartCubePos d
  · have hyΩ : c.toFun y ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := (c.toFun_mem_iff hy).2 hyQ
    simp only [Set.indicator_of_mem hyΩ, Set.indicator_of_mem hyQ]
  · have hyΩ : c.toFun y ∉ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := fun h ↦
      hyQ ((c.toFun_mem_iff hy).1 h)
    simp only [Set.indicator_of_notMem hyΩ, Set.indicator_of_notMem hyQ, mul_zero]

/-- **The chart piece of Proposition 9.18, (iii) ⇒ (i), on $Q_+$.** Let $1 \le p < \infty$ and let
$c$ be a local chart $H : Q \to U$ of class $C^1$ of an open set
$\Omega \subseteq \mathbb{R}^N$. Let $\theta$ be a smooth function with compact support such
that $\operatorname{supp} \theta \subseteq U$, and let $u$ be a real function whose extension by
zero $\mathbf{1}_\Omega u$ lies in $W^{1,p}(\mathbb{R}^N)$. Then every $Z \in W^{1,p}(Q_+)$
whose function equals $(\theta u) \circ H$ almost everywhere on $Q_+$ lies in $W_0^{1,p}(Q_+)$.

The proof applies `SobolevEuclidean.mem_zero_of_indicator_memSobolev_unitChartCubePos` with a
smooth $\alpha$ equal to $1$ on the compact set
$H^{-1}(\operatorname{supp} \theta) \subseteq Q$, where $\alpha \, (\theta u) \circ H = (\theta
u) \circ H$. -/
theorem mem_zero_unitChartCubePos_of_indicator_memSobolev (hp' : p ≠ ⊤)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume)
    {Z : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hZ : fn Z =ᵐ[volume.restrict (unitChartCubePos d)] fun y ↦ θ (c.toFun y) * u (c.toFun y)) :
    Z ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d) := by
  have hQm : MeasurableSet (unitChartCubePos d) := isOpen_unitChartCubePos.measurableSet
  -- a smooth `α`, compactly supported in `Q`, equal to `1` on `H⁻¹(supp θ)`
  have hK : IsCompact (c.invFun '' tsupport θ) :=
    hθc.image_of_continuousOn (c.continuousOn_invFun.mono (hθU.trans subset_closure))
  have hKQ : c.invFun '' tsupport θ ⊆ unitChartCube d :=
    (image_mono hθU).trans c.mapsTo_invFun.image_subset
  obtain ⟨V, -, hVo, hKV, -, hVc, hVQ, -⟩ :=
    hK.exists_pos_forall_closedBall_subset isOpen_unitChartCube hKQ
  obtain ⟨α, hαs, hα1, hαV, -⟩ := hK.exists_contDiff_eqOn_one hVo hKV
  have hαc : HasCompactSupport α :=
    hVc.of_isClosed_subset isClosed_closure (hαV.trans subset_closure)
  have hαQ : tsupport α ⊆ unitChartCube d := hαV.trans (subset_closure.trans hVQ)
  refine SobolevEuclidean.mem_zero_of_indicator_memSobolev_unitChartCubePos hp'
    (c.indicator_comp_toFun_memSobolevMultiIndex hθ hθc hu) hαs hαc hαQ ?_
  filter_upwards [hZ, ae_restrict_mem hQm] with y hy hyQ
  rw [hy]
  by_cases hθy : θ (c.toFun y) = 0
  · simp [hθy]
  · have hyK : y ∈ c.invFun '' tsupport θ :=
      ⟨c.toFun y, subset_tsupport _ hθy, c.invFun_toFun (unitChartCubePos_subset hyQ)⟩
    rw [hα1 hyK, Pi.one_apply, one_mul]

/-- Let $1 \le p < \infty$ and let $c$ be a local chart $H : Q \to U$ of class $C^1$ of an open set
$\Omega \subseteq \mathbb{R}^N$. Let $\theta$ be a smooth function with compact support such
that $\operatorname{supp} \theta \subseteq U$, and let $u$ be a real function whose extension by
zero $\mathbf{1}_\Omega u$ lies in $W^{1,p}(\mathbb{R}^N)$. Then there is an element of
$W_0^{1,p}(Q_+)$ whose function equals $(\theta u) \circ H$ almost everywhere on $Q_+$. -/
theorem exists_mem_zero_unitChartCubePos_of_indicator_memSobolev (hp' : p ≠ ⊤)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume) :
    ∃ Z ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d),
      fn Z =ᵐ[volume.restrict (unitChartCubePos d)] fun y ↦ θ (c.toFun y) * u (c.toFun y) := by
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun y ↦ θ (c.toFun y) * u (c.toFun y)) 1 p (unitChartCubePosOpens d) volume :=
    ((c.indicator_comp_toFun_memSobolevMultiIndex hθ hθc hu).mono_set
      unitChartCubePosOpens_le).congr_ae
      (indicator_ae_eq_restrict isOpen_unitChartCubePos.measurableSet.nullMeasurableSet)
  obtain ⟨Z, hZ⟩ := hmem.exists_sobolevMultiIndex
  exact ⟨Z, c.mem_zero_unitChartCubePos_of_indicator_memSobolev hp' hθ hθc hθU hu hZ, hZ⟩

/-- Let $\Omega'$ and $\Omega''$ be open, and let $T : W^{1,p}(\Omega') \to W^{1,p}(\Omega'')$ be a
bounded linear map that sends $W_0^{1,p}(\Omega')$ into $W_0^{1,p}(\Omega'')$. Let
$Z \in W_0^{1,p}(\Omega')$, and let $V \in W^{1,p}(\Omega'')$ have the same function as $T Z$
almost everywhere on $\Omega''$. Then $V \in W_0^{1,p}(\Omega'')$. -/
theorem _root_.SobolevMultiIndexZero.mem_of_fn_ae_eq_map {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {ι : Type*} [Fintype ι]
    [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω' Ω'' : Opens E}
    {μ : Measure E} (T : SobolevMultiIndex F b 1 p Ω' μ →L[ℝ] SobolevMultiIndex F b 1 p Ω'' μ)
    (hT : ∀ z ∈ SobolevMultiIndexZero F b 1 p Ω' μ, T z ∈ SobolevMultiIndexZero F b 1 p Ω'' μ)
    {Z : SobolevMultiIndex F b 1 p Ω' μ} (hZ : Z ∈ SobolevMultiIndexZero F b 1 p Ω' μ)
    {V : SobolevMultiIndex F b 1 p Ω'' μ} (heq : fn (T Z) =ᵐ[μ.restrict (Ω'' : Set E)] fn V) :
    V ∈ SobolevMultiIndexZero F b 1 p Ω'' μ :=
  ext_of_fn_ae_eq heq ▸ hT Z hZ

/-- Let $1 \le p < \infty$ and let $c$ be a local chart $H : Q \to U$ of class $C^1$ of an open set
$\Omega \subseteq \mathbb{R}^N$, such that $H$ restricted to $Q_+$ is a $C^1$ diffeomorphism
onto $U \cap \Omega$ with Jacobians bounded by $M$. Let $\theta$ and $u$ be real functions, let
$Z \in W_0^{1,p}(Q_+)$ have the function $(\theta u) \circ H$ almost everywhere on $Q_+$, and
let $V \in W^{1,p}(\Omega)$ have the function $\theta u$ almost everywhere on $\Omega$. Then the
restriction of $V$ to $U \cap \Omega$ lies in $W_0^{1,p}(U \cap \Omega)$.

This is a step of the proof of `ContDiffChart.restrictL_mem_zero_of_indicator_memSobolev`. The
restriction of $V$ is the transfer back along $H^{-1}$ (`SobolevMultiIndexZero.compDiffeoL_mem`)
of $Z$. The hypothesis on the Jacobians and the element $Z$ are arguments, so that each of the
three elaborations of the proof stays within its own heartbeat budget. -/
theorem restrictL_mem_zero_of_indicator_memSobolev_aux (hp' : p ≠ ⊤) {M : ℝ}
    (hH : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCubePosOpens d : Set _)
      (c.opensInter : Set _) M)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {Z : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hZ0 : Z ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d))
    (hZ : fn Z =ᵐ[volume.restrict (unitChartCubePos d)] fun y ↦ θ (c.toFun y) * u (c.toFun y))
    {V : SobolevEuclidean (d + 1) 1 p Ω}
    (hV : fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ θ x * u x) :
    restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume c.opensInter_le V
      ∈ SobolevEuclideanZero (d + 1) 1 p c.opensInter := by
  refine SobolevMultiIndexZero.mem_of_fn_ae_eq_map
    (compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume hH.symm)
    (fun z hz ↦ SobolevMultiIndexZero.compDiffeoL_mem hp' hH.symm hz) hZ0 ?_
  have h1 := hH.symm.ae_comp_restrict (P := fun y ↦ fn Z y = θ (c.toFun y) * u (c.toFun y)) hZ
  have h2 : fn V =ᵐ[volume.restrict (c.opensInter : Set _)] fun x ↦ θ x * u x :=
    hV.filter_mono (ae_mono (Measure.restrict_mono c.opensInter_le le_rfl))
  filter_upwards [fn_compDiffeoL hH.symm Z, h1, fn_restrictL c.opensInter_le V, h2,
    ae_restrict_mem c.opensInter.isOpen.measurableSet] with x hx1 hx2 hx3 hx4 hx5
  refine hx1.trans (hx2.trans ?_)
  rw [c.toFun_invFun hx5.1]
  exact (hx3.trans hx4).symm

/-- **The chart piece of Proposition 9.18, (iii) ⇒ (i), on $U \cap \Omega$.** Let $1 \le p < \infty$
and let $c$ be a local chart $H : Q \to U$ of class $C^1$ of an open set
$\Omega \subseteq \mathbb{R}^N$. Let $\theta$ be a smooth function with compact support such
that $\operatorname{supp} \theta \subseteq U$, and let $u$ be a real function whose extension by
zero $\mathbf{1}_\Omega u$ lies in $W^{1,p}(\mathbb{R}^N)$. Then for every
$V \in W^{1,p}(\Omega)$ whose function equals $\theta u$ almost everywhere on $\Omega$, the
restriction of $V$ to $U \cap \Omega$ lies in $W_0^{1,p}(U \cap \Omega)$. -/
theorem restrictL_mem_zero_of_indicator_memSobolev (hp' : p ≠ ⊤)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume)
    {V : SobolevEuclidean (d + 1) 1 p Ω}
    (hV : fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ θ x * u x) :
    restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume c.opensInter_le V
      ∈ SobolevEuclideanZero (d + 1) 1 p c.opensInter := by
  obtain ⟨M, hH⟩ := c.isDiffeoOnWithBoundedJacobian_pos le_rfl Ω.isOpen
  obtain ⟨Z, hZ0, hZ⟩ :=
    c.exists_mem_zero_unitChartCubePos_of_indicator_memSobolev hp' hθ hθc hθU hu
  exact c.restrictL_mem_zero_of_indicator_memSobolev_aux hp' hH hZ0 hZ hV

/-- **The chart piece of Proposition 9.18, (iii) ⇒ (i).** Let $1 \le p < \infty$ and let $c$ be a
local chart $H : Q \to U$ of class $C^1$ of an open set $\Omega \subseteq \mathbb{R}^N$. Let
$\theta$ be a smooth function with compact support such that
$\operatorname{supp} \theta \subseteq U$, and let $u$ be a real function whose extension by zero
$\mathbf{1}_\Omega u$ lies in $W^{1,p}(\mathbb{R}^N)$. Then every $V \in W^{1,p}(\Omega)$ whose
function equals $\theta u$ almost everywhere on $\Omega$ lies in $W_0^{1,p}(\Omega)$.

The restriction of $V$ to $U \cap \Omega$ lies in $W_0^{1,p}(U \cap \Omega)$
(`ContDiffChart.restrictL_mem_zero_of_indicator_memSobolev`), and $V$ vanishes on $\Omega$
outside the closed set $\operatorname{supp} \theta$, whose trace on $\Omega$ lies in
$U \cap \Omega$. So `SobolevMultiIndexZero.mem_of_mem_restrict` applies. -/
theorem mem_zero_of_indicator_memSobolev (hp' : p ≠ ⊤)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume)
    {V : SobolevEuclidean (d + 1) 1 p Ω}
    (hV : fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ θ x * u x) :
    V ∈ SobolevEuclideanZero (d + 1) 1 p Ω := by
  refine SobolevMultiIndexZero.mem_of_mem_restrict c.opensInter_le
    (c.restrictL_mem_zero_of_indicator_memSobolev hp' hθ hθc hθU hu hV) (isClosed_tsupport θ)
    (fun x hx ↦ ⟨hθU hx.1, hx.2⟩) ?_
  filter_upwards [hV] with x hx hxθ
  rw [hx, image_eq_zero_of_notMem_tsupport hxθ, zero_mul]

end ContDiffChart

namespace SobolevEuclideanZero

/-- **Proposition 9.18, (iii) ⇒ (i), for a function that vanishes outside a ball.** Let
$1 \le p < \infty$, let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be an open set of class
$C^1$, and let $u$ be a real function with $u(x) = 0$ for $\|x\| > R$ whose extension by zero
$\mathbf{1}_\Omega u$ lies in $W^{1,p}(\mathbb{R}^N)$. Then every $v \in W^{1,p}(\Omega)$ whose
function equals $u$ almost everywhere on $\Omega$ lies in $W_0^{1,p}(\Omega)$.

The hypothesis on $\Omega$ is `IsContDiffChartDomain 1`. The proof follows Proposition 9.18,
(iii) ⇒ (i), of [brezis2011functional], "by local charts and partition of unity". Finitely many
charts $c_i$ cover the compact set $\partial\Omega \cap \bar B(0, R)$. Lemma 9.3 gives a
partition $\theta_0 + \sum_i \theta_i = 1$ (`IsCompact.exists_contDiff_partitionOfUnity`) with
$\operatorname{supp} \theta_i \subseteq U_i$ and $\theta_0$ vanishing near this part of the
boundary. Each $\theta_i u$ is the function of an element of $W_0^{1,p}(\Omega)$ by
`ContDiffChart.mem_zero_of_indicator_memSobolev`. The function
$\theta_0 u = u - \sum_i \theta_i u$ vanishes on $\Omega$ outside the compact set
$\operatorname{supp} \theta_0 \cap \bar\Omega \cap \bar B(0, R) \subseteq \Omega$, so it lies in
$W_0^{1,p}(\Omega)$ by Lemma 9.5, and $v$ is the sum. -/
theorem mem_of_indicator_memSobolev_of_forall_eq_zero (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume)
    {R : ℝ} (huR : ∀ x, R < ‖x‖ → u x = 0) {v : SobolevEuclidean (d + 1) 1 p Ω}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u) :
    v ∈ SobolevEuclideanZero (d + 1) 1 p Ω := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hΩm := Ω.isOpen.measurableSet
  -- the compact piece of the boundary inside the ball, its finite atlas and partition of unity
  have hΓ : IsCompact (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ closedBall 0 R) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_frontier.inter isClosed_closedBall)
      (isBounded_closedBall.subset inter_subset_right)
  obtain ⟨k, c, hc⟩ := hΩ.exists_finite_atlas_of_isCompact hΓ inter_subset_left
  obtain ⟨θ₀, θ, -, hθs, -, -, hsum, hθc, hθU, hθ₀Γ⟩ :=
    hΓ.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hc
  -- `u ∈ W^{1,p}(Ω)`, and the elements `θ_i u`
  have huΩ : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u 1 p Ω
      volume :=
    (hu.mono_set le_top).congr_ae (indicator_ae_eq_restrict hΩm.nullMeasurableSet)
  have hθu : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun x ↦ θ i x * u x) 1 p Ω volume := fun i ↦ by
    obtain ⟨M, hM⟩ := (IsSobolevCutoff.of_hasCompactSupport (Ω := ⊤) (hθs i) (hθc i)
      (subset_univ _)).exists_bound
    exact huΩ.contDiff_mul hp (hθs i) hM
  choose V hV using fun i ↦ (hθu i).exists_sobolevMultiIndex
  have hVmem : ∀ i, V i ∈ SobolevEuclideanZero (d + 1) 1 p Ω := fun i ↦
    (c i).mem_zero_of_indicator_memSobolev hp' (hθs i) (hθc i) (hθU i) hu (hV i)
  -- the remaining piece `θ₀ u = u − ∑ θ_i u` has compact support in `Ω`
  have hV₀ : fn (v - ∑ i, V i) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ θ₀ x * u x := by
    filter_upwards [fn_sub v (∑ i, V i), fn_finset_sum Finset.univ V, ae_all_iff.2 hV, hv]
      with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Finset.sum_apply, h4]
    simp only [h3]
    have := hsum x
    rw [← Finset.sum_mul]
    have e : ∑ i, θ i x = 1 - θ₀ x := by linarith
    rw [e]
    ring
  have hK : IsCompact (tsupport θ₀ ∩ closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ∩ closedBall 0 R) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) R).inter_left
      ((isClosed_tsupport θ₀).inter isClosed_closure)
  have hKΩ : tsupport θ₀ ∩ closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ closedBall 0 R
      ⊆ Ω := by
    rintro x ⟨⟨hxθ, hxc⟩, hxR⟩
    rw [closure_eq_interior_union_frontier, Ω.isOpen.interior_eq] at hxc
    rcases hxc with hxΩ | hxf
    · exact hxΩ
    · exact absurd ⟨hxf, hxR⟩ (disjoint_left.1 hθ₀Γ hxθ)
  have hV₀mem : v - ∑ i, V i ∈ SobolevEuclideanZero (d + 1) 1 p Ω := by
    refine mem_zero_of_ae_eq_zero_compl_isCompact hp' _ hK hKΩ ?_
    filter_upwards [hV₀, ae_restrict_mem hΩm] with x hx hxΩ hxK
    rw [hx]
    by_cases hxθ : x ∈ tsupport θ₀
    · by_cases hxR : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) R
      · exact absurd ⟨⟨hxθ, subset_closure hxΩ⟩, hxR⟩ hxK
      · rw [huR x (not_le.1 fun h ↦ hxR (mem_closedBall_zero_iff.2 h)), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul]
  have e : v = (v - ∑ i, V i) + ∑ i, V i := by abel
  rw [e]
  exact add_mem hV₀mem (Submodule.sum_mem _ fun i _ ↦ hVmem i)

/-- **Proposition 9.18, (iii) ⇒ (i).** Let $1 \le p < \infty$, let $\Omega \subseteq \mathbb{R}^N$,
$N = d + 1$, be an open set of class $C^1$, and let $u$ be a real function whose extension by
zero $\bar u = \mathbf{1}_\Omega u$ lies in $W^{1,p}(\mathbb{R}^N)$. Then there is
$v \in W_0^{1,p}(\Omega)$ whose function equals $u$ almost everywhere on $\Omega$. This is
Proposition 9.18, (iii) ⇒ (i), of [brezis2011functional]. The converse, (i) ⇒ (iii), is
`SobolevMultiIndexZero.indicator_memSobolevMultiIndex` and holds on every open set.

The hypothesis on $\Omega$ is `IsContDiffChartDomain 1`. The case of a function that vanishes
outside a ball is `SobolevEuclideanZero.mem_of_indicator_memSobolev_of_forall_eq_zero`. In
general, with the cut-off sequence $\zeta_n$ (`SobolevMultiIndex.tendsto_cutoff_smul`),
$\zeta_n u$ has bounded support and its extension by zero $\zeta_n \bar u$ lies in
$W^{1,p}(\mathbb{R}^N)$. So the elements with function $\zeta_n u$ lie in $W_0^{1,p}(\Omega)$,
and they converge in $W^{1,p}(\Omega)$; the closed subspace $W_0^{1,p}(\Omega)$ contains the
limit. -/
theorem mem_of_indicator_memSobolev (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator u) 1 p ⊤ volume) :
    ∃ v ∈ SobolevEuclideanZero (d + 1) 1 p Ω,
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hΩm := Ω.isOpen.measurableSet
  have huΩ : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u 1 p Ω
      volume :=
    (hu.mono_set le_top).congr_ae (indicator_ae_eq_restrict hΩm.nullMeasurableSet)
  obtain ⟨U, hU⟩ := huΩ.exists_sobolevMultiIndex
  refine ⟨U, ?_, hU⟩
  -- the cut-off sequence `ζ_n U → U`
  obtain ⟨ζ, hζ, hζ1, hζs, hζ01⟩ := exists_contDiff_eqOn_one_closedBall_one
    (EuclideanSpace ℝ (Fin (d + 1)))
  obtain ⟨w, hw, -, hwt⟩ :=
    tendsto_cutoff_smul hp' hζ hζ01 hζ1 (hζs.trans ball_subset_closedBall) U
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hwt (Eventually.of_forall fun n ↦ ?_)
  have hcpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hζc : HasCompactSupport ζ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) 2).of_isClosed_subset
      (isClosed_tsupport ζ) (hζs.trans ball_subset_closedBall)
  -- the cut-off `ζ_n`: smooth, compactly supported, vanishing for `‖x‖ > 2 (n + 1)`
  have hζn : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ ζ (((n : ℝ) + 1)⁻¹ • x) :=
    hζ.comp (contDiff_id.const_smul _)
  have hζnc : HasCompactSupport fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ ζ (((n : ℝ) + 1)⁻¹ • x) :=
    hζc.comp_homeomorph (Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (inv_ne_zero hcpos.ne'))
  have hζn0 : ∀ x : EuclideanSpace ℝ (Fin (d + 1)), 2 * ((n : ℝ) + 1) < ‖x‖ →
      ζ (((n : ℝ) + 1)⁻¹ • x) = 0 := fun x hx ↦ by
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    have h2 : ‖((n : ℝ) + 1)⁻¹ • x‖ < 2 := by simpa using hζs h
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos, inv_mul_lt_iff₀ hcpos] at h2
    linarith
  obtain ⟨M, hM⟩ := (IsSobolevCutoff.of_hasCompactSupport (Ω := ⊤) hζn hζnc
    (subset_univ _)).exists_bound
  have hun : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator
        fun x ↦ ζ (((n : ℝ) + 1)⁻¹ • x) * u x) 1 p ⊤ volume := by
    refine (hu.contDiff_mul hp hζn hM).congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  refine mem_of_indicator_memSobolev_of_forall_eq_zero hp' hΩ hun (R := 2 * ((n : ℝ) + 1))
    (fun x hx ↦ by rw [hζn0 x hx, zero_mul]) ?_
  filter_upwards [hw n, hU] with x hx1 hx2
  rw [hx1, hx2]

end SobolevEuclideanZero

end Prop918Chart

/-! ### Theorem 9.17, (ii) ⇒ (i): the computation on $Q_+$ -/

section Strip

variable {d : ℕ}

/-- The **strip** $\{x \in Q_+ : x_N < \varepsilon\}$ at the bottom of the upper half cylinder
$Q_+ \subseteq \mathbb{R}^{d+1}$. -/
def unitChartCubeStrip (d : ℕ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x ∈ unitChartCubePos d | x (Fin.last d) < ε}

/-- The strip lies in $Q_+$. -/
theorem unitChartCubeStrip_subset {ε : ℝ} : unitChartCubeStrip d ε ⊆ unitChartCubePos d :=
  fun _ hx ↦ hx.1

/-- The strip is open. -/
theorem isOpen_unitChartCubeStrip {ε : ℝ} : IsOpen (unitChartCubeStrip d ε) :=
  isOpen_unitChartCubePos.inter (isOpen_lt continuous_apply_last continuous_const)

/-- The strip is measurable. -/
theorem measurableSet_unitChartCubeStrip {ε : ℝ} : MeasurableSet (unitChartCubeStrip d ε) :=
  isOpen_unitChartCubeStrip.measurableSet

/-- For $\varepsilon \le 1$, $x' \in \mathbb{R}^d$ and $t \in \mathbb{R}$, the point $(x', t)$ lies
in the strip $\{x \in Q_+ : x_N < \varepsilon\}$ if and only if $\|x'\| < 1$ and
$0 < t < \varepsilon$.

The point $(x', t)$ is `EuclideanSpace.snocLast x' t`. -/
theorem snocLast_mem_unitChartCubeStrip_iff {ε : ℝ} (hε : ε ≤ 1) {x' : EuclideanSpace ℝ (Fin d)}
    {t : ℝ} :
    EuclideanSpace.snocLast x' t ∈ unitChartCubeStrip d ε ↔ ‖x'‖ < 1 ∧ 0 < t ∧ t < ε := by
  simp only [unitChartCubeStrip, unitChartCubePos, unitChartCube, mem_ofPred_eq,
    EuclideanSpace.init_snocLast, EuclideanSpace.snocLast_apply_last]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨h1, ?_⟩, h2⟩, h3⟩
    rw [abs_of_pos h2]
    exact h3.trans_le hε

/-- **Fubini's theorem on the strip.** For $\varepsilon \le 1$ and an almost everywhere measurable
function $F : \mathbb{R}^{d+1} \to [0, \infty]$,
$$\int_{\{x \in Q_+ : x_N < \varepsilon\}} F = \int_{\{\|x'\| < 1\}} \int_0^\varepsilon F(x', t)
  \, dt \, dx'.$$
-/
theorem lintegral_unitChartCubeStrip {ε : ℝ} (hε : ε ≤ 1)
    {F : EuclideanSpace ℝ (Fin (d + 1)) → ℝ≥0∞} (hF : AEMeasurable F) :
    ∫⁻ x in unitChartCubeStrip d ε, F x
      = ∫⁻ x' in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ t in Ioo 0 ε,
        F (EuclideanSpace.snocLast x' t) := by
  rw [← lintegral_indicator measurableSet_unitChartCubeStrip,
    EuclideanSpace.lintegral_lastInit _ (hF.indicator measurableSet_unitChartCubeStrip),
    ← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun x' ↦ ?_
  by_cases hx' : x' ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1
  · rw [Set.indicator_of_mem hx', ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t ↦ ?_
    by_cases ht : t ∈ Ioo 0 ε
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem]
      exact (snocLast_mem_unitChartCubeStrip_iff hε).2 ⟨mem_ball_zero_iff.1 hx', ht.1, ht.2⟩
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem]
      exact fun h ↦ ht ⟨((snocLast_mem_unitChartCubeStrip_iff hε).1 h).2.1,
        ((snocLast_mem_unitChartCubeStrip_iff hε).1 h).2.2⟩
  · rw [Set.indicator_of_notMem hx']
    have h0 : ∀ t, (unitChartCubeStrip d ε).indicator F (EuclideanSpace.snocLast x' t) = 0 :=
      fun t ↦ Set.indicator_of_notMem (fun h ↦
        hx' (mem_ball_zero_iff.2 ((snocLast_mem_unitChartCubeStrip_iff hε).1 h).1)) F
    simp [h0]

/-- **The strip inequality for a $C^1$ function supported in $Q_+$.** Let $\varepsilon \le 1$, and
let $g \in C^1(\mathbb{R}^{d+1})$ with $\operatorname{supp} g \subseteq Q_+$. Then
$$\int_{\{x \in Q_+ : x_N < \varepsilon\}} |g| \le \varepsilon \int_{\{x \in Q_+ : x_N <
  \varepsilon\}} |\partial_N g|.$$

The integrals are lower Lebesgue integrals of `‖·‖ₑ`. The proof uses the fundamental theorem of
calculus along the last coordinate, from $x_N = 0$, where $g$ vanishes: $|g(x', t)| \le
\int_0^\varepsilon |\partial_N g(x', s)| \, ds$ for $0 < t < \varepsilon$. This is integrated
over $t \in (0, \varepsilon)$ and $\|x'\| < 1$ (`lintegral_unitChartCubeStrip`). -/
theorem lintegral_unitChartCubeStrip_le_of_contDiff {ε : ℝ} (hε : ε ≤ 1)
    {g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hg : ContDiff ℝ 1 g)
    (hgs : tsupport g ⊆ unitChartCubePos d) :
    ∫⁻ x in unitChartCubeStrip d ε, ‖g x‖ₑ
      ≤ ENNReal.ofReal ε * ∫⁻ x in unitChartCubeStrip d ε,
        ‖fderiv ℝ g x (EuclideanSpace.single (Fin.last d) 1)‖ₑ := by
  obtain ⟨D, hDdef⟩ : ∃ D : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
    D = fun x ↦ fderiv ℝ g x (EuclideanSpace.single (Fin.last d) 1) := ⟨_, rfl⟩
  have hgc : Continuous g := hg.continuous
  have hDc : Continuous D := by
    rw [hDdef]; exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hzero : ∀ x, x ∉ unitChartCubePos d → g x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgs h)
  -- the derivative of `g` along the last coordinate
  have hderiv : ∀ (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ),
      HasDerivAt (fun s ↦ g (EuclideanSpace.snocLast x' s))
        (D (EuclideanSpace.snocLast x' t)) t := by
    intro x' t
    have h1 : HasDerivAt (fun s : ℝ ↦ EuclideanSpace.snocLast x' s)
        (EuclideanSpace.single (Fin.last d) 1) t := by
      have heq : (fun s : ℝ ↦ EuclideanSpace.snocLast x' s)
          = fun s ↦ EuclideanSpace.snocLast x' 0 + s • EuclideanSpace.single (Fin.last d) 1 := by
        funext s
        exact EuclideanSpace.snocLast_eq_add_smul_single x' s
      rw [heq]
      exact (((hasDerivAt_id' t).smul_const _).const_add (EuclideanSpace.snocLast x' 0)).congr_deriv
        (one_smul ℝ _)
    have h2 := (hg.differentiable one_ne_zero (EuclideanSpace.snocLast x' t)).hasFDerivAt
    rw [hDdef]
    exact h2.comp_hasDerivAt t h1
  -- the pointwise bound on the strip
  have hpt : ∀ (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ), 0 < t → t < ε →
      ‖g (EuclideanSpace.snocLast x' t)‖ₑ
        ≤ ∫⁻ s in Ioo 0 ε, ‖D (EuclideanSpace.snocLast x' s)‖ₑ := by
    intro x' t ht0 htε
    have hint : IntervalIntegrable (fun s ↦ D (EuclideanSpace.snocLast x' s)) volume 0 t :=
      (hDc.comp (EuclideanSpace.continuous_snocLast.comp (Continuous.prodMk_right x')))
        |>.intervalIntegrable _ _
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s ↦ g (EuclideanSpace.snocLast x' s)) (fun s _ ↦ hderiv x' s) hint
    have hg0 : g (EuclideanSpace.snocLast x' 0) = 0 :=
      hzero _ (by simp [unitChartCubePos, EuclideanSpace.snocLast_apply_last])
    rw [hg0, sub_zero] at hfund
    rw [← hfund, intervalIntegral.integral_of_le ht0.le]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine (lintegral_mono_set (Ioc_subset_Ioc_right htε.le)).trans ?_
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  -- Fubini on both sides
  have hgm : AEMeasurable fun x ↦ ‖g x‖ₑ := hgc.measurable.enorm.aemeasurable
  have hDm : AEMeasurable fun x ↦ ‖D x‖ₑ := hDc.measurable.enorm.aemeasurable
  have hD : ∀ x, fderiv ℝ g x (EuclideanSpace.single (Fin.last d) 1) = D x := fun x ↦ by
    rw [hDdef]
  simp only [hD]
  rw [lintegral_unitChartCubeStrip hε hgm, lintegral_unitChartCubeStrip hε hDm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x' _
  calc ∫⁻ t in Ioo 0 ε, ‖g (EuclideanSpace.snocLast x' t)‖ₑ
      ≤ ∫⁻ _ in Ioo 0 ε, ∫⁻ s in Ioo 0 ε, ‖D (EuclideanSpace.snocLast x' s)‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hpt x' t ht.1 ht.2
    _ = ENNReal.ofReal ε * ∫⁻ s in Ioo 0 ε, ‖D (EuclideanSpace.snocLast x' s)‖ₑ := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]

end Strip

section Limit

/-- Let $\nu \le \mu$ be measures, let $1 \le p \le \infty$, and let $h$ be a real function, almost
everywhere strongly measurable for $\mu$. Then
$$\int \|h\| \, d\nu \le \|h\|_{L^p(\mu)} \, \nu(X)^{1 - 1/p}.$$

The integral is a lower Lebesgue integral. In the exponent, $p$ is converted to a real number by
`ENNReal.toReal`, which sends $\infty$ to $0$. Since $1/0 = 0$ in Lean, the exponent is $1$ for
$p = \infty$. -/
theorem MeasureTheory.lintegral_enorm_le_eLpNorm_mul_of_le {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hν : ν ≤ μ) {p : ℝ≥0∞} (hp : 1 ≤ p) {h : X → ℝ}
    (hh : AEStronglyMeasurable h μ) :
    ∫⁻ x, ‖h x‖ₑ ∂ν ≤ eLpNorm h p μ * ν univ ^ (1 - 1 / p.toReal) := by
  have hh' := hh.mono_measure hν
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) (p := 1) hp hh'
  rw [eLpNorm_one_eq_lintegral_enorm hh', ENNReal.toReal_one, div_one] at this
  exact this.trans (mul_le_mul' (eLpNorm_mono_measure _ hν) le_rfl)

/-- The triangle inequality $\int \|h_1\| \, d\nu \le \int \|h_1 - h_2\| \, d\nu + \int \|h_2\| \,
d\nu$ for real functions $h_1$, $h_2$ with $h_1 - h_2$ almost everywhere strongly measurable.
The integrals are lower Lebesgue integrals. -/
theorem MeasureTheory.lintegral_enorm_le_lintegral_enorm_sub_add {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {h₁ h₂ : X → ℝ} (hm : AEStronglyMeasurable (h₁ - h₂) ν) :
    ∫⁻ x, ‖h₁ x‖ₑ ∂ν ≤ ∫⁻ x, ‖(h₁ - h₂) x‖ₑ ∂ν + ∫⁻ x, ‖h₂ x‖ₑ ∂ν := by
  rw [← lintegral_add_left' hm.enorm]
  refine lintegral_mono fun x ↦ ?_
  calc ‖h₁ x‖ₑ = ‖(h₁ x - h₂ x) + h₂ x‖ₑ := by rw [sub_add_cancel]
    _ ≤ ‖h₁ x - h₂ x‖ₑ + ‖h₂ x‖ₑ := enorm_add_le _ _

/-- **Passing an integral inequality to the limit.** Let $\nu \le \mu$ be measures with $\nu$
finite, let $1 \le p < \infty$ and let $c \in [0, \infty)$. Let $f$, $g$, $f_n$, $g_n$ be real
functions, almost everywhere strongly measurable for $\mu$, with $f_n \to f$ and $g_n \to g$ in
$L^p(\mu)$. If $\int |f_n| \, d\nu \le c \int |g_n| \, d\nu$ for every $n$, then
$\int |f| \, d\nu \le c \int |g| \, d\nu$.

The integrals are lower Lebesgue integrals, and $c$ is in `ℝ≥0∞`. -/
theorem MeasureTheory.lintegral_enorm_le_mul_of_tendsto {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hν : ν ≤ μ) [IsFiniteMeasure ν] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {f g : X → ℝ} {fs gs : ℕ → X → ℝ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfs : ∀ n, AEStronglyMeasurable (fs n) μ) (hgs : ∀ n, AEStronglyMeasurable (gs n) μ)
    (hn : ∀ n, ∫⁻ x, ‖fs n x‖ₑ ∂ν ≤ c * ∫⁻ x, ‖gs n x‖ₑ ∂ν)
    (hft : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0))
    (hgt : Tendsto (fun n ↦ eLpNorm (gs n - g) p μ) atTop (𝓝 0)) :
    ∫⁻ x, ‖f x‖ₑ ∂ν ≤ c * ∫⁻ x, ‖g x‖ₑ ∂ν := by
  have hV : ν univ ^ (1 - 1 / p.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by
      have : 1 / p.toReal ≤ 1 := by
        rw [div_le_one (ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp'),
          ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono hp' hp
      linarith) (measure_ne_top ν _)
  have hbound : ∀ n, ∫⁻ x, ‖f x‖ₑ ∂ν
      ≤ eLpNorm (fs n - f) p μ * ν univ ^ (1 - 1 / p.toReal)
        + c * (eLpNorm (gs n - g) p μ * ν univ ^ (1 - 1 / p.toReal) + ∫⁻ x, ‖g x‖ₑ ∂ν) := by
    intro n
    calc ∫⁻ x, ‖f x‖ₑ ∂ν
        ≤ ∫⁻ x, ‖(f - fs n) x‖ₑ ∂ν + ∫⁻ x, ‖fs n x‖ₑ ∂ν :=
          lintegral_enorm_le_lintegral_enorm_sub_add ((hf.sub (hfs n)).mono_measure hν)
      _ ≤ ∫⁻ x, ‖(f - fs n) x‖ₑ ∂ν + c * ∫⁻ x, ‖gs n x‖ₑ ∂ν := add_le_add le_rfl (hn n)
      _ ≤ ∫⁻ x, ‖(f - fs n) x‖ₑ ∂ν
          + c * (∫⁻ x, ‖(gs n - g) x‖ₑ ∂ν + ∫⁻ x, ‖g x‖ₑ ∂ν) :=
          add_le_add le_rfl (mul_le_mul' le_rfl (lintegral_enorm_le_lintegral_enorm_sub_add
            (((hgs n).sub hg).mono_measure hν)))
      _ ≤ eLpNorm (f - fs n) p μ * ν univ ^ (1 - 1 / p.toReal)
          + c * (eLpNorm (gs n - g) p μ * ν univ ^ (1 - 1 / p.toReal) + ∫⁻ x, ‖g x‖ₑ ∂ν) :=
          add_le_add (lintegral_enorm_le_eLpNorm_mul_of_le hν hp (hf.sub (hfs n)))
            (mul_le_mul' le_rfl (add_le_add
              (lintegral_enorm_le_eLpNorm_mul_of_le hν hp ((hgs n).sub hg)) le_rfl))
      _ = _ := by rw [eLpNorm_sub_comm]
  have h1 := ENNReal.Tendsto.mul_const hft (Or.inr hV)
  have h2 := ENNReal.Tendsto.mul_const hgt (Or.inr hV)
  have h3 := h1.add (ENNReal.Tendsto.const_mul (h2.add (tendsto_const_nhds
    (x := ∫⁻ x, ‖g x‖ₑ ∂ν))) (Or.inr hc))
  simp only [zero_mul, zero_add] at h3
  exact ge_of_tendsto h3 (Eventually.of_forall hbound)

end Limit

section StripTyped

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open SobolevMultiIndex

/-- The strip $\{x \in Q_+ : x_N < \varepsilon\}$ has finite measure. -/
theorem volume_unitChartCubeStrip_ne_top {ε : ℝ} :
    volume (unitChartCubeStrip d ε) ≠ ⊤ :=
  (measure_mono (unitChartCubeStrip_subset.trans (unitChartCubePos_subset.trans
    unitChartCube_subset_ball))).trans_lt measure_ball_lt_top |>.ne

omit [Fact (1 ≤ p)] in
/-- The strip inequality for an element whose function is a test function. Let $\varepsilon \le 1$,
and let $w \in W^{1,p}(Q_+)$ have the function $\varphi$ almost everywhere on $Q_+$ for a test
function $\varphi$ on $Q_+$. Then
$$\int_{\{x \in Q_+ : x_N < \varepsilon\}} |w| \le \varepsilon \int_{\{x \in Q_+ : x_N <
  \varepsilon\}} |\partial_N w|.$$
-/
theorem SobolevEuclidean.lintegral_unitChartCubeStrip_le_of_fn_ae_eq_testFunction {ε : ℝ}
    (hε : ε ≤ 1) {w : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    {φ : 𝓓(unitChartCubePosOpens d, ℝ)} (hφ : fn w =ᵐ[volume.restrict (unitChartCubePos d)] φ) :
    ∫⁻ x in unitChartCubeStrip d ε, ‖fn w x‖ₑ
      ≤ ENNReal.ofReal ε * ∫⁻ x in unitChartCubeStrip d ε,
        ‖weakDeriv w (MultiIndexLE.single (Fin.last d)) x‖ₑ := by
  have hSQ : volume.restrict (unitChartCubeStrip d ε)
      ≤ volume.restrict (unitChartCubePos d) :=
    Measure.restrict_mono unitChartCubeStrip_subset le_rfl
  have h1 : ∫⁻ x in unitChartCubeStrip d ε, ‖fn w x‖ₑ = ∫⁻ x in unitChartCubeStrip d ε, ‖φ x‖ₑ :=
    lintegral_congr_ae ((hφ.filter_mono (ae_mono hSQ)).mono fun x hx ↦ by simp only [hx])
  have h2 : ∫⁻ x in unitChartCubeStrip d ε, ‖weakDeriv w (MultiIndexLE.single (Fin.last d)) x‖ₑ
      = ∫⁻ x in unitChartCubeStrip d ε, ‖fderiv ℝ φ x (EuclideanSpace.single (Fin.last d) 1)‖ₑ := by
    have := SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hφ (Fin.last d)
    rw [EuclideanSpace.basisFun_toBasis_last] at this
    exact lintegral_congr_ae ((this.filter_mono (ae_mono hSQ)).mono fun x hx ↦ by simp only [hx])
  rw [h1, h2]
  exact lintegral_unitChartCubeStrip_le_of_contDiff hε (φ.contDiff.of_le (by simp))
    φ.tsupport_subset

/-- **The strip inequality on $W_0^{1,p}(Q_+)$.** Let $1 \le p < \infty$, let $\varepsilon \le 1$
and let $u \in W_0^{1,p}(Q_+)$. Then
$$\int_{\{x \in Q_+ : x_N < \varepsilon\}} |u| \le \varepsilon \int_{\{x \in Q_+ : x_N <
  \varepsilon\}} |\partial_N u|.$$

The inequality for test functions (`lintegral_unitChartCubeStrip_le_of_contDiff`) passes to the
limit in $W^{1,p}(Q_+)$. Both sides are continuous for the convergence in $L^p$ on the strip,
which has finite measure. -/
theorem SobolevEuclideanZero.lintegral_unitChartCubeStrip_le (hp' : p ≠ ⊤) {ε : ℝ} (hε : ε ≤ 1)
    {u : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d)) :
    ∫⁻ x in unitChartCubeStrip d ε, ‖fn u x‖ₑ
      ≤ ENNReal.ofReal ε * ∫⁻ x in unitChartCubeStrip d ε,
        ‖weakDeriv u (MultiIndexLE.single (Fin.last d)) x‖ₑ := by
  obtain ⟨w, φ, hφ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hu
  have hSQ : volume.restrict (unitChartCubeStrip d ε)
      ≤ volume.restrict (unitChartCubePos d) :=
    Measure.restrict_mono unitChartCubeStrip_subset le_rfl
  have : IsFiniteMeasure (volume.restrict (unitChartCubeStrip d ε)) :=
    isFiniteMeasure_restrict.2 volume_unitChartCubeStrip_ne_top
  exact lintegral_enorm_le_mul_of_tendsto hSQ Fact.out hp' ENNReal.ofReal_ne_top
    (memLp u).aestronglyMeasurable (Lp.aestronglyMeasurable _)
    (fun n ↦ (memLp (w n)).aestronglyMeasurable) (fun n ↦ Lp.aestronglyMeasurable _)
    (fun n ↦ SobolevEuclidean.lintegral_unitChartCubeStrip_le_of_fn_ae_eq_testFunction hε (hφ n))
    (tendsto_eLpNorm_fn_sub hw) (tendsto_eLpNorm_weakDeriv_sub hw _)

end StripTyped

section StripLimit

variable {d : ℕ}

open EuclideanSpace

/-- For $\varepsilon \le 1$, the measure of the strip is $|\{x \in Q_+ : x_N < \varepsilon\}| =
|B'(0, 1)| \, \varepsilon$, where $B'(0, 1)$ is the unit ball of $\mathbb{R}^d$. For
$\varepsilon \le 0$ both sides are $0$. -/
theorem volume_unitChartCubeStrip {ε : ℝ} (hε : ε ≤ 1) :
    volume (unitChartCubeStrip d ε)
      = volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * ENNReal.ofReal ε := by
  rw [← setLIntegral_one, lintegral_unitChartCubeStrip hε aemeasurable_const]
  simp only [setLIntegral_const, one_mul, Real.volume_Ioo, sub_zero]
  rw [mul_comm]

/-- **The strip integrals of an integrable function tend to $0$.** Let $g$ be a real function with
$\int_{Q_+} |g| < \infty$, and let $\varepsilon_n \le 1$ with $\varepsilon_n \to 0$. Then
$\int_{\{x \in Q_+ : x_N < \varepsilon_n\}} |g| \to 0$. -/
theorem tendsto_lintegral_unitChartCubeStrip {g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hg : ∫⁻ x in unitChartCubePos d, ‖g x‖ₑ ≠ ⊤) {ε : ℕ → ℝ} (hε : ∀ n, ε n ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫⁻ x in unitChartCubeStrip d (ε n), ‖g x‖ₑ) atTop (𝓝 0) := by
  have heq : ∀ n, ∫⁻ x in unitChartCubeStrip d (ε n), ‖g x‖ₑ
      = ∫⁻ x in unitChartCubeStrip d (ε n), ‖g x‖ₑ ∂(volume.restrict (unitChartCubePos d)) := by
    intro n
    rw [Measure.restrict_restrict measurableSet_unitChartCubeStrip,
      inter_eq_self_of_subset_left unitChartCubeStrip_subset]
  refine (tendsto_congr heq).2 (tendsto_setLIntegral_zero hg ?_)
  have h : ∀ n, (volume.restrict (unitChartCubePos d) ∘ fun n ↦ unitChartCubeStrip d (ε n)) n
      = volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * ENNReal.ofReal (ε n) := fun n ↦ by
    simp only [Function.comp_apply]
    rw [Measure.restrict_apply measurableSet_unitChartCubeStrip,
      inter_eq_self_of_subset_left unitChartCubeStrip_subset, volume_unitChartCubeStrip (hε n)]
  refine (tendsto_congr h).2 ?_
  have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hε0)
    (a := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) (Or.inr measure_ball_lt_top.ne)
  simpa using this

/-- **A lower bound for the strip integral.** Let $\varepsilon \le 1$, let $v$ be an almost
everywhere measurable real function on $\mathbb{R}^{d+1}$, and let $x_0' \in \mathbb{R}^d$ and
$r, c \in \mathbb{R}$ with $r + \|x_0'\| \le 1$. If $c \le |v(x', t)|$ for every
$x' \in B'(x_0', r)$ and $t \in (0, \varepsilon)$, then
$$c \, \varepsilon \, |B'(x_0', r)| \le \int_{\{x \in Q_+ : x_N < \varepsilon\}} |v|.$$

The cylinder $B'(x_0', r) \times (0, \varepsilon)$ lies in the strip. The factors $c$ and
$\varepsilon$ enter through `ENNReal.ofReal`, so they count as $0$ when they are negative. -/
theorem le_lintegral_unitChartCubeStrip {ε : ℝ} (hε : ε ≤ 1)
    {v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hv : AEMeasurable v)
    {x₀' : EuclideanSpace ℝ (Fin d)} {r c : ℝ} (hr1 : r + ‖x₀'‖ ≤ 1)
    (hlow : ∀ x' ∈ ball x₀' r, ∀ t ∈ Ioo 0 ε, c ≤ |v (snocLast x' t)|) :
    ENNReal.ofReal c * (ENNReal.ofReal ε * volume (ball x₀' r))
      ≤ ∫⁻ x in unitChartCubeStrip d ε, ‖v x‖ₑ := by
  rw [lintegral_unitChartCubeStrip hε hv.enorm]
  calc ENNReal.ofReal c * (ENNReal.ofReal ε * volume (ball x₀' r))
      = ∫⁻ _ in ball x₀' r, ENNReal.ofReal c * ENNReal.ofReal ε := by
        rw [setLIntegral_const, mul_assoc]
    _ ≤ ∫⁻ x' in ball x₀' r, ∫⁻ t in Ioo 0 ε, ‖v (snocLast x' t)‖ₑ := by
        refine setLIntegral_mono' measurableSet_ball fun x' hx' ↦ ?_
        calc ENNReal.ofReal c * ENNReal.ofReal ε
            = ∫⁻ _ in Ioo 0 ε, ENNReal.ofReal c := by
              rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
          _ ≤ ∫⁻ t in Ioo 0 ε, ‖v (snocLast x' t)‖ₑ := by
              refine setLIntegral_mono' measurableSet_Ioo fun t ht ↦ ?_
              rw [Real.enorm_eq_ofReal_abs]
              exact ENNReal.ofReal_le_ofReal (hlow x' hx' t ht)
    _ ≤ ∫⁻ x' in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ t in Ioo 0 ε,
          ‖v (snocLast x' t)‖ₑ :=
        lintegral_mono_set (ball_subset_ball' (by rwa [dist_zero_right]))

end StripLimit

section Thm917

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open EuclideanSpace SobolevMultiIndex

/-- **Theorem 9.17, (ii) ⇒ (i), the computation on $Q_+$.** Let $1 \le p < \infty$ and let
$u \in W_0^{1,p}(Q_+)$. If the function of $u$ equals, almost everywhere on $Q_+$, a function
$\tilde u$ that is continuous on $\overline{Q_+}$, then $\tilde u = 0$ on $Q_0$. This is the
core of Theorem 9.17, (ii) ⇒ (i), of [brezis2011functional].

The proof tests the strip inequality $\int_{\{x_N < \varepsilon\}} |u| \le \varepsilon
\int_{\{x_N < \varepsilon\}} |\partial_N u|$
(`SobolevEuclideanZero.lintegral_unitChartCubeStrip_le`) at a point $x_0 \in Q_0$ with
$\tilde u(x_0) \neq 0$. By continuity, $|\tilde u| \ge |\tilde u(x_0)|/2$ on a cylinder
$B'(x_0', r) \times (0, \varepsilon)$, so the left side is at least $(|\tilde u(x_0)|/2) \,
\varepsilon \, |B'(x_0', r)|$. But $\int_{\{x_N < \varepsilon\}} |\partial_N u| \to 0$ as
$\varepsilon \to 0$, because $\partial_N u \in L^1(Q_+)$. This is a contradiction. -/
theorem SobolevEuclideanZero.eqOn_unitChartCubeZero_of_continuousOn_closure (hp' : p ≠ ⊤)
    {u : SobolevEuclidean (d + 1) 1 p (unitChartCubePosOpens d)}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p (unitChartCubePosOpens d))
    {ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hc : ContinuousOn ũ (closure (unitChartCubePos d)))
    (hũ : fn u =ᵐ[volume.restrict (unitChartCubePos d)] ũ) :
    EqOn ũ 0 (unitChartCubeZero d) := by
  intro x₀ hx₀
  by_contra hne
  rw [Pi.zero_apply] at hne
  -- the constant `c = |ũ x₀| / 2` and the radius `r`
  have hc0 : 0 < |ũ x₀| / 2 := by positivity
  have hx₀c : x₀ ∈ closure (unitChartCubePos d) :=
    frontier_subset_closure (unitChartCubeZero_subset_frontier_unitChartCubePos hx₀)
  have hx₀' : snocLast (init x₀) 0 = x₀ := by
    conv_rhs => rw [← snocLast_init_last x₀]
    rw [hx₀.2]
  have hG : ContinuousWithinAt (fun q : EuclideanSpace ℝ (Fin d) × ℝ ↦ ũ (snocLast q.1 q.2))
      ((fun q : EuclideanSpace ℝ (Fin d) × ℝ ↦ snocLast q.1 q.2) ⁻¹' closure (unitChartCubePos d))
      (init x₀, 0) := by
    refine ContinuousWithinAt.comp (f := fun q : EuclideanSpace ℝ (Fin d) × ℝ ↦ snocLast q.1 q.2)
      ?_ continuous_snocLast.continuousWithinAt (mapsTo_preimage _ _)
    simpa only [hx₀'] using hc x₀ hx₀c
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 hG _ hc0
  have hx₀1 : ‖init x₀‖ < 1 := hx₀.1.1
  obtain ⟨r, hrδ, hr1, hr⟩ : ∃ r : ℝ, r ≤ δ / 2 ∧ r + ‖init x₀‖ ≤ 1 ∧ 0 < r :=
    ⟨min (δ / 2) (1 - ‖init x₀‖), min_le_left _ _,
      by linarith [min_le_right (δ / 2) (1 - ‖init x₀‖)], lt_min (by positivity) (by linarith)⟩
  -- the lower bound on the cylinder
  have hlow : ∀ x' ∈ ball (init x₀) r, ∀ t ∈ Ioo 0 r,
      |ũ x₀| / 2 ≤ |ũ (snocLast x' t)| ∧ snocLast x' t ∈ unitChartCubePos d := by
    intro x' hx' t ht
    have hmem : snocLast x' t ∈ unitChartCubePos d := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [init_snocLast]
        calc ‖x'‖ = ‖x' - init x₀ + init x₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖x' - init x₀‖ + ‖init x₀‖ := norm_add_le _ _
          _ < r + ‖init x₀‖ := by
              have := mem_ball_iff_norm.1 hx'
              linarith
          _ ≤ 1 := hr1
      · rw [snocLast_apply_last, abs_of_pos ht.1]
        linarith [ht.2, norm_nonneg (init x₀)]
      · rw [snocLast_apply_last]; exact ht.1
    refine ⟨?_, hmem⟩
    have hdist : dist (x', t) (init x₀, 0) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨(mem_ball.1 hx').trans_le (by linarith), ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      linarith [ht.2]
    have := hδ' (x := (x', t)) (subset_closure hmem) hdist
    rw [hx₀', Real.dist_eq] at this
    have h2 := abs_sub_abs_le_abs_sub (ũ x₀) (ũ (snocLast x' t))
    rw [abs_sub_comm] at h2
    linarith
  -- the measurable representative `v`
  obtain ⟨v, hvdef⟩ : ∃ v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      v = (closure (unitChartCubePos d)).indicator ũ := ⟨_, rfl⟩
  have hvm : AEMeasurable v := by
    rw [hvdef]
    exact (aemeasurable_indicator_iff isClosed_closure.measurableSet).2
      (hc.aemeasurable isClosed_closure.measurableSet)
  have hveq : ∀ x ∈ unitChartCubePos d, v x = ũ x := fun x hx ↦ by
    rw [hvdef, Set.indicator_of_mem (subset_closure hx)]
  -- the strip inequality along `ε n = r / (n + 1)`
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun n : ℕ ↦ r / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hε1 : ∀ n, ε n ≤ 1 := fun n ↦ by
    rw [hεdef]
    exact (div_le_self hr.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])).trans
      (by linarith [norm_nonneg (init x₀)])
  have hεr : ∀ n, ε n ≤ r := fun n ↦ by
    rw [hεdef]
    exact div_le_self hr.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hε0 : ∀ n, 0 < ε n := fun n ↦ by
    rw [hεdef]
    positivity
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    simp only [hεdef]
    ring
  have hSQ : ∀ n, volume.restrict (unitChartCubeStrip d (ε n))
      ≤ volume.restrict (unitChartCubePos d) := fun n ↦
    Measure.restrict_mono unitChartCubeStrip_subset le_rfl
  have hstrip : ∀ n, ENNReal.ofReal (|ũ x₀| / 2) * volume (ball (init x₀) r)
      ≤ ∫⁻ x in unitChartCubeStrip d (ε n),
        ‖weakDeriv u (MultiIndexLE.single (Fin.last d)) x‖ₑ := by
    intro n
    have h1 : ∫⁻ x in unitChartCubeStrip d (ε n), ‖fn u x‖ₑ
        = ∫⁻ x in unitChartCubeStrip d (ε n), ‖v x‖ₑ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hũ.filter_mono (ae_mono (hSQ n)),
        ae_restrict_mem measurableSet_unitChartCubeStrip] with x hx hxS
      rw [hx, hveq x (unitChartCubeStrip_subset hxS)]
    have h2 := le_lintegral_unitChartCubeStrip (hε1 n) hvm hr1 (x₀' := init x₀) (c := |ũ x₀| / 2)
      (fun x' hx' t ht ↦ by
        have := hlow x' hx' t ⟨ht.1, ht.2.trans_le (hεr n)⟩
        rw [hveq _ this.2]
        exact this.1)
    have h3 := SobolevEuclideanZero.lintegral_unitChartCubeStrip_le hp' (hε1 n) hu
    rw [h1] at h3
    have h4 := h2.trans h3
    rw [mul_left_comm] at h4
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (hε0 n)).ne'
      ENNReal.ofReal_ne_top).1 h4
  -- the right side tends to `0`
  have hfin : IsFiniteMeasure (volume.restrict (unitChartCubePos d)) :=
    isFiniteMeasure_restrict.2 ((measure_mono (unitChartCubePos_subset.trans
      unitChartCube_subset_ball)).trans_lt measure_ball_lt_top).ne
  have hL1 : ∫⁻ x in unitChartCubePos d, ‖weakDeriv u (MultiIndexLE.single (Fin.last d)) x‖ₑ
      ≠ ⊤ :=
    (hasFiniteIntegral_iff_enorm.1 (memLp_one_iff_integrable.1
      ((Lp.memLp _).mono_exponent Fact.out)).hasFiniteIntegral).ne
  have hlim := tendsto_lintegral_unitChartCubeStrip hL1 hε1 hεt
  have h0 := ge_of_tendsto hlim (Eventually.of_forall hstrip)
  rw [nonpos_iff_eq_zero, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact (ENNReal.ofReal_pos.2 hc0).ne' h0
  · exact (Metric.measure_ball_pos volume (init x₀) hr).ne' h0

end Thm917

/-! ### Theorem 9.17, (ii) ⇒ (i): the reduction by local charts -/

section Thm917Chart

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

namespace ContDiffChart

variable (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- A local chart $H$ of $\Omega$ sends $\overline{Q_+}$ into $\bar\Omega$. -/
theorem mapsTo_closure_unitChartCubePos :
    MapsTo c.toFun (closure (unitChartCubePos d)) (closure (Ω : Set _)) := by
  have h1 : c.toFun '' closure (unitChartCubePos d) ⊆ closure (c.toFun '' unitChartCubePos d) :=
    (c.continuousOn.mono (closure_mono unitChartCubePos_subset)).image_closure
  rw [c.image_pos] at h1
  exact fun y hy ↦ closure_mono inter_subset_right (h1 (mem_image_of_mem _ hy))

/-- **The chart piece of Theorem 9.17, (ii) ⇒ (i).** Let $1 \le p < \infty$ and let $c$ be a local
chart $H : Q \to U$ of class $C^1$ of an open set $\Omega \subseteq \mathbb{R}^N$, such that $H$
restricted to $Q_+$ is a $C^1$ diffeomorphism onto $U \cap \Omega$ with Jacobians bounded by
$M$. Let $\theta$ be a smooth function with compact support such that
$\operatorname{supp} \theta \subseteq U$. Let $u \in W_0^{1,p}(\Omega)$ have a representative
$\tilde u$ that is continuous on $\bar\Omega$, and let $V \in W^{1,p}(U \cap \Omega)$ have the
function $u \theta$ almost everywhere on $U \cap \Omega$. Then $(\tilde u \theta) \circ H = 0$
on $Q_0$.

The transfer $V \circ H$ lies in $W_0^{1,p}(Q_+)$ (`SobolevMultiIndexZero.mul_contDiff_mem`,
`SobolevMultiIndexZero.compDiffeoL_mem`) and has the representative $(\tilde u \theta) \circ H$,
which is continuous on $\overline{Q_+}$. The computation on $Q_+$
(`SobolevEuclideanZero.eqOn_unitChartCubeZero_of_continuousOn_closure`) concludes. -/
theorem eqOn_unitChartCubeZero_aux (hp' : p ≠ ⊤) {M : ℝ}
    (hH : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCubePosOpens d : Set _)
      (c.opensInter : Set _) M)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : SobolevEuclidean (d + 1) 1 p Ω}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p Ω) {ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hũ : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {V : SobolevEuclidean (d + 1) 1 p c.opensInter}
    (hV : fn V =ᵐ[volume.restrict (c.opensInter : Set _)] fun x ↦ fn u x * θ x) :
    EqOn (fun y ↦ ũ (c.toFun y) * θ (c.toFun y)) 0 (unitChartCubeZero d) := by
  have hle : volume.restrict (c.opensInter : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ≤ volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    Measure.restrict_mono c.opensInter_le le_rfl
  -- `V ∈ W_0^{1,p}(U ∩ Ω)`
  have hVZ : V ∈ SobolevEuclideanZero (d + 1) 1 p c.opensInter :=
    SobolevMultiIndexZero.mul_contDiff_mem c.opensInter_le hθ hθc
      (fun x hx ↦ ⟨hθU hx.1, hx.2⟩) hu hV
  -- the transfer `V ∘ H ∈ W_0^{1,p}(Q_+)`
  have hWZ := SobolevMultiIndexZero.compDiffeoL_mem hp' hH hVZ
  -- its continuous representative `(ũ θ) ∘ H`
  have hH1 : ContinuousOn c.toFun (closure (unitChartCubePos d)) :=
    c.continuousOn.mono (closure_mono unitChartCubePos_subset)
  have hcont : ContinuousOn (fun y ↦ ũ (c.toFun y) * θ (c.toFun y))
      (closure (unitChartCubePos d)) :=
    (hc.comp hH1 c.mapsTo_closure_unitChartCubePos).mul (hθ.continuous.comp_continuousOn hH1)
  have hW : fn (compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume hH V)
      =ᵐ[volume.restrict (unitChartCubePos d)] fun y ↦ ũ (c.toFun y) * θ (c.toFun y) := by
    have h1 := fn_compDiffeoL hH V
    have h2 := hH.ae_comp_restrict (P := fun x ↦ fn V x = fn u x * θ x) hV
    have h3 := hH.ae_comp_restrict (P := fun x ↦ fn u x = ũ x) (hũ.filter_mono (ae_mono hle))
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    rw [hy1, hy2, hy3]
  exact SobolevEuclideanZero.eqOn_unitChartCubeZero_of_continuousOn_closure hp' hWZ hcont hW

end ContDiffChart

/-- **Theorem 9.17, (ii) ⇒ (i)**, for an open set of class $C^1$. Let $1 \le p < \infty$, let
$\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be an open set of class $C^1$, and let
$u \in W_0^{1,p}(\Omega)$. If the function of $u$ equals, almost everywhere on $\Omega$, a
function $\tilde u$ that is continuous on $\bar\Omega$, then $\tilde u = 0$ on $\partial\Omega$.
This is Theorem 9.17, (ii) ⇒ (i), of [brezis2011functional], where "using local charts this is
reduced to" the computation on $Q_+$. Together with
`SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`, this is Theorem 9.17.

The hypothesis on $\Omega$ is `IsContDiffChartDomain 1`. For $x_0 \in \partial\Omega$, take a
chart $c$ at $x_0$ and a smooth $\theta$ with compact support in $U$ and $\theta = 1$ near
$x_0$. Then $u \theta$ lies in $W_0^{1,p}(U \cap \Omega)$ and transfers along the chart to
$W_0^{1,p}(Q_+)$ with the continuous representative $(\tilde u \theta) \circ H$, which vanishes
on $Q_0$ (`ContDiffChart.eqOn_unitChartCubeZero_aux`). Since $x_0 = H(y_0)$ with $y_0 \in Q_0$,
$\tilde u(x_0) = \tilde u(x_0) \theta(x_0) = 0$. -/
theorem SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p Ω)
    {ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hũ : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    EqOn ũ 0 (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  intro x₀ hx₀
  obtain ⟨c, hx₀U⟩ := hΩ.exists_chart hx₀
  -- the cut-off `θ`, equal to `1` near `x₀`, with compact support in `c.U`
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 c.isOpen_U x₀ hx₀U
  obtain ⟨θ, hθ, hθ1, hθU, -⟩ := (isCompact_closedBall x₀ (r / 2)).exists_contDiff_eqOn_one
    c.isOpen_U ((closedBall_subset_ball (by linarith)).trans hrU)
  have hθc : HasCompactSupport θ :=
    c.isCompact_closure_U.of_isClosed_subset (isClosed_tsupport _) (hθU.trans subset_closure)
  obtain ⟨M₀, hM₀⟩ := hθc.exists_bound_of_continuous hθ.continuous
  obtain ⟨M₁, hM₁⟩ := (hθc.fderiv ℝ).exists_bound_of_continuous (hθ.continuous_fderiv (by simp))
  have hM : ∀ x, |θ x| ≤ M₀ + M₁ ∧ ‖fderiv ℝ θ x‖ ≤ M₀ + M₁ := fun x ↦ by
    have h0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ x)
    have h1 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ x)
    exact ⟨(Real.norm_eq_abs _).symm.trans_le ((hM₀ x).trans (by linarith)),
      (hM₁ x).trans (by linarith)⟩
  -- `V ∈ W^{1,p}(U ∩ Ω)` with function `u θ`
  obtain ⟨V, hV⟩ := ((memSobolevMultiIndex (restrictL ℝ
    (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume c.opensInter_le u)).contDiff_mul
    Fact.out hθ hM).exists_sobolevMultiIndex
  have hV' : fn V =ᵐ[volume.restrict (c.opensInter : Set _)] fun x ↦ fn u x * θ x := by
    filter_upwards [hV, fn_restrictL c.opensInter_le u] with x h1 h2
    rw [h1, h2, mul_comm]
  -- the chart piece
  obtain ⟨M, hH⟩ := c.isDiffeoOnWithBoundedJacobian_pos le_rfl Ω.isOpen
  have h0 := c.eqOn_unitChartCubeZero_aux hp' hH hθ hθc hθU hu hũ hc hV'
    ((c.invFun_mem_zero_iff hx₀U).2 hx₀)
  simp only [Pi.zero_apply, c.toFun_invFun hx₀U] at h0 ⊢
  rwa [hθ1 (mem_closedBall_self (by positivity)), Pi.one_apply, mul_one] at h0

end Thm917Chart

/-! ### Proposition 9.20: the dual $W^{-1,p'}(\Omega)$ -/

section Dual

/-! ### The Hahn–Banach theorem along a map bounded below, and duals of products of $L^p$ spaces -/

/-- **The Hahn–Banach theorem along a linear map with bounded inverse.** Let $V$ and $W$ be real
normed spaces, let $g : V \to W$ be linear, and let $C \ge 0$ with $\|v\| \le C \|g v\|$ for
every $v \in V$. Then for every continuous linear functional $F$ on $V$ there is a continuous
linear functional $\Phi$ on $W$ with $\Phi \circ g = F$ and $\|\Phi\| \le C \|F\|$.

The map $g$ is injective, $F \circ g^{-1}$ is a functional of norm at most $C \|F\|$ on the
range of $g$, and the Hahn–Banach theorem (`exists_extension_norm_eq`) extends it. -/
theorem exists_strongDual_comp_eq_of_norm_le {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (g : V →ₗ[ℝ] W) {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ v, ‖v‖ ≤ C * ‖g v‖) (F : StrongDual ℝ V) :
    ∃ Φ : StrongDual ℝ W, (∀ v, Φ (g v) = F v) ∧ ‖Φ‖ ≤ C * ‖F‖ := by
  have hinj : Function.Injective g := by
    intro u v huv
    have h := hg (u - v)
    rw [map_sub, huv, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
  obtain ⟨e, he⟩ : ∃ e : V ≃ₗ[ℝ] LinearMap.range g,
      ∀ v, e v = ⟨g v, LinearMap.mem_range_self _ v⟩ :=
    ⟨LinearEquiv.ofInjective g hinj, fun _ ↦ rfl⟩
  have hbound : ∀ w : LinearMap.range g,
      ‖(F.toLinearMap ∘ₗ e.symm.toLinearMap) w‖ ≤ (C * ‖F‖) * ‖w‖ := by
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe, he]
    change ‖F v‖ ≤ (C * ‖F‖) * ‖g v‖
    calc ‖F v‖ ≤ ‖F‖ * ‖v‖ := F.le_opNorm v
      _ ≤ ‖F‖ * (C * ‖g v‖) := mul_le_mul_of_nonneg_left (hg v) (norm_nonneg _)
      _ = (C * ‖F‖) * ‖g v‖ := by ring
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_extension_norm_eq (LinearMap.range g)
    ((F.toLinearMap ∘ₗ e.symm.toLinearMap).mkContinuous (C * ‖F‖) hbound)
  refine ⟨Φ, fun v ↦ ?_, hΦn.trans_le (LinearMap.mkContinuous_norm_le _
    (mul_nonneg hC (norm_nonneg _)) hbound)⟩
  have h2 : ((F.toLinearMap ∘ₗ e.symm.toLinearMap).mkContinuous (C * ‖F‖) hbound)
      ⟨g v, LinearMap.mem_range_self _ v⟩ = F v := by
    rw [LinearMap.mkContinuous_apply, ← he, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rfl
  exact (hΦ ⟨g v, LinearMap.mem_range_self _ v⟩).trans h2

/-- Let $\nu$ be a $\sigma$-finite measure, let $1 \le p < \infty$ and let $q$ be the conjugate
exponent. Let $\kappa$ be a finite index set, and let $\Phi$ be a continuous linear functional
on the $\ell^p$ product of $\kappa$ copies of $L^p(\nu)$. Then there are $f_i \in L^q(\nu)$,
$i \in \kappa$, with $\|f_i\| \le \|\Phi\|$ and
$$\Phi(x) = \sum_{i \in \kappa} \int f_i \, x_i \, d\nu$$
for every $x$ in the product.

The restriction of $\Phi$ to each factor is a functional on $L^p(\nu)$ of norm at most
$\|\Phi\|$, and the Riesz representation theorem (`MeasureTheory.Lp.dualEquiv`, Theorems 4.11
and 4.14 of [brezis2011functional]) represents it isometrically by a function of $L^q(\nu)$.
With `exists_strongDual_comp_eq_of_norm_le`, this is the common core of the proofs of
Propositions 8.14 and 9.20 of [brezis2011functional]. -/
theorem MeasureTheory.Lp.strongDual_piLp_exists_forall_eq_sum_integral {α : Type*}
    [MeasurableSpace α] {ν : Measure α} [SigmaFinite ν] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] [p.HolderConjugate q] (hp : p ≠ ⊤) {κ : Type*} [Fintype κ]
    (Φ : StrongDual ℝ (PiLp p fun _ : κ ↦ Lp ℝ p ν)) :
    ∃ f : κ → Lp ℝ q ν, (∀ x : PiLp p fun _ : κ ↦ Lp ℝ p ν, Φ x = ∑ i, ∫ t, f i t * x i t ∂ν) ∧
      ∀ i, ‖f i‖ ≤ ‖Φ‖ := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Lp ℝ q ν ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p ν),
      ∀ (u : Lp ℝ q ν) (f : Lp ℝ p ν), e u f = ∫ x, u x * f x ∂ν :=
    ⟨Lp.dualEquiv ℝ p q ν hp, fun u f ↦ Lp.dualEquiv_apply hp u f⟩
  refine ⟨fun i ↦ e.symm (Φ.comp (PiLp.singleL p (X := fun _ : κ ↦ Lp ℝ p ν) i)),
    fun x ↦ ?_, fun i ↦ ?_⟩
  · rw [PiLp.strongDual_apply_eq_sum Φ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← he, LinearIsometryEquiv.apply_symm_apply]
  · rw [LinearIsometryEquiv.norm_map]
    exact PiLp.norm_strongDual_comp_singleL_le Φ i

/-! ### The dual of $W_0^{1,p}(\Omega)$ -/

namespace SobolevEuclideanZero

variable {N : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The dual $W^{-1,p'}(\Omega)$ of $W_0^{1,p}(\Omega)$.** Let $\Omega \subseteq \mathbb{R}^N$ be
open, let $1 \le p < \infty$ and let $p'$ be the conjugate exponent. Then for every continuous
linear functional $F$ on $W_0^{1,p}(\Omega)$ there are $f_0, f_1, \dots, f_N \in L^{p'}(\Omega)$
with $\|f_\alpha\|_{L^{p'}(\Omega)} \le \|F\|$ for every $\alpha$ and
$$F(v) = \int_\Omega f_0 v + \sum_{i=1}^N \int_\Omega f_i \, \partial_i v$$
for every $v \in W_0^{1,p}(\Omega)$. This is Proposition 9.20 of [brezis2011functional].

The functions $f_\alpha$ are indexed by the multi-indices $\alpha$ with $|\alpha| \le 1$, and
the sum is over all of them, with $\partial^0 v = v$. The source states the identity
$\|F\| = \max_\alpha \|f_\alpha\|_{p'}$, which refers to its norm $\sum_\alpha \|h_\alpha\|_p$
on the product. For the $\ell^p$ sum norm of `SobolevMultiIndexTuple`, the one-sided bound is
what is stated here. The proof adapts that of Proposition 8.14, as the source says. The map
$v \mapsto (\partial^\alpha v)_\alpha$ is an isometry of $W_0^{1,p}(\Omega)$ into the $\ell^p$
product of $N + 1$ copies of $L^p(\Omega)$. So $F$ extends by the Hahn–Banach theorem to a
functional of the same norm on the product (`exists_strongDual_comp_eq_of_norm_le`), which the
Riesz representation theorem on each factor represents
(`MeasureTheory.Lp.strongDual_piLp_exists_forall_eq_sum_integral`). -/
theorem exists_dual_repr [p.HolderConjugate q] (hp : p ≠ ⊤)
    (F : StrongDual ℝ (SobolevEuclideanZero N 1 p Ω)) :
    ∃ f : MultiIndexLE (Fin N) 1 → Lp ℝ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      (∀ v : SobolevEuclideanZero N 1 p Ω,
        F v = ∑ α, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          f α x * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean N 1 p Ω) α x) ∧
        ∀ α, ‖f α‖ ≤ ‖F‖ := by
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  -- the isometric inclusion of `W_0^{1,p}(Ω)` into the ambient `ℓ^p` product
  obtain ⟨ι, hι⟩ : ∃ ι : SobolevEuclideanZero N 1 p Ω →ₗᵢ[ℝ]
      SobolevMultiIndexTuple ℝ (Fin N) 1 p Ω volume, ∀ v : SobolevEuclideanZero N 1 p Ω,
        ι v = ((v : SobolevEuclidean N 1 p Ω) : SobolevMultiIndexTuple ℝ (Fin N) 1 p Ω volume) :=
    ⟨(SobolevMultiIndex ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).subtypeₗᵢ.comp
      (SobolevEuclideanZero N 1 p Ω).subtypeₗᵢ, fun _ ↦ rfl⟩
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_strongDual_comp_eq_of_norm_le ι.toLinearMap zero_le_one
    (fun v ↦ by rw [one_mul, LinearIsometry.coe_toLinearMap, ι.norm_map]) F
  rw [one_mul] at hΦn
  obtain ⟨f, hf, hfn⟩ := Lp.strongDual_piLp_exists_forall_eq_sum_integral (q := q) hp Φ
  refine ⟨f, fun v ↦ ?_, fun α ↦ (hfn α).trans hΦn⟩
  rw [← hΦ v, hf, LinearIsometry.coe_toLinearMap, hι]
  rfl

variable (N p Ω) in
/-- The **gradient** $v \mapsto \nabla v = (\partial_i v)_i$ on $W_0^{1,p}(\Omega)$, as a linear map
into the $\ell^p$ product of $N$ copies of $L^p(\Omega)$. -/
noncomputable def gradₗ : SobolevEuclideanZero N 1 p Ω →ₗ[ℝ]
    PiLp p fun _ : Fin N ↦ Lp ℝ p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) where
  toFun v := SobolevMultiIndex.grad (v : SobolevEuclidean N 1 p Ω)
  map_add' _ _ := SobolevMultiIndex.grad_add _ _
  map_smul' _ _ := SobolevMultiIndex.grad_smul _ _

/-- The value `SobolevEuclideanZero.gradₗ N p Ω v` is the gradient tuple `SobolevMultiIndex.grad v`.
-/
theorem gradₗ_apply (v : SobolevEuclideanZero N 1 p Ω) :
    gradₗ N p Ω v = SobolevMultiIndex.grad (v : SobolevEuclidean N 1 p Ω) :=
  rfl

/-- **Poincaré's inequality for the gradient map.** Let $\Omega \subseteq B(0, R)$ be open in
$\mathbb{R}^{d+1}$ with $R \ge 0$, and let $1 \le p < \infty$. Then for every
$v \in W_0^{1,p}(\Omega)$,
$$\|v\|_{W^{1,p}(\Omega)} \le \big(1 + (2R)^p\big)^{1/p} \|\nabla v\|_{L^p(\Omega)}.$$

This is `SobolevEuclideanZero.norm_le_gradNorm` for the map `SobolevEuclideanZero.gradₗ`. -/
theorem norm_le_mul_norm_gradₗ {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hp : p ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    ‖v‖ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal) * ‖gradₗ (d + 1) p Ω v‖ :=
  norm_le_gradNorm hp hR hΩ v

/-- **Proposition 9.20 on a bounded open set: $f_0 = 0$.** Let $\Omega \subseteq B(0, R)$ be open in
$\mathbb{R}^N$, $N = d + 1$, with $R \ge 0$, let $1 \le p < \infty$ and let $p'$ be the
conjugate exponent. Then for every continuous linear functional $F$ on $W_0^{1,p}(\Omega)$ there
are $f_1, \dots, f_N \in L^{p'}(\Omega)$ with
$$F(v) = \sum_{i=1}^N \int_\Omega f_i \, \partial_i v \quad\text{for every } v \in
  W_0^{1,p}(\Omega), \qquad \|f_i\|_{L^{p'}(\Omega)} \le \big(1 + (2R)^p\big)^{1/p} \|F\|.$$
This is the last sentence of Proposition 9.20 of [brezis2011functional].

By Poincaré's inequality (`SobolevEuclideanZero.norm_le_mul_norm_gradₗ`), the gradient
$v \mapsto \nabla v$ is injective on $W_0^{1,p}(\Omega)$ with bounded inverse. So $F$ extends
along it to a functional on the $\ell^p$ product of $N$ copies of $L^p(\Omega)$
(`exists_strongDual_comp_eq_of_norm_le`), which
`MeasureTheory.Lp.strongDual_piLp_exists_forall_eq_sum_integral` represents, as in the proof of
Proposition 8.14. -/
theorem exists_dual_repr_of_isBounded {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    [p.HolderConjugate q] (hp : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (F : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    ∃ f : Fin (d + 1) → Lp ℝ q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      (∀ v : SobolevEuclideanZero (d + 1) 1 p Ω,
        F v = ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          f i x * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 p Ω)
            (MultiIndexLE.single i) x) ∧
        ∀ i, ‖f i‖ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal) * ‖F‖ := by
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_strongDual_comp_eq_of_norm_le (gradₗ (d + 1) p Ω)
    (by positivity) (norm_le_mul_norm_gradₗ hp hR hΩ) F
  obtain ⟨f, hf, hfn⟩ := Lp.strongDual_piLp_exists_forall_eq_sum_integral (q := q) hp Φ
  refine ⟨f, fun v ↦ ?_, fun i ↦ (hfn i).trans hΦn⟩
  rw [← hΦ v, hf]
  simp only [gradₗ_apply, SobolevMultiIndex.grad_apply]

end SobolevEuclideanZero

end Dual


/-! ### The Gelfand triple $H^1_0(\Omega) \subset L^2(\Omega) \subset H^{-1}(\Omega)$ -/

section GelfandTriple

open scoped InnerProductSpace

namespace SobolevEuclideanZero

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

variable (N Ω) in
/-- The **inclusion** $L^2(\Omega) \subset H^{-1}(\Omega)$, $f \mapsto (v \mapsto \int_\Omega f v)$,
for an open $\Omega \subseteq \mathbb{R}^N$. It is the transpose of the inclusion
$H^1_0(\Omega) \subset L^2(\Omega)$ (`SobolevMultiIndexZero.fnL`), composed with the
self-duality of $L^2(\Omega)$. This is the inclusion of §9.4 of [brezis2011functional], "The
Dual Space of $W_0^{1,p}(\Omega)$", Notation. -/
def toDualL2 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
    StrongDual ℝ (SobolevEuclideanZero N 1 2 Ω) :=
  ((ContinuousLinearMap.compL ℝ (SobolevEuclideanZero N 1 2 Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ℝ).flip
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)).comp
    (innerSL ℝ)

/-- For $f \in L^2(\Omega)$ and $v \in H^1_0(\Omega)$, the value of
`SobolevEuclideanZero.toDualL2 N Ω f` at $v$ is the inner product
$\langle f, v \rangle_{L^2(\Omega)}$. -/
theorem toDualL2_apply_inner (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 2 Ω) :
    toDualL2 N Ω f v
      = ⟪f, SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume v⟫_ℝ :=
  rfl

/-- For $f \in L^2(\Omega)$ and $v \in H^1_0(\Omega)$, the value of
`SobolevEuclideanZero.toDualL2 N Ω f` at $v$ is $\int_\Omega f v$. -/
theorem toDualL2_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 2 Ω) :
    toDualL2 N Ω f v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      f x * SobolevMultiIndex.fn (v : SobolevEuclidean N 1 2 Ω) x := by
  rw [toDualL2_apply_inner, L2.inner_eq_integral_mul]
  rfl

/-- **A bounded linear map into the dual of a reflexive space whose range separates points has dense
range.** Let $X$ be a reflexive real normed space, let $L$ be a real normed space, and let
$j : L \to X^*$ be a bounded linear map. If every $v \in X$ with $j(f)(v) = 0$ for all $f \in L$
is $0$, then $j$ has dense range.

By reflexivity, a functional on $X^*$ that vanishes on the range of $j$ is the evaluation at
some $v$, and then $v = 0$. A closed proper subspace of $X^*$ would be separated from a point by
a nonzero functional (`Submodule.exists_dual_eq_zero_of_notMem`). -/
theorem _root_.denseRange_of_forall_apply_eq_zero {X L : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedSpace.IsReflexive ℝ X] [NormedAddCommGroup L] [NormedSpace ℝ L]
    (j : L →L[ℝ] StrongDual ℝ X) (h : ∀ v : X, (∀ f, j f v = 0) → v = 0) : DenseRange j := by
  obtain ⟨M, hM⟩ : ∃ M : Submodule ℝ (StrongDual ℝ X),
      M = (LinearMap.range (j : L →ₗ[ℝ] StrongDual ℝ X)).topologicalClosure := ⟨_, rfl⟩
  have hMtop : M = ⊤ := by
    by_contra hne
    obtain ⟨z, hz⟩ : ∃ z, z ∉ M := by
      by_contra h'
      push Not at h'
      exact hne (Submodule.eq_top_iff'.2 h')
    obtain ⟨Λ, -, hΛ0, hΛz⟩ :=
      M.exists_dual_eq_zero_of_notMem (hM ▸ Submodule.isClosed_topologicalClosure _) hz
    obtain ⟨v, rfl⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := ℝ) Λ
    have hv : v = 0 := h v fun f ↦ by
      have := hΛ0 (j f) (hM ▸ Submodule.le_topologicalClosure _ ⟨f, rfl⟩)
      rwa [NormedSpace.dual_def] at this
    apply hΛz
    rw [hv, map_zero]
    rfl
  have hrange : Set.range j = ((LinearMap.range (j : L →ₗ[ℝ] StrongDual ℝ X)) : Set _) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  rw [DenseRange, hrange, Submodule.dense_iff_topologicalClosure_eq_top, ← hM, hMtop]

/-!
### The triple $W_0^{1,p}(\Omega) \subset L^2(\Omega) \subset W^{-1,p'}(\Omega)$ for general $p$
-/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **inclusion** $L^2(\Omega) \subset W^{-1,p'}(\Omega)$ along a bounded linear map
$\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$: the map $f \mapsto (v \mapsto \langle f, \iota v
\rangle_{L^2(\Omega)})$. It is the transpose of $\iota$, composed with the self-duality of
$L^2(\Omega)$.

The map $\iota$ is a parameter. At $p = 2$ it is `SobolevMultiIndexZero.fnL`
(`SobolevEuclideanZero.toDualL2_eq_toDualOfL2`). For $2N/(N+2) \le p$ it is the bounded
inclusion of Remark 20, `SobolevEuclideanZero.isContinuousEmbedding_toLp` in
`Numlib.Analysis.Sobolev.EmbeddingDomain`, which this module does not import. -/
def toDualOfL2 (ι : SobolevEuclideanZero N 1 p Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      StrongDual ℝ (SobolevEuclideanZero N 1 p Ω) :=
  ((ContinuousLinearMap.compL ℝ (SobolevEuclideanZero N 1 p Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ℝ).flip ι).comp (innerSL ℝ)

/-- For $f \in L^2(\Omega)$ and $v \in W_0^{1,p}(\Omega)$, the value of
`SobolevEuclideanZero.toDualOfL2 ι f` at $v$ is $\langle f, \iota v \rangle_{L^2(\Omega)}$. -/
theorem toDualOfL2_apply_inner (ι : SobolevEuclideanZero N 1 p Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 p Ω) : toDualOfL2 ι f v = ⟪f, ι v⟫_ℝ :=
  rfl

/-- The inclusion `SobolevEuclideanZero.toDualL2` is `SobolevEuclideanZero.toDualOfL2` along the
inclusion $H^1_0(\Omega) \subset L^2(\Omega)$, `SobolevMultiIndexZero.fnL`. -/
theorem toDualL2_eq_toDualOfL2 :
    toDualL2 N Ω = toDualOfL2
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume) :=
  rfl

/-- A bounded linear map $\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$ **sends each element to its
function** if $\iota v$ equals the function of $v$ almost everywhere on $\Omega$, for every
$v \in W_0^{1,p}(\Omega)$. Such a map is the inclusion of the Gelfand triple. At $p = 2$,
`SobolevMultiIndexZero.fnL` is one (`SobolevEuclideanZero.isFnInclusion_fnL`). -/
def IsFnInclusion (ι : SobolevEuclideanZero N 1 p Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop :=
  ∀ v : SobolevEuclideanZero N 1 p Ω, (ι v : EuclideanSpace ℝ (Fin N) → ℝ)
    =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω)

variable {ι : SobolevEuclideanZero N 1 p Ω →L[ℝ]
  Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- The predicate `SobolevEuclideanZero.IsFnInclusion ι` holds if and only if $\iota v$ equals the
function of $v$ almost everywhere on $\Omega$, for every $v \in W_0^{1,p}(\Omega)$. -/
theorem isFnInclusion_iff : IsFnInclusion ι ↔ ∀ v : SobolevEuclideanZero N 1 p Ω,
    (ι v : EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω) :=
  Iff.rfl

/-- The inclusion $H^1_0(\Omega) \subset L^2(\Omega)$, `SobolevMultiIndexZero.fnL`, sends each
element to its function. -/
theorem isFnInclusion_fnL :
    IsFnInclusion (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume) :=
  fun _ ↦ Filter.EventuallyEq.rfl

/-- Let $\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$ send each element to its function. Then for
$f \in L^2(\Omega)$ and $v \in W_0^{1,p}(\Omega)$, the value of
`SobolevEuclideanZero.toDualOfL2 ι f` at $v$ is $\int_\Omega f v$. -/
theorem toDualOfL2_apply
    (hι : IsFnInclusion ι)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 p Ω) :
    toDualOfL2 ι f v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      f x * SobolevMultiIndex.fn (v : SobolevEuclidean N 1 p Ω) x := by
  rw [toDualOfL2_apply_inner, L2.inner_eq_integral_mul]
  exact integral_congr_ae (Filter.EventuallyEq.rfl.mul (hι v))

/-- A bounded linear map $\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$ that sends each element to its
function is injective. The function determines the element
(`SobolevMultiIndexZero.fnL_injective`). -/
theorem injective_of_forall_ae_eq
    (hι : IsFnInclusion ι) :
    Function.Injective ι := fun u v huv ↦ by
  refine SobolevMultiIndexZero.fnL_injective (Lp.ext ?_)
  rw [SobolevMultiIndexZero.fnL_apply, SobolevMultiIndexZero.fnL_apply]
  exact (hι u).symm.trans ((Lp.ext_iff.1 huv).trans (hι v))

/-- A bounded linear map $\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$ that sends each element to its
function has dense range. Its range contains the test functions, which are dense in
$L^2(\Omega)$ (`MeasureTheory.Lp.dense_contDiff_tsupport_subset`). -/
theorem denseRange_of_forall_ae_eq
    (hι : IsFnInclusion ι) :
    DenseRange ι := by
  refine (Lp.dense_contDiff_tsupport_subset (F := ℝ) (μ := volume) (p := 2) Ω.isOpen
    ENNReal.ofNat_ne_top).mono ?_
  rintro f ⟨g, hfg, hgc, hgs, hgΩ⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(Ω, ℝ), (φ : EuclideanSpace ℝ (Fin N) → ℝ) = g :=
    ⟨⟨g, hgs, hgc, hgΩ⟩, rfl⟩
  obtain ⟨u, hu, hφu⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := p) (μ := volume)
  refine ⟨⟨u, SobolevMultiIndexZero.testFunctions_le hu⟩, Lp.ext ((hι _).trans ?_)⟩
  refine hφu.trans ?_
  rw [hφ]
  exact hfg.symm

/-- Let $\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$ send each element to its function. Then the
inclusion $L^2(\Omega) \subset W^{-1,p'}(\Omega)$ along $\iota$ is injective.

A function of $L^2(\Omega)$ whose integral against every test function vanishes is zero
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem toDualOfL2_injective
    (hι : IsFnInclusion ι) :
    Function.Injective (toDualOfL2 ι) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf ↦ ?_
  have hΩm := Ω.isOpen.measurableSet
  have hloc : LocallyIntegrableOn (⇑f) Ω (volume : Measure (EuclideanSpace ℝ (Fin N))) :=
    (Lp.memLp f).locallyIntegrableOn one_le_two
  have key := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc
    fun g hgs hgc hgΩ ↦ ?_
  · refine Lp.ext ?_
    filter_upwards [(ae_restrict_iff' hΩm).2 key, Lp.coeFn_zero ℝ 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))] with x hx hx0
    rw [hx, hx0]
    rfl
  · obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(Ω, ℝ), (φ : EuclideanSpace ℝ (Fin N) → ℝ) = g :=
      ⟨⟨g, hgs, hgc, hgΩ⟩, rfl⟩
    obtain ⟨u, hu, hφu⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
      (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := p) (μ := volume)
    have h1 := DFunLike.congr_fun hf ⟨u, SobolevMultiIndexZero.testFunctions_le hu⟩
    rw [toDualOfL2_apply hι, zero_apply] at h1
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgΩ h), zero_smul], ← h1, ← hφ]
    refine integral_congr_ae (hφu.mono fun x hx ↦ ?_)
    simp only [smul_eq_mul, mul_comm, hx]

/-- Let $W_0^{1,p}(\Omega)$ be reflexive, which holds for $1 < p < \infty$, and let
$\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$ send each element to its function. Then the
inclusion $L^2(\Omega) \subset W^{-1,p'}(\Omega)$ along $\iota$ has dense range.

The range separates points: if $\langle f, \iota v \rangle = 0$ for all $f \in L^2(\Omega)$,
then $f = \iota v$ gives $\iota v = 0$, hence $v = 0$. So `denseRange_of_forall_apply_eq_zero`
applies. -/
theorem denseRange_toDualOfL2 [NormedSpace.IsReflexive ℝ (SobolevEuclideanZero N 1 p Ω)]
    (hι : IsFnInclusion ι) :
    DenseRange (toDualOfL2 ι) :=
  denseRange_of_forall_apply_eq_zero _ fun v hv ↦ by
    have h := hv (ι v)
    rw [toDualOfL2_apply_inner, real_inner_self_eq_norm_sq] at h
    exact injective_of_forall_ae_eq hι
      ((norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)).trans (map_zero _).symm)

/-- **The Gelfand triple $W_0^{1,p}(\Omega) \subset L^2(\Omega) \subset W^{-1,p'}(\Omega)$.** Let
$\Omega \subseteq \mathbb{R}^N$ be open, let $1 < p < \infty$, and let
$\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$ be a bounded linear map that sends each element to
its function. Then $\iota$ and the inclusion $L^2(\Omega) \subset W^{-1,p'}(\Omega)$,
$f \mapsto (v \mapsto \int_\Omega f v)$, are both injective with dense range.

This is the statement of §9.4 of [brezis2011functional], "The Dual Space of
$W_0^{1,p}(\Omega)$", Notation: "if $\Omega$ is bounded then $W_0^{1,p}(\Omega) \subset
L^2(\Omega) \subset W^{-1,p'}(\Omega)$ if $2N/(N+2) \le p < \infty$, with continuous and dense
injections; if $\Omega$ is not bounded, the same holds for $2N/(N+2) \le p \le 2$". The second
inclusion is `SobolevEuclideanZero.toDualOfL2 ι`. Remark 20 supplies $\iota$
(`SobolevEuclideanZero.isContinuousEmbedding_toLp` at $q = 2$); this is where the condition
$2N/(N+2) \le p$ enters, together with $L^p(\Omega) \subset L^2(\Omega)$ on a bounded $\Omega$
for $p > 2$. The density of the second inclusion uses the reflexivity of $W_0^{1,p}(\Omega)$,
and it fails at $p = 1$, which the range of the source allows for $N \le 2$: $W_0^{1,1}(\Omega)$
contains a complemented copy of $\ell^1$, so its dual contains $\ell^\infty$ and is not
separable, while the range of a bounded map from the separable space $L^2(\Omega)$ is separable. -/
theorem gelfandTriple_of_forall_ae_eq (hp : 1 < p) (hp' : p ≠ ⊤)
    (hι : IsFnInclusion ι) :
    Function.Injective ι ∧ DenseRange ι ∧
      Function.Injective (toDualOfL2 ι) ∧ DenseRange (toDualOfL2 ι) := by
  have : Fact (1 < p) := ⟨hp⟩
  have : Fact (p ≠ (⊤ : ℝ≥0∞)) := ⟨hp'⟩
  exact ⟨injective_of_forall_ae_eq hι, denseRange_of_forall_ae_eq hι, toDualOfL2_injective hι,
    denseRange_toDualOfL2 hι⟩

/-- The inclusion $H^1_0(\Omega) \subset L^2(\Omega)$ has dense range. Its range contains the test
functions, which are dense in $L^2(\Omega)$ (`MeasureTheory.Lp.dense_contDiff_tsupport_subset`). -/
theorem denseRange_fnL :
    DenseRange (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume) :=
  denseRange_of_forall_ae_eq isFnInclusion_fnL

/-- The inclusion $L^2(\Omega) \subset H^{-1}(\Omega)$ is injective. A function of $L^2(\Omega)$
whose integral against every test function vanishes is zero
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem toDualL2_injective : Function.Injective (toDualL2 N Ω) :=
  toDualOfL2_injective isFnInclusion_fnL

/-- The inclusion $L^2(\Omega) \subset H^{-1}(\Omega)$ has dense range.

The space $H^1_0(\Omega)$ is a Hilbert space, hence reflexive. The range separates points: if
$\int_\Omega f v = 0$ for all $f \in L^2(\Omega)$, then $f = v$ gives $\|v\|_2 = 0$. So
`denseRange_of_forall_apply_eq_zero` applies. -/
theorem denseRange_toDualL2 : DenseRange (toDualL2 N Ω) :=
  denseRange_toDualOfL2 isFnInclusion_fnL

/-- **The Gelfand triple $H^1_0(\Omega) \subset L^2(\Omega) \subset H^{-1}(\Omega)$.** Let
$\Omega \subseteq \mathbb{R}^N$ be open. Then the inclusion $H^1_0(\Omega) \to L^2(\Omega)$ and
the inclusion $L^2(\Omega) \to H^{-1}(\Omega)$, $f \mapsto (v \mapsto \int_\Omega f v)$, are
both injective with dense range: "these injections are continuous and dense". This is the
statement of §9.4 of [brezis2011functional], "The Dual Space of $W_0^{1,p}(\Omega)$", Notation.

The first inclusion is `SobolevMultiIndexZero.fnL`, and the second is
`SobolevEuclideanZero.toDualL2`. -/
theorem gelfandTriple :
    Function.Injective (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
        1 2 Ω volume) ∧
      DenseRange (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
        volume) ∧
      Function.Injective (toDualL2 N Ω) ∧ DenseRange (toDualL2 N Ω) :=
  ⟨SobolevMultiIndexZero.fnL_injective, denseRange_fnL, toDualL2_injective, denseRange_toDualL2⟩

end SobolevEuclideanZero

end GelfandTriple

/-!
### Remark 17, the punctured space: the capacity of a point

For $N \ge 2$ and $1 \le p \le N$, $W_0^{1,p}(\mathbb{R}^N \setminus \{0\}) = W^{1,p}(\mathbb{R}^N
\setminus \{0\})$. The cut-off near $0$ is the average $\eta_n(x) = (n+1)^{-1} \sum_{k \le n}
\eta(3^k x)$ of contractions of one cut-off $\eta$. The gradients of the summands are supported in
disjoint shells, so $\|\nabla \eta_n\|_{L^N}^N \le C (n+1)^{1-N} \to 0$, and Hölder's inequality
gives $\|\nabla \eta_n\|_{L^p} \to 0$ for every $p \le N$. One construction covers $p < N$ and the
endpoint $p = N$, with no radial integration.
-/

section PointCutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **averaged cut-off** at the origin: for a function $\eta$ on a real normed space $E$ and
$n \in \mathbb{N}$,
$$\eta_n(x) = \frac{1}{n+1} \sum_{k=0}^{n} \eta(3^k x).$$

For a cut-off $\eta$ equal to $1$ on $\bar B(0, 1)$ and supported in $B(0, 2)$, the function
$\eta_n$ is $1$ on $\bar B(0, 3^{-n})$, vanishes for $\|x\| \ge 2$, and tends to $0$ at every
$x \neq 0$. The gradients $\nabla \eta(3^k x)$ of the summands have disjoint supports, the
shells $3^{-k} \le \|x\| < 2 \cdot 3^{-k}$. Therefore
$\|\nabla \eta_n\|_{L^d}^d \le C (n+1)^{1-d}$ in dimension $d$, and a point has zero capacity in
$W^{1,p}$ for $p \le d$. -/
def pointCutoff (η : E → ℝ) (n : ℕ) (x : E) : ℝ :=
  ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), η ((3 : ℝ) ^ k • x)

variable {η : E → ℝ}

/-- If $\eta$ is smooth, the averaged cut-off $\eta_n$ is smooth. -/
theorem contDiff_pointCutoff (hη : ContDiff ℝ ∞ η) (n : ℕ) : ContDiff ℝ ∞ (pointCutoff η n) :=
  contDiff_const.mul (ContDiff.sum fun _ _ ↦ hη.comp (contDiff_id.const_smul _))

/-- If $\eta$ takes its values in $[0, 1]$, the averaged cut-off $\eta_n$ takes its values in
$[0, 1]$. -/
theorem pointCutoff_mem_Icc (hη01 : ∀ x, η x ∈ Icc (0 : ℝ) 1) (n : ℕ) (x : E) :
    pointCutoff η n x ∈ Icc (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨mul_nonneg (inv_pos.2 hpos).le (Finset.sum_nonneg fun k _ ↦ (hη01 _).1), ?_⟩
  rw [pointCutoff, inv_mul_le_iff₀ hpos, mul_one]
  calc ∑ k ∈ Finset.range (n + 1), η ((3 : ℝ) ^ k • x)
      ≤ ∑ k ∈ Finset.range (n + 1), (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ (hη01 _).2
    _ = (n : ℝ) + 1 := by simp

/-- If $\eta = 1$ on $\bar B(0, 1)$, then $\eta_n(x) = 1$ for $\|x\| \le 3^{-n}$. -/
theorem pointCutoff_eq_one (hη1 : EqOn η 1 (closedBall 0 1)) (n : ℕ) {x : E}
    (hx : ‖x‖ ≤ ((3 : ℝ) ^ n)⁻¹) : pointCutoff η n x = 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [pointCutoff, Finset.sum_eq_card_nsmul (b := (1 : ℝ)) fun k hk ↦ ?_]
  · simp [hpos.ne']
  · refine hη1 (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    calc (3 : ℝ) ^ k * ‖x‖ ≤ 3 ^ k * (3 ^ n)⁻¹ := by gcongr
      _ ≤ 1 := by
        rw [mul_inv_le_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ (by norm_num) hk'

/-- If $\operatorname{supp} \eta \subseteq B(0, 2)$, then $\eta_n(x) = 0$ for $\|x\| \ge 2$. -/
theorem pointCutoff_eq_zero (hηs : tsupport η ⊆ ball 0 2) (n : ℕ) {x : E} (hx : 2 ≤ ‖x‖) :
    pointCutoff η n x = 0 := by
  rw [pointCutoff, Finset.sum_eq_zero fun k _ ↦ ?_, mul_zero]
  refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
  have h2 := mem_ball_zero_iff.1 (hηs h)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
  have : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  nlinarith

/-- If $\operatorname{supp} \eta \subseteq B(0, 2)$ and $\eta$ takes its values in $[0, 1]$, then
$\eta_n(x) \to 0$ as $n \to \infty$ for every $x \neq 0$. At most $\log_3(2/\|x\|) + 1$ of the
$n + 1$ summands are nonzero. -/
theorem tendsto_pointCutoff (hηs : tsupport η ⊆ ball 0 2) (hη01 : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    {x : E} (hx : x ≠ 0) : Tendsto (fun n ↦ pointCutoff η n x) atTop (𝓝 0) := by
  classical
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 / ‖x‖ < 3 ^ K := pow_unbounded_of_one_lt _ (by norm_num)
  have hzero : ∀ k, K ≤ k → η ((3 : ℝ) ^ k • x) = 0 := fun k hk ↦ by
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    have h2 := mem_ball_zero_iff.1 (hηs h)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
    have h3 : (3 : ℝ) ^ K ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hk
    rw [div_lt_iff₀ hxpos] at hK
    nlinarith
  have hle : ∀ n, pointCutoff η n x ≤ ((n : ℝ) + 1)⁻¹ * K := fun n ↦ by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [pointCutoff]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hpos).le
    rw [← Finset.sum_filter_of_ne (p := fun k ↦ k < K) fun k _ hk ↦ ?_]
    · calc ∑ k ∈ (Finset.range (n + 1)).filter (fun k ↦ k < K), η ((3 : ℝ) ^ k • x)
          ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k ↦ k < K), (1 : ℝ) :=
            Finset.sum_le_sum fun k _ ↦ (hη01 _).2
        _ ≤ ∑ k ∈ Finset.range K, (1 : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ zero_le_one
            intro k hk
            exact Finset.mem_range.2 (Finset.mem_filter.1 hk).2
        _ = K := by simp
    · by_contra h
      exact hk (hzero k (not_lt.1 h))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ (pointCutoff_mem_Icc hη01 n x).1) hle
  simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (K : ℝ)

/-- If $\eta$ is smooth, the averaged cut-off has the derivative
$$D\eta_n(x) = \frac{1}{n+1} \sum_{k=0}^{n} 3^k \, D\eta(3^k x)$$
at every $x$. -/
theorem hasFDerivAt_pointCutoff (hη : ContDiff ℝ ∞ η) (n : ℕ) (x : E) :
    HasFDerivAt (pointCutoff η n) (((n : ℝ) + 1)⁻¹ •
      ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x)) x := by
  refine HasFDerivAt.const_mul (HasFDerivAt.fun_sum fun k _ ↦ ?_) _
  have h := ((hη.differentiable (by simp)) _).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul ((3 : ℝ) ^ k))
  rwa [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] at h

/-- If $\eta$ is smooth, the derivative of the averaged cut-off is $D\eta_n(x) = (n+1)^{-1}
\sum_{k=0}^{n} 3^k \, D\eta(3^k x)$. This is the form with `fderiv` of
`hasFDerivAt_pointCutoff`. -/
theorem fderiv_pointCutoff (hη : ContDiff ℝ ∞ η) (n : ℕ) (x : E) :
    fderiv ℝ (pointCutoff η n) x = ((n : ℝ) + 1)⁻¹ •
      ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x) :=
  (hasFDerivAt_pointCutoff hη n x).fderiv

/-- If $\eta = 1$ on $\bar B(0, 1)$, then $D\eta(y) = 0$ for $\|y\| < 1$. -/
theorem fderiv_eq_zero_of_eqOn_one_closedBall_one (hη1 : EqOn η 1 (closedBall 0 1)) {y : E}
    (hy : ‖y‖ < 1) : fderiv ℝ η y = 0 := by
  have hev : η =ᶠ[𝓝 y] fun _ ↦ (1 : ℝ) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)) fun z hz ↦
      hη1 (ball_subset_closedBall hz)
  rw [hev.fderiv_eq, fderiv_fun_const, Pi.zero_apply]

end PointCutoff

section PointCutoffNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {η : E → ℝ}

/-- Let $\eta = 1$ on $\bar B(0, 1)$ with $\operatorname{supp} \eta \subseteq B(0, 2)$. If
$3^k D\eta(3^k x) \neq 0$, then $3^{-k} \le \|x\| < 2 \cdot 3^{-k}$: the $k$-th summand of
$D\eta_n$ vanishes outside this shell. -/
theorem norm_mem_Ico_of_pow_smul_fderiv_ne_zero (hη1 : EqOn η 1 (closedBall 0 1))
    (hηs : tsupport η ⊆ ball 0 2) {k : ℕ} {x : E}
    (h : (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x) ≠ 0) :
    ((3 : ℝ) ^ k)⁻¹ ≤ ‖x‖ ∧ ‖x‖ < 2 * ((3 : ℝ) ^ k)⁻¹ := by
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have hne : fderiv ℝ η ((3 : ℝ) ^ k • x) ≠ 0 := fun h0 ↦ h (by rw [h0, smul_zero])
  have h2 := mem_ball_zero_iff.1 (hηs (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 hne)))
  have h1 : ¬ ‖(3 : ℝ) ^ k • x‖ < 1 := fun hlt ↦
    hne (fderiv_eq_zero_of_eqOn_one_closedBall_one hη1 hlt)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos h3] at h1 h2
  rw [not_lt] at h1
  constructor
  · rw [inv_le_iff_one_le_mul₀ h3, mul_comm]
    exact h1
  · rwa [lt_mul_inv_iff₀ h3, mul_comm]

/-- Let $\eta = 1$ on $\bar B(0, 1)$ with $\operatorname{supp} \eta \subseteq B(0, 2)$. If
$3^k D\eta(3^k x) \neq 0$ and $3^{k'} D\eta(3^{k'} x) \neq 0$, then $k = k'$: the shells of two
distinct summands of $D\eta_n$ are disjoint. -/
theorem eq_of_pow_smul_fderiv_ne_zero (hη1 : EqOn η 1 (closedBall 0 1))
    (hηs : tsupport η ⊆ ball 0 2) {k k' : ℕ} {x : E}
    (h : (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x) ≠ 0)
    (h' : (3 : ℝ) ^ k' • fderiv ℝ η ((3 : ℝ) ^ k' • x) ≠ 0) : k = k' := by
  have key : ∀ {k k' : ℕ}, k < k' → ((3 : ℝ) ^ k)⁻¹ ≤ ‖x‖ → ‖x‖ < 2 * ((3 : ℝ) ^ k')⁻¹ → False :=
    fun {k k'} hkk' h1 h2 ↦ by
    have h3 : (3 : ℝ) ^ (k + 1) ≤ 3 ^ k' := pow_le_pow_right₀ (by norm_num) hkk'
    have h4 : 2 * ((3 : ℝ) ^ k')⁻¹ ≤ 2 * ((3 : ℝ) ^ (k + 1))⁻¹ := by gcongr
    have h5 : 2 * ((3 : ℝ) ^ (k + 1))⁻¹ < ((3 : ℝ) ^ k)⁻¹ := by
      rw [pow_succ, mul_inv, ← mul_assoc, mul_comm 2, mul_assoc]
      have : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹ := by positivity
      nlinarith
    linarith
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact key hlt (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs h).1
      (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs h').2
  · exact key hlt (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs h').1
      (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs h).2

/-- Let $(a_i)_{i \in s}$ be a finite family in a normed group with at most one nonzero member, and
let $q > 0$. Then $\|\sum_{i \in s} a_i\|^q \le \sum_{i \in s} \|a_i\|^q$, in `ℝ≥0∞`. -/
theorem enorm_sum_rpow_le_sum_of_forall_eq {ι G : Type*} [NormedAddCommGroup G] {s : Finset ι}
    {a : ι → G} (h : ∀ i ∈ s, ∀ j ∈ s, a i ≠ 0 → a j ≠ 0 → i = j) {q : ℝ} (hq : 0 < q) :
    ‖∑ i ∈ s, a i‖ₑ ^ q ≤ ∑ i ∈ s, ‖a i‖ₑ ^ q := by
  classical
  by_cases h0 : ∃ i ∈ s, a i ≠ 0
  · obtain ⟨i, hi, hai⟩ := h0
    rw [Finset.sum_eq_single i (fun j hj hji ↦ by_contra fun haj ↦ hji (h j hj i hi haj hai))
      (fun hi' ↦ absurd hi hi')]
    exact Finset.single_le_sum (f := fun j ↦ ‖a j‖ₑ ^ q) (fun _ _ ↦ zero_le) hi
  · push Not at h0
    rw [Finset.sum_eq_zero h0, enorm_zero, ENNReal.zero_rpow_of_pos hq]
    exact zero_le

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- **The $L^d$ norm of the gradient of the averaged cut-off.** Let $E$ be a nontrivial
finite-dimensional real normed space of dimension $d$ with an additive Haar measure $\mu$. Let
$\eta$ be smooth with $\eta = 1$ on $\bar B(0, 1)$, $\operatorname{supp} \eta \subseteq B(0, 2)$
and $\|D\eta\| \le M$. Then for every $n$,
$$\int \|D\eta_n\|^d \, d\mu \le (n+1) \Big(\frac{2M}{n+1}\Big)^d \mu\big(B(0, 1)\big).$$

The summands $3^k D\eta(3^k x)$ of $(n+1) D\eta_n$ are bounded by $3^k M$ and supported in the
disjoint shells inside $B(0, 2 \cdot 3^{-k})$, which has measure
$(2 \cdot 3^{-k})^d \mu(B(0, 1))$. -/
theorem lintegral_enorm_fderiv_pointCutoff_pow_le [Nontrivial E] (hη : ContDiff ℝ ∞ η)
    (hη1 : EqOn η 1 (closedBall 0 1)) (hηs : tsupport η ⊆ ball 0 2) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (n : ℕ) :
    ∫⁻ x, ‖fderiv ℝ (pointCutoff η n) x‖ₑ ^ (finrank ℝ E : ℝ) ∂μ
      ≤ ((n : ℝ≥0∞) + 1) * ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (2 * M)) ^ finrank ℝ E)
        * μ (ball 0 1) := by
  classical
  have hd : 0 < finrank ℝ E := finrank_pos
  have hd' : (0 : ℝ) < finrank ℝ E := by exact_mod_cast hd
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set d := finrank ℝ E with hddef
  -- the pointwise bound
  have hpt : ∀ x, ‖fderiv ℝ (pointCutoff η n) x‖ₑ ^ (d : ℝ) ≤ ∑ k ∈ Finset.range (n + 1),
      (ball (0 : E) (2 * ((3 : ℝ) ^ k)⁻¹)).indicator
        (fun _ ↦ ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (3 ^ k * M)) ^ d)) x := by
    intro x
    rw [fderiv_pointCutoff hη, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hd'.le]
    calc ‖((n : ℝ) + 1)⁻¹‖ₑ ^ (d : ℝ)
          * ‖∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x)‖ₑ ^ (d : ℝ)
        ≤ ‖((n : ℝ) + 1)⁻¹‖ₑ ^ (d : ℝ) * ∑ k ∈ Finset.range (n + 1),
            ‖(3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x)‖ₑ ^ (d : ℝ) := by
          gcongr
          exact enorm_sum_rpow_le_sum_of_forall_eq
            (fun k _ k' _ hk hk' ↦ eq_of_pow_smul_fderiv_ne_zero hη1 hηs hk hk') hd'
      _ = ∑ k ∈ Finset.range (n + 1), ‖((n : ℝ) + 1)⁻¹‖ₑ ^ (d : ℝ)
          * ‖(3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x)‖ₑ ^ (d : ℝ) := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum fun k _ ↦ ?_
    have h3 : (0 : ℝ) < 3 ^ k := by positivity
    by_cases hx : x ∈ ball (0 : E) (2 * ((3 : ℝ) ^ k)⁻¹)
    · rw [Set.indicator_of_mem hx, Real.enorm_of_nonneg (inv_pos.2 hpos).le, mul_pow,
        ENNReal.ofReal_mul (by positivity), ← Real.rpow_natCast (((n : ℝ) + 1)⁻¹),
        ← Real.rpow_natCast ((3 : ℝ) ^ k * M),
        ← ENNReal.ofReal_rpow_of_nonneg (inv_pos.2 hpos).le hd'.le,
        ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hd'.le]
      gcongr
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos h3]
      exact mul_le_mul_of_nonneg_left (hM _) h3.le
    · have h0 : (3 : ℝ) ^ k • fderiv ℝ η ((3 : ℝ) ^ k • x) = 0 := by
        by_contra hne
        exact hx (mem_ball_zero_iff.2 (norm_mem_Ico_of_pow_smul_fderiv_ne_zero hη1 hηs hne).2)
      rw [h0, enorm_zero, ENNReal.zero_rpow_of_pos hd', mul_zero]
      exact zero_le
  -- integration
  calc ∫⁻ x, ‖fderiv ℝ (pointCutoff η n) x‖ₑ ^ (d : ℝ) ∂μ
      ≤ ∫⁻ x, ∑ k ∈ Finset.range (n + 1), (ball (0 : E) (2 * ((3 : ℝ) ^ k)⁻¹)).indicator
          (fun _ ↦ ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (3 ^ k * M)) ^ d)) x ∂μ :=
        lintegral_mono hpt
    _ = ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (3 ^ k * M)) ^ d)
          * μ (ball (0 : E) (2 * ((3 : ℝ) ^ k)⁻¹)) := by
        rw [lintegral_finsetSum _ fun k _ ↦ measurable_const.indicator measurableSet_ball]
        exact Finset.sum_congr rfl fun k _ ↦ lintegral_indicator_const measurableSet_ball _
    _ = ∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (2 * M)) ^ d) * μ (ball (0 : E) 1) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Measure.addHaar_ball μ _ (by positivity), ← mul_assoc, ← ENNReal.ofReal_mul
          (by positivity), ← mul_pow]
        congr 3
        field_simp
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- Let $E$ have dimension $d \ge 2$, and let $\eta$ be smooth with $\eta = 1$ on $\bar B(0, 1)$,
$\operatorname{supp} \eta \subseteq B(0, 2)$ and $\|D\eta\| \le M$. Then
$\int \|D\eta_n\|^d \, d\mu \to 0$ as $n \to \infty$. -/
theorem tendsto_lintegral_enorm_fderiv_pointCutoff_pow (hη : ContDiff ℝ ∞ η)
    (hη1 : EqOn η 1 (closedBall 0 1)) (hηs : tsupport η ⊆ ball 0 2) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (hd : 2 ≤ finrank ℝ E) :
    Tendsto (fun n ↦ ∫⁻ x, ‖fderiv ℝ (pointCutoff η n) x‖ₑ ^ (finrank ℝ E : ℝ) ∂μ) atTop
      (𝓝 0) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  set d := finrank ℝ E with hddef
  -- the real bound `(n + 1) ((2M)/(n+1))^d = ((n+1)⁻¹)^(d-1) (2M)^d → 0`
  have hreal : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ * (2 * M)) ^ d) atTop
      (𝓝 0) := by
    have he : ∀ n : ℕ, ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ * (2 * M)) ^ d
        = (1 / ((n : ℝ) + 1)) ^ (d - 1) * (2 * M) ^ d := fun n ↦ by
      obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      rw [he, Nat.add_sub_cancel, mul_pow, pow_succ, one_div]
      field_simp
    simp_rw [he]
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat.pow (d - 1)).mul_const ((2 * M) ^ d)
    rwa [zero_pow (by omega), zero_mul] at h1
  have hB : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0∞) + 1)
      * ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ * (2 * M)) ^ d) * μ (ball (0 : E) 1)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hreal) (b := μ (ball (0 : E) 1))
      (Or.inr measure_ball_lt_top.ne)
    rw [ENNReal.ofReal_zero, zero_mul] at h1
    refine h1.congr fun n ↦ ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 2
    exact_mod_cast (ENNReal.ofReal_natCast (n + 1)).symm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun _ ↦ zero_le)
    fun n ↦ lintegral_enorm_fderiv_pointCutoff_pow_le hη hη1 hηs hM n

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If $\operatorname{supp} \eta \subseteq B(0, 2)$, then the derivative $D\eta_n$ of the averaged
cut-off vanishes outside $\bar B(0, 2)$. -/
theorem support_fderiv_pointCutoff_subset (hηs : tsupport η ⊆ ball 0 2) (n : ℕ) :
    Function.support (fderiv ℝ (pointCutoff η n)) ⊆ closedBall 0 2 := by
  refine (support_fderiv_subset (𝕜 := ℝ)).trans ?_
  refine (closure_mono fun x hx ↦ ?_).trans closure_ball_subset_closedBall
  rw [mem_ball_zero_iff]
  by_contra h
  exact hx (pointCutoff_eq_zero hηs n (not_lt.1 h))

/-- **The $L^p$ norm of the gradient of the averaged cut-off tends to $0$.** Let $E$ have dimension
$d \ge 2$, let $1 \le p \le d$, and let $\eta$ be smooth with $\eta = 1$ on $\bar B(0, 1)$,
$\operatorname{supp} \eta \subseteq B(0, 2)$ and $\|D\eta\| \le M$. Then
$\|D\eta_n\|_{L^p(\mu)} \to 0$. So a point has zero capacity in $W^{1,p}$ for $p \le d$.

The case $p = d$ follows from `lintegral_enorm_fderiv_pointCutoff_pow_le`, and the other cases
follow by Hölder's inequality on $\bar B(0, 2)$, which contains the supports of the gradients. -/
theorem tendsto_eLpNorm_fderiv_pointCutoff (hη : ContDiff ℝ ∞ η)
    (hη1 : EqOn η 1 (closedBall 0 1)) (hηs : tsupport η ⊆ ball 0 2) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (hd : 2 ≤ finrank ℝ E) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpd : p ≤ finrank ℝ E) :
    Tendsto (fun n ↦ eLpNorm (fderiv ℝ (pointCutoff η n)) p μ) atTop (𝓝 0) := by
  set d := finrank ℝ E with hddef
  have hdpos : (0 : ℝ) < d := by norm_cast; omega
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hdt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top hdt hpd
  have hm : ∀ n, AEStronglyMeasurable (fderiv ℝ (pointCutoff η n)) μ := fun n ↦
    ((contDiff_pointCutoff hη n).continuous_fderiv (by simp)).aestronglyMeasurable
  -- the case `p = d`
  have hLd : Tendsto (fun n ↦ eLpNorm (fderiv ℝ (pointCutoff η n)) d μ) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / (d : ℝ))).tendsto 0).comp
      (tendsto_lintegral_enorm_fderiv_pointCutoff_pow (μ := μ) hη hη1 hηs hM hd)
    simp only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.2 hdpos)] at h
    refine h.congr fun n ↦ ?_
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hd0 hdt (hm n), ENNReal.toReal_natCast]
  -- Hölder on `closedBall 0 2`
  have hC : μ (closedBall (0 : E) 2) ^ (1 / p.toReal - 1 / (d : ℝ)) ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg ?_ measure_closedBall_lt_top.ne
    rw [sub_nonneg]
    refine one_div_le_one_div_of_le (ENNReal.toReal_pos hp0 hpt) ?_
    have := ENNReal.toReal_mono hdt hpd
    rwa [ENNReal.toReal_natCast] at this
  have hle : ∀ n, eLpNorm (fderiv ℝ (pointCutoff η n)) p μ
      ≤ eLpNorm (fderiv ℝ (pointCutoff η n)) d μ
        * μ (closedBall (0 : E) 2) ^ (1 / p.toReal - 1 / (d : ℝ)) := fun n ↦ by
    rw [← eLpNorm_restrict_eq_of_support_subset (hm n) (support_fderiv_pointCutoff_subset hηs n),
      ← eLpNorm_restrict_eq_of_support_subset (p := d) (hm n)
        (support_fderiv_pointCutoff_subset hηs n)]
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpd
      (μ := μ.restrict (closedBall (0 : E) 2)) ((hm n).restrict)
    rwa [Measure.restrict_apply_univ, ENNReal.toReal_natCast] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hle
  simpa using ENNReal.Tendsto.mul_const hLd (Or.inr hC)

end PointCutoffNorm

section PointCapacity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndex

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- Let $1 \le p \le \infty$ and let $u_n, u \in W^{1,p}(\Omega)$. If $u_n \to u$ in $L^p(\Omega)$
and $\partial_i u_n \to \partial_i u$ in $L^p(\Omega)$ for every $i$, then $u_n \to u$ in
$W^{1,p}(\Omega)$.

This is `SobolevMultiIndex.tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub`, with the
multi-indices of order at most one listed as $0$ and the $e_i$. -/
theorem tendsto_of_tendsto_eLpNorm_fn_sub_of_forall_single {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {w : ℕ → SobolevMultiIndex F b 1 p Ω μ} {u : SobolevMultiIndex F b 1 p Ω μ}
    (h0 : Tendsto (fun n ↦ eLpNorm (fn (w n) - fn u) p (μ.restrict (Ω : Set E))) atTop (𝓝 0))
    (hi : ∀ i, Tendsto (fun n ↦ eLpNorm ((weakDeriv (w n) (MultiIndexLE.single i) : E → F)
      - (weakDeriv u (MultiIndexLE.single i) : E → F)) p (μ.restrict (Ω : Set E))) atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 u) := by
  refine tendsto_of_forall_tendsto_eLpNorm_weakDeriv_sub fun α ↦ ?_
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
  · exact h0
  · exact hi i

/-- **Lemma 9.5 without compactness at infinity.** Let $1 \le p < \infty$, let
$u \in W^{1,p}(\Omega)$ be real-valued, and let $U$ be an open set that contains
$E \setminus \Omega$. If the function of $u$ vanishes almost everywhere on $U \cap \Omega$, then
$u \in W_0^{1,p}(\Omega)$. This combines Lemma 9.5 of [brezis2011functional] with footnote 5 of
§9.1.

The cut-offs $\zeta_n u \to u$ (`SobolevMultiIndex.tendsto_cutoff_smul`) vanish almost
everywhere outside the compact set $\bar B(0, 2(n+1)) \setminus U \subseteq \Omega$. So they lie
in $W_0^{1,p}(\Omega)$ by Lemma 9.5
(`SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact`), and $W_0^{1,p}(\Omega)$ is closed. -/
theorem mem_zero_of_ae_eq_zero_of_compl_subset (hp' : p ≠ ⊤) (u : SobolevMultiIndex ℝ b 1 p Ω μ)
    {U : Set E} (hU : IsOpen U) (hΩU : (Ω : Set E)ᶜ ⊆ U)
    (hu : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∈ U → fn u x = 0) :
    u ∈ SobolevMultiIndexZero ℝ b 1 p Ω μ := by
  obtain ⟨ζ, hζ, hζ1, hζs, hζ01⟩ := exists_contDiff_eqOn_one_closedBall_one E
  obtain ⟨v, hv, hv0, hvt⟩ :=
    tendsto_cutoff_smul hp' hζ hζ01 hζ1 (hζs.trans ball_subset_closedBall) u
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hvt (Eventually.of_forall fun n ↦ ?_)
  refine mem_zero_of_ae_eq_zero_compl_isCompact hp' (v n)
    (K := closedBall 0 (2 * ((n : ℝ) + 1)) ∩ Uᶜ)
    ((isCompact_closedBall _ _).inter_right hU.isClosed_compl)
    (fun x hx ↦ by_contra fun hxΩ ↦ hx.2 (hΩU hxΩ)) ?_
  filter_upwards [hv n, hv0 n, hu] with x hx hx0 hxU hxK
  by_cases hxb : 2 * ((n : ℝ) + 1) < ‖x‖
  · exact hx0 hxb
  · have hxU' : x ∈ U := by
      by_contra h
      exact hxK ⟨mem_closedBall_zero_iff.2 (not_lt.1 hxb), h⟩
    rw [hx, hxU hxU', mul_zero]

/-- **Bounded functions are dense in $W^{1,p}(\Omega)$.** Let $1 \le p < \infty$ and let
$u \in W^{1,p}(\Omega)$ be real-valued. Then there are $v_n \in W^{1,p}(\Omega)$ with
$v_n \to u$ in $W^{1,p}(\Omega)$ such that the function of each $v_n$ is essentially bounded on
$\Omega$.

The proof uses the truncations $H_n(t) = t - (n+1) G(t/(n+1))$ built from `stepTruncation`. They
are $C^1$, $H_n(t) = t$ for $|t| \le n + 1$, $H_n(t) = 0$ for $|t| \ge 2(n+1)$, and
$|H_n'| \le 1 + M$. The composites $H_n \circ u$ lie in $W^{1,p}(\Omega)$ by Proposition 9.5
(`MemSobolevMultiIndex.contDiff_comp`) and are bounded. Their weak derivatives are
$H_n'(u) \partial_i u$ (`SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_comp`), and they
converge to $u$ in $W^{1,p}(\Omega)$ by dominated convergence. -/
theorem exists_seq_tendsto_ae_abs_le (hp' : p ≠ ⊤) (u : SobolevMultiIndex ℝ b 1 p Ω μ) :
    ∃ v : ℕ → SobolevMultiIndex ℝ b 1 p Ω μ,
      (∀ n, ∃ M : ℝ, ∀ᵐ x ∂μ.restrict (Ω : Set E), |fn (v n) x| ≤ M) ∧
        Tendsto v atTop (𝓝 u) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hum : AEStronglyMeasurable (fn u) (μ.restrict (Ω : Set E)) := (memLp u).aestronglyMeasurable
  obtain ⟨M, hM0, hM⟩ := exists_abs_deriv_stepTruncation_le
  -- the truncations `H_n(t) = t − (n+1) G(t/(n+1))`
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℝ, c = fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ := ⟨_, rfl⟩
  have hcpos : ∀ n, 0 < c n := fun n ↦ by rw [hcdef]; positivity
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ → ℝ → ℝ,
      H = fun (n : ℕ) (t : ℝ) ↦ t - (c n)⁻¹ * stepTruncation (t * c n) := ⟨_, rfl⟩
  have hHd : ∀ n t, HasDerivAt (H n) (1 - deriv stepTruncation (t * c n)) t := fun n t ↦ by
    rw [hHdef]
    exact (hasDerivAt_id t).sub (hasDerivAt_scaled_stepTruncation (hcpos n).ne' t)
  have hHc : ∀ n, ContDiff ℝ 1 (H n) := fun n ↦ by
    rw [hHdef]
    exact contDiff_id.sub (contDiff_const.mul
      ((contDiff_stepTruncation.of_le (by simp)).comp (contDiff_id.mul contDiff_const)))
  have hH0 : ∀ n, H n 0 = 0 := fun n ↦ by simp [hHdef, stepTruncation_zero]
  have hHderiv : ∀ n t, deriv (H n) t = 1 - deriv stepTruncation (t * c n) :=
    fun n t ↦ (hHd n t).deriv
  have hHM : ∀ n t, |deriv (H n) t| ≤ 1 + M := fun n t ↦ by
    rw [hHderiv]
    exact (abs_sub _ _).trans (by rw [abs_one]; linarith [hM (t * c n)])
  have hHle : ∀ n t, |H n t| ≤ (1 + M) * |t| := fun n t ↦ by
    simpa [hH0 n] using abs_sub_le_mul_of_abs_deriv_le (hHc n) (hHM n) t 0
  have hHzero : ∀ (n : ℕ) (t : ℝ), 2 ≤ |t| * c n → H n t = 0 := fun n t ht ↦ by
    simp only [hHdef]
    rw [stepTruncation_of_two_le (by rwa [abs_mul, abs_of_pos (hcpos n)]), mul_comm t,
      inv_mul_cancel_left₀ (hcpos n).ne', sub_self]
  have hHid : ∀ (n : ℕ) (t : ℝ), |t| * c n ≤ 1 → H n t = t := fun n t ht ↦ by
    simp only [hHdef]
    rw [stepTruncation_of_abs_le (by rwa [abs_mul, abs_of_pos (hcpos n)]), mul_zero, sub_zero]
  have hHd1 : ∀ (n : ℕ) (t : ℝ), |t| * c n < 1 → deriv (H n) t = 1 := fun n t ht ↦ by
    rw [hHderiv, deriv_stepTruncation_of_abs_lt (by rwa [abs_mul, abs_of_pos (hcpos n)]),
      sub_zero]
  have hHbdd : ∀ n t, |H n t| ≤ (1 + M) * (2 * (c n)⁻¹) := fun n t ↦ by
    by_cases ht : 2 ≤ |t| * c n
    · rw [hHzero n t ht, abs_zero]
      exact mul_nonneg (by linarith) (mul_nonneg zero_le_two (inv_pos.2 (hcpos n)).le)
    · refine (hHle n t).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      rw [not_le, ← lt_div_iff₀ (hcpos n), div_eq_mul_inv] at ht
      exact ht.le
  have hev : ∀ t : ℝ, ∀ n ≥ ⌈|t|⌉₊, |t| * c n < 1 := fun t n hn ↦ by
    rw [hcdef, mul_inv_lt_iff₀ (by positivity), one_mul]
    exact (Nat.le_ceil _).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hn)
  -- the truncated elements `H_n ∘ u`
  choose U hU using fun n ↦
    ((memSobolevMultiIndex u).contDiff_comp hp (hHc n) (hH0 n) (hHM n)).exists_sobolevMultiIndex
  refine ⟨U, fun n ↦ ⟨(1 + M) * (2 * (c n)⁻¹), ?_⟩,
    tendsto_of_tendsto_eLpNorm_fn_sub_of_forall_single ?_ fun i ↦ ?_⟩
  · filter_upwards [hU n] with x hx
    rw [hx]
    exact hHbdd n _
  -- `H_n ∘ u → u` in `L^p(Ω)`
  · have hL0 : Tendsto (fun n ↦ eLpNorm ((fun x ↦ H n (fn u x)) - fn u) p
        (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
      refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp' (bound := fun x ↦ (1 + M) * ‖fn u x‖)
        (fun n ↦ (hHc n).continuous.comp_aestronglyMeasurable hum) hum
        ((memLp u).norm.const_mul _) (fun n ↦ Eventually.of_forall fun x ↦ ?_)
        (Eventually.of_forall fun x ↦ ?_)
      · simpa [Real.norm_eq_abs] using hHle n (fn u x)
      · exact tendsto_atTop_of_eventually_const (i₀ := ⌈|fn u x|⌉₊) fun n hn ↦
          hHid n _ (hev _ n hn).le
    exact hL0.congr fun n ↦
      (eLpNorm_congr_ae ((hU n).sub (Filter.EventuallyEq.refl _ _))).symm
  -- `H_n'(u) ∂_i u → ∂_i u` in `L^p(Ω)`
  · have hdU : ∀ n, (weakDeriv (U n) (MultiIndexLE.single i) : E → ℝ)
        =ᵐ[μ.restrict (Ω : Set E)]
          fun x ↦ deriv (H n) (fn u x) * weakDeriv u (MultiIndexLE.single i) x := fun n ↦
      weakDeriv_single_ae_eq_of_fn_ae_eq_comp (hHc n) (hHM n) (hU n) i
    have hLi : Tendsto (fun n ↦ eLpNorm
        ((fun x ↦ deriv (H n) (fn u x) * weakDeriv u (MultiIndexLE.single i) x)
          - (weakDeriv u (MultiIndexLE.single i) : E → ℝ)) p (μ.restrict (Ω : Set E))) atTop
        (𝓝 0) := by
      refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp'
        (bound := fun x ↦ (1 + M) * ‖weakDeriv u (MultiIndexLE.single i) x‖)
        (fun n ↦ (((hHc n).continuous_deriv le_rfl).comp_aestronglyMeasurable hum).mul
          (Lp.aestronglyMeasurable _))
        (Lp.aestronglyMeasurable _) ((Lp.memLp _).norm.const_mul _)
        (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hHM n _) (norm_nonneg _)
      · exact tendsto_atTop_of_eventually_const (i₀ := ⌈|fn u x|⌉₊) fun n hn ↦ by
          rw [hHd1 n _ (hev _ n hn), one_mul]
    exact hLi.congr fun n ↦
      (eLpNorm_congr_ae ((hdU n).sub (Filter.EventuallyEq.refl _ _))).symm


/-- **The capacity of a point is zero in $W^{1,p}$ for $p \le \dim E$.** Let $E$ have dimension
$d \ge 2$, let $1 \le p \le d$, and let $u \in W^{1,p}(\Omega)$ be real-valued with $|u| \le M$
almost everywhere on $\Omega$. Then there are $v_n \in W^{1,p}(\Omega)$ with $v_n \to u$ in
$W^{1,p}(\Omega)$ such that, for each $n$, the function of $v_n$ vanishes almost everywhere on
$\Omega \cap B(0, r)$ for some $r > 0$.

The approximants are $(1 - \eta_n) u$, with the averaged cut-offs $\eta_n$ of `pointCutoff`,
which equal $1$ near $0$. Then $\eta_n u \to 0$ and $\eta_n \partial_i u \to 0$ in $L^p(\Omega)$
by dominated convergence, since $\eta_n \to 0$ outside the null set $\{0\}$. Further $\|u \,
\partial_i \eta_n\|_p \le M \|e_i\| \|\nabla \eta_n\|_p \to 0$ by
`tendsto_eLpNorm_fderiv_pointCutoff`. This is where $p \le d$ enters, through
$\|\nabla \eta_n\|_{L^d}^d \le C (n+1)^{1-d}$. -/
theorem exists_seq_tendsto_ae_eq_zero_ball (hp' : p ≠ ⊤) (hd : 2 ≤ finrank ℝ E)
    (hpd : p ≤ finrank ℝ E) (u : SobolevMultiIndex ℝ b 1 p Ω μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), |fn u x| ≤ M) :
    ∃ v : ℕ → SobolevMultiIndex ℝ b 1 p Ω μ,
      (∀ n, ∃ r > 0, ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∈ ball 0 r → fn (v n) x = 0) ∧
        Tendsto v atTop (𝓝 u) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hum : AEStronglyMeasurable (fn u) (μ.restrict (Ω : Set E)) := (memLp u).aestronglyMeasurable
  obtain ⟨η, hη, hη1, hηs, hη01⟩ := exists_contDiff_eqOn_one_closedBall_one E
  have hηc : HasCompactSupport η :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) (isClosed_tsupport η)
      (hηs.trans ball_subset_closedBall)
  obtain ⟨Mη, hMη⟩ := (hηc.fderiv ℝ).exists_bound_of_continuous (hη.continuous_fderiv (by simp))
  -- the factors `c n = 1 − η_n`
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → E → ℝ, c = fun n x ↦ 1 - pointCutoff η n x := ⟨_, rfl⟩
  have hcs : ∀ n, ContDiff ℝ ∞ (c n) := fun n ↦ by
    rw [hcdef]
    exact contDiff_const.sub (contDiff_pointCutoff hη n)
  have hcd : ∀ n x, fderiv ℝ (c n) x = -fderiv ℝ (pointCutoff η n) x := fun n x ↦ by
    have h : HasFDerivAt (c n) (0 - fderiv ℝ (pointCutoff η n) x) x := by
      rw [fderiv_pointCutoff hη, hcdef]
      exact (hasFDerivAt_const (1 : ℝ) x).fun_sub (hasFDerivAt_pointCutoff hη n x)
    rw [h.fderiv, zero_sub]
  have hc01 : ∀ n x, c n x ∈ Icc (0 : ℝ) 1 := fun n x ↦ by
    have := pointCutoff_mem_Icc hη01 n x
    rw [hcdef]
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  have hcM : ∀ n, ∃ K : ℝ, ∀ x, |c n x| ≤ K ∧ ‖fderiv ℝ (c n) x‖ ≤ K := fun n ↦ by
    have hsupp : HasCompactSupport (pointCutoff η n) := by
      refine IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) (isClosed_tsupport _) ?_
      refine (closure_mono fun x hx ↦ ?_).trans closure_ball_subset_closedBall
      rw [mem_ball_zero_iff]
      by_contra h
      exact hx (pointCutoff_eq_zero hηs n (not_lt.1 h))
    obtain ⟨K, hK⟩ := (hsupp.fderiv ℝ).exists_bound_of_continuous
      ((contDiff_pointCutoff hη n).continuous_fderiv (by simp))
    refine ⟨max 1 K, fun x ↦ ⟨?_, ?_⟩⟩
    · exact (abs_le.2 ⟨by linarith [(hc01 n x).1], (hc01 n x).2⟩).trans (le_max_left _ _)
    · rw [hcd, norm_neg]
      exact (hK x).trans (le_max_right _ _)
  have hc1 : ∀ n, ∀ x ∈ ball (0 : E) ((3 : ℝ) ^ n)⁻¹, c n x = 0 := fun n x hx ↦ by
    rw [hcdef]
    dsimp only
    rw [pointCutoff_eq_one hη1 n (mem_ball_zero_iff.1 hx).le, sub_self]
  have hclim : ∀ x, x ≠ 0 → Tendsto (fun n ↦ c n x) atTop (𝓝 1) := fun x hx ↦ by
    have := (tendsto_pointCutoff hηs hη01 hx).const_sub 1
    rw [sub_zero] at this
    rw [hcdef]
    exact this
  have hae : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  -- the elements `v n`, with functions `c n * u`
  have hmem : ∀ n, MemSobolevMultiIndex b (fun x ↦ c n x * fn u x) 1 p Ω μ := fun n ↦
    (memSobolevMultiIndex u).contDiff_mul hp (hcs n) (hcM n).choose_spec
  choose v hv using fun n ↦ (hmem n).exists_sobolevMultiIndex
  refine ⟨v, fun n ↦ ⟨((3 : ℝ) ^ n)⁻¹, by positivity, ?_⟩, ?_⟩
  · filter_upwards [hv n] with x hx hxr
    rw [hx, hc1 n x hxr, zero_mul]
  -- the weak derivatives of `v n`
  have hperm := fun i ↦ multiIndexTuple_single_perm (b : ι → E) i
  have hwu : ∀ i, HasWeakIteratedLineDerivOn ![b i] (fn u) (weakDeriv u (MultiIndexLE.single i))
      Ω μ := fun i ↦ (hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm (hperm i)
  have hwv : ∀ n i, (weakDeriv (v n) (MultiIndexLE.single i) : E → ℝ)
      =ᵐ[μ.restrict (Ω : Set E)] fun x ↦
        c n x * weakDeriv u (MultiIndexLE.single i) x + fderiv ℝ (c n) x (b i) * fn u x := by
    intro n i
    have h1 : HasWeakIteratedLineDerivOn ![b i] (fun x ↦ c n x * fn u x)
        (weakDeriv (v n) (MultiIndexLE.single i)) Ω μ :=
      ((hasWeakIteratedLineDerivOn (v n) (MultiIndexLE.single i)).of_perm (hperm i)).congr_ae
        (hv n) (EventuallyEq.refl _ _)
    exact (ae_restrict_iff' hΩm).2 (h1.ae_eq ((hwu i).contDiff_mul (hcs n)))
  -- dominated convergence for a factor `c n` tending to `1`
  have hdom : ∀ {f : E → ℝ}, MemLp f p (μ.restrict (Ω : Set E)) →
      Tendsto (fun n ↦ eLpNorm ((fun x ↦ c n x * f x) - f) p (μ.restrict (Ω : Set E))) atTop
        (𝓝 0) := fun {f} hf ↦ by
    refine tendsto_eLpNorm_sub_of_tendsto_ae hp0 hp' (bound := fun x ↦ ‖f x‖)
      (fun n ↦ (hcs n).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
      hf.aestronglyMeasurable hf.norm (fun n ↦ Eventually.of_forall fun x ↦ ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs (c n x)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (abs_le.2 ⟨by linarith [(hc01 n x).1], (hc01 n x).2⟩)
    · filter_upwards [hae] with x hx
      have := (hclim x hx).mul_const (f x)
      rw [one_mul] at this
      exact this
  -- the gradient term
  have hgrad : ∀ i, Tendsto (fun n ↦ eLpNorm (fun x ↦ fderiv ℝ (c n) x (b i) * fn u x) p
      (μ.restrict (Ω : Set E))) atTop (𝓝 0) := by
    intro i
    have hT := ENNReal.Tendsto.mul_const
      (tendsto_eLpNorm_fderiv_pointCutoff (μ := μ) hη hη1 hηs hMη hd hp hpd)
      (b := ENNReal.ofReal (M * ‖b i‖)) (Or.inr ENNReal.ofReal_ne_top)
    rw [zero_mul] at hT
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ ↦ zero_le)
      fun n ↦ ?_
    rw [mul_comm]
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (f := fun x ↦ fderiv ℝ (c n) x (b i) * fn u x) (g := fderiv ℝ (pointCutoff η n))
      (c := M * ‖b i‖) ?_ ?_ p).trans ?_
    · exact (((hcs n).fderiv_right (m := ∞) le_rfl).clm_apply
        contDiff_const).continuous.aestronglyMeasurable.mul hum
    · filter_upwards [hM] with x hx
      rw [norm_mul, hcd, neg_apply, norm_neg, Real.norm_eq_abs (fn u x)]
      calc ‖fderiv ℝ (pointCutoff η n) x (b i)‖ * |fn u x|
          ≤ ‖fderiv ℝ (pointCutoff η n) x‖ * ‖b i‖ * M :=
            mul_le_mul ((fderiv ℝ (pointCutoff η n) x).le_opNorm (b i)) hx (abs_nonneg _)
              (by positivity)
        _ = M * ‖b i‖ * ‖fderiv ℝ (pointCutoff η n) x‖ := by ring
    · gcongr
      exact Measure.restrict_le_self
  -- the convergence
  refine tendsto_of_tendsto_eLpNorm_fn_sub_of_forall_single ?_ fun i ↦ ?_
  · refine (hdom (memLp u)).congr fun n ↦ ?_
    exact (eLpNorm_congr_ae ((hv n).sub (Filter.EventuallyEq.refl _ _))).symm
  · have hsum := (hdom (Lp.memLp (weakDeriv u (MultiIndexLE.single i)))).add (hgrad i)
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
      fun n ↦ ?_
    have h : (weakDeriv (v n) (MultiIndexLE.single i) : E → ℝ)
        - (weakDeriv u (MultiIndexLE.single i) : E → ℝ) =ᵐ[μ.restrict (Ω : Set E)]
          ((fun x ↦ c n x * weakDeriv u (MultiIndexLE.single i) x)
            - (weakDeriv u (MultiIndexLE.single i) : E → ℝ))
          + fun x ↦ fderiv ℝ (c n) x (b i) * fn u x := by
      filter_upwards [hwv n i] with x hx
      simp only [Pi.sub_apply, Pi.add_apply, hx]
      ring
    rw [eLpNorm_congr_ae h]
    exact eLpNorm_add_le hp

end SobolevMultiIndex

/-- **$W_0^{1,p}(\Omega) = W^{1,p}(\Omega)$ when $E \setminus \Omega \subseteq \{0\}$.** Let $E$ be
a finite-dimensional real normed space of dimension $d \ge 2$, let $1 \le p \le d$, and let
$\Omega \subseteq E$ be an open set whose complement is contained in $\{0\}$, that is
$\Omega = E$ or $\Omega = E \setminus \{0\}$. Then $W_0^{1,p}(\Omega) = W^{1,p}(\Omega)$ for
real-valued functions: a point has zero capacity. This generalizes the example of Remark 17 in
Chapter 9 of [brezis2011functional]: "if $\Omega = \mathbb{R}^N \setminus \{0\}$ and $N \ge 2$
one can show that $H_0^1(\Omega) = H^1(\Omega)$".

Bounded elements are dense (`SobolevMultiIndex.exists_seq_tendsto_ae_abs_le`). A bounded element
is the limit of elements that vanish near $0$
(`SobolevMultiIndex.exists_seq_tendsto_ae_eq_zero_ball`). These lie in $W_0^{1,p}(\Omega)$ by
Lemma 9.5 in the form `SobolevMultiIndex.mem_zero_of_ae_eq_zero_of_compl_subset`, and
$W_0^{1,p}(\Omega)$ is closed. -/
theorem SobolevMultiIndexZero.eq_top_of_compl_subset_singleton (hd : 2 ≤ finrank ℝ E)
    (hpd : p ≤ finrank ℝ E) (hΩ : (Ω : Set E)ᶜ ⊆ {0}) :
    SobolevMultiIndexZero ℝ b 1 p Ω μ = ⊤ := by
  have hp' : p ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) hpd
  refine top_unique fun u _ ↦ ?_
  obtain ⟨v, hvb, hvt⟩ := SobolevMultiIndex.exists_seq_tendsto_ae_abs_le hp' u
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hvt (Eventually.of_forall fun n ↦ ?_)
  obtain ⟨M, hM⟩ := hvb n
  obtain ⟨w, hw0, hwt⟩ := SobolevMultiIndex.exists_seq_tendsto_ae_eq_zero_ball hp' hd hpd (v n) hM
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hwt (Eventually.of_forall fun m ↦ ?_)
  obtain ⟨r, hr, hw⟩ := hw0 m
  exact SobolevMultiIndex.mem_zero_of_ae_eq_zero_of_compl_subset hp' (w m) isOpen_ball
    (hΩ.trans (singleton_subset_iff.2 (mem_ball_self hr))) hw

/-- **$W_0^{1,p}(\mathbb{R}^N \setminus \{0\}) = W^{1,p}(\mathbb{R}^N \setminus \{0\})$** for
$N \ge 2$ and $1 \le p \le N$. This is the example of Remark 17 in Chapter 9 of
[brezis2011functional], which states $H_0^1(\mathbb{R}^N \setminus \{0\}) = H^1(\mathbb{R}^N
\setminus \{0\})$ for $N \ge 2$ ("if $\mathbb{R}^N \setminus \Omega$ is sufficiently thin and
$p < N$ … one can show"). The endpoint $p = N$ is included.

This is `SobolevMultiIndexZero.eq_top_of_compl_subset_singleton` on `SobolevEuclideanZero`. A
point has zero $W^{1,p}$ capacity for $p \le N$, by the averaged cut-offs `pointCutoff`. -/
theorem SobolevEuclideanZero.eq_top_of_compl_singleton {N : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (hN : 2 ≤ N) (hp : p ≤ N)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin N))) = {0}ᶜ) : SobolevEuclideanZero N 1 p Ω = ⊤ :=
  SobolevMultiIndexZero.eq_top_of_compl_subset_singleton
    (by rw [finrank_euclideanSpace_fin]; exact hN) (by rw [finrank_euclideanSpace_fin]; exact hp)
    (by rw [hΩ, compl_compl])

end PointCapacity

/-! ### Density: identities checked on the test functions hold on $W_0^{k,p}(\Omega)$ -/

section EqOn

/-- **Two continuous maps on $W^{k,p}(\Omega)$ that agree on the test functions agree on
$W_0^{k,p}(\Omega)$.** Let $X$ be a Hausdorff topological space, and let
$f, g : W^{k,p}(\Omega) \to X$ be continuous. If $f = g$ on the elements whose function is a
test function (`SobolevMultiIndex.testFunctions`), then $f = g$ on $W_0^{k,p}(\Omega)$, the
closure of these elements.

This is the density step of every argument that a classical solution is a weak solution: an
identity between continuous functionals checked on $C_c^\infty(\Omega)$ holds on
$W_0^{k,p}(\Omega)$. -/
theorem SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}
    {X : Type*} [TopologicalSpace X] [T2Space X] {f g : SobolevMultiIndex F b k p Ω μ → X}
    (hf : Continuous f) (hg : Continuous g)
    (h : EqOn f g (SobolevMultiIndex.testFunctions F b k p Ω μ)) :
    EqOn f g (SobolevMultiIndexZero F b k p Ω μ) := by
  rw [SobolevMultiIndexZero, Submodule.topologicalClosure_coe]
  exact closure_minimal h (isClosed_eq hf hg)

end EqOn

/-! ### Footnote 39: a $W_0^{1,p}$ function with vanishing gradient is zero -/

section Footnote39

open SobolevMultiIndex

/-- Let $N \ge 1$, let $1 \le p < \infty$, and let $\Omega \subseteq \mathbb{R}^N$ be open. If
$u \in W_0^{1,p}(\Omega)$ has $\partial_i u = 0$ for every $i$, then $u = 0$. This is footnote
39 of §9.7 of [brezis2011functional].

For $N = 0$ the statement is false. The extension by zero $\bar u$ lies in
$W^{1,p}(\mathbb{R}^N)$ with $\nabla \bar u = \overline{\nabla u} = 0$ (Proposition 9.18, (i) ⇒
(iii), `SobolevEuclideanZero.extendZeroL`). So $\bar u$ is almost everywhere constant on the
connected space $\mathbb{R}^N$ (Remark 7, `HasWeakFDerivOn.ae_eq_const_of_isPreconnected`). A
constant in $L^p(\mathbb{R}^N)$ with $p < \infty$ is $0$ (`MeasureTheory.memLp_const_iff`),
because $\mathbb{R}^N$ has infinite measure for $N \ge 1$. -/
theorem SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero {N : ℕ} (hN : N ≠ 0)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp' : p ≠ ⊤) {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (u : SobolevEuclideanZero N 1 p Ω)
    (h : ∀ i, weakDeriv (u : SobolevEuclidean N 1 p Ω) (MultiIndexLE.single i) = 0) : u = 0 := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hΩm := Ω.isOpen.measurableSet
  have : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
  -- the tensor gradient of the extension by zero vanishes almost everywhere
  obtain ⟨w, hw, -, hwi, -⟩ := exists_hasWeakFDerivOn_fn (SobolevEuclideanZero.extendZeroL N p Ω u)
  simp only [Opens.coe_top, Measure.restrict_univ] at hwi
  have hw0 : w =ᵐ[volume] 0 := by
    have hall : ∀ᵐ x ∂volume, ∀ i, w x ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis i) = 0 :=
      ae_all_iff.2 fun i ↦ by
        refine (hwi i).trans ((SobolevEuclideanZero.weakDeriv_extendZeroL_single u i).trans ?_)
        rw [h i]
        have := (ae_eq_restrict_iff_indicator_ae_eq hΩm).1
          (Lp.coeFn_zero ℝ p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        refine this.trans (Eventually.of_forall fun x ↦ ?_)
        simp
    filter_upwards [hall] with x hx
    simp only [EuclideanSpace.basisFun_toBasis_apply] at hx
    refine ContinuousLinearMap.ext fun ξ ↦ ?_
    rw [← (EuclideanSpace.basisFun (Fin N) ℝ).toBasis.sum_repr ξ, map_sum]
    simp [hx]
  obtain ⟨c, hc⟩ := hw.ae_eq_const_of_isPreconnected
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using hw0) isPreconnected_univ
  simp only [Opens.coe_top, Measure.restrict_univ] at hc
  -- the constant is zero, the measure of `ℝ^N` being infinite
  have hmem : MemLp (fun _ : EuclideanSpace ℝ (Fin N) ↦ c) p volume :=
    (SobolevEuclidean.memLp_fn (SobolevEuclideanZero.extendZeroL N p Ω u)).ae_eq hc
  have hc0 : c = 0 := by
    rcases (memLp_const_iff hp0 hp').1 hmem with h0 | hfin
    · exact h0
    · rw [measure_univ_of_isAddLeftInvariant] at hfin
      exact absurd hfin (lt_irrefl _)
  -- hence `u = 0`
  refine Subtype.ext (ext_of_fn_ae_eq ?_)
  refine ((SobolevEuclideanZero.fn_extendZeroL_restrict u).symm.trans ?_).trans fn_zero.symm
  refine ae_restrict_of_ae (hc.trans (Eventually.of_forall fun x ↦ ?_))
  simp [hc0]

end Footnote39

/-! ### The positive part in the $H^1$ norm, and functions between $0$ and an element of $H^1_0$ -/

section Sandwich

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **The positive part is contractive in $H^1(\Omega)$.** Let $\Omega \subseteq \mathbb{R}^N$ be
open, and let $\psi, w \in H^1(\Omega)$ such that the function of $w$ equals
$\psi^+ = \max(\psi, 0)$ almost everywhere on $\Omega$. Then
$\|w\|_{H^1(\Omega)} \le \|\psi\|_{H^1(\Omega)}$.

This holds because $|\psi^+| \le |\psi|$ and $\partial_i \psi^+ = \mathbf{1}_{\{\psi > 0\}}
\partial_i \psi$. -/
theorem SobolevEuclidean.norm_le_of_fn_ae_eq_posPart {N : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} {ψ w : SobolevEuclidean N 1 2 Ω}
    (hw : fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ max (fn ψ x) 0) :
    ‖w‖ ≤ ‖ψ‖ := by
  have h0 : ‖weakDeriv w 0‖ ≤ ‖weakDeriv ψ 0‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hw] with x hx
    have e : (weakDeriv w 0) x = max (fn ψ x) 0 := hx
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs]
    change |max (fn ψ x) 0| ≤ |fn ψ x|
    exact abs_le.2 ⟨by linarith [abs_nonneg (fn ψ x), le_max_right (fn ψ x) 0],
      max_le (le_abs_self _) (abs_nonneg _)⟩
  have hi : ∀ i, ‖weakDeriv w (MultiIndexLE.single i)‖ ≤ ‖weakDeriv ψ (MultiIndexLE.single i)‖ :=
    fun i ↦ by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [weakDeriv_single_ae_eq_of_fn_ae_eq_posPart hw i] with x hx
      rw [hx]
      exact norm_indicator_le_norm_self _ _
  have hnsq : ∀ v : SobolevEuclidean N 1 2 Ω, ‖v‖ ^ 2
      = ‖weakDeriv v 0‖ ^ 2 + ∑ i, ‖weakDeriv v (MultiIndexLE.single i)‖ ^ 2 := fun v ↦ by
    rw [SobolevMultiIndex.norm_eq_sum (p := 2) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun α _ ↦ sq_nonneg _),
      MultiIndexLE.sum_univ_one]
  have hsq : ‖w‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [hnsq, hnsq]
    refine add_le_add (pow_le_pow_left₀ (norm_nonneg _) h0 2)
      (Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hi i) 2)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- **A function between $0$ and an element of $H^1_0(\Omega)$ lies in $H^1_0(\Omega)$.** Let
$\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be an open set of class $C^1$ with bounded
boundary. Let $v \in H^1(\Omega)$ and $w \in H^1_0(\Omega)$ with $0 \le v \le w$ almost
everywhere on $\Omega$. Then $v \in H^1_0(\Omega)$.

The hypothesis on $\Omega$ is `IsContDiffChartDomain 1`. The extension by zero of $v$ is
$\min(\tilde v^+, \bar w)$, where $\tilde v$ is a Sobolev extension of $v$ to $\mathbb{R}^N$
(Theorem 9.7, `SobolevEuclidean.exists_extensionL`) and $\bar w$ is the extension by zero of $w$
(`SobolevEuclideanZero.extendZeroL`). Both lie in $H^1(\mathbb{R}^N)$, so the extension by zero
of $v$ lies in $H^1(\mathbb{R}^N)$ (`MemSobolevMultiIndex.posPart`). Proposition 9.18, (iii) ⇒
(i) (`SobolevEuclideanZero.mem_of_indicator_memSobolev`), concludes. -/
theorem SobolevEuclideanZero.mem_of_nonneg_of_le
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {v w : SobolevEuclidean (d + 1) 1 2 Ω} (hw : w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hv0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn v x)
    (hvw : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn v x ≤ fn w x) :
    v ∈ SobolevEuclideanZero (d + 1) 1 2 Ω := by
  have hΩm := Ω.isOpen.measurableSet
  -- a Sobolev extension `ṽ` of `v`, and the extension by zero `w̄` of `w`
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL (p := 2) hΩ hΓ
  obtain ⟨V, hV⟩ : ∃ V : SobolevEuclidean (d + 1) 1 2 ⊤, V = P v := ⟨_, rfl⟩
  have hVv : fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn v := by
    rw [hV]
    exact (hP v).1
  obtain ⟨W, hW⟩ : ∃ W : SobolevEuclidean (d + 1) 1 2 ⊤,
      W = SobolevEuclideanZero.extendZeroL (d + 1) 2 Ω ⟨w, hw⟩ := ⟨_, rfl⟩
  have hWw : fn W =ᵐ[volume] (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator (fn w) := by
    rw [hW]
    exact SobolevEuclideanZero.fn_extendZeroL _
  -- almost everywhere for `volume.restrict ⊤` is almost everywhere
  have htop : ∀ {q : EuclideanSpace ℝ (Fin (d + 1)) → Prop},
      (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))).restrict
        ((⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        q x) ↔ ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))), q x := by
    intro q
    rw [Opens.coe_top, Measure.restrict_univ]
  -- `A = ṽ⁺` and `Q = (A − w̄)⁺`, in `H¹(ℝ^N)`
  obtain ⟨A, hA⟩ := ((memSobolevMultiIndex V).posPart one_le_two).exists_sobolevMultiIndex
  obtain ⟨Q, hQ⟩ := ((memSobolevMultiIndex (A - W)).posPart one_le_two).exists_sobolevMultiIndex
  have hAW := Lp.coeFn_sub (weakDeriv A 0) (weakDeriv W 0)
  have hAQ := Lp.coeFn_sub (weakDeriv A 0) (weakDeriv Q 0)
  -- `A − Q = min (ṽ⁺, w̄)` is the extension by zero of `v`
  have hind : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))),
      fn (A - Q) x = (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator (fn v) x := by
    filter_upwards [htop.1 hAQ, htop.1 hA, htop.1 hQ, htop.1 hAW, hWw, (ae_restrict_iff' hΩm).1 hVv,
      (ae_restrict_iff' hΩm).1 hv0, (ae_restrict_iff' hΩm).1 hvw] with x h1 h2 h3 h4 h5 h6 h7 h8
    have e1 : fn (A - Q) x = fn A x - fn Q x := h1
    have e4 : fn (A - W) x = fn A x - fn W x := h4
    rw [e1, h3, e4, h2, h5]
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
    · rw [indicator_of_mem hx, indicator_of_mem hx, h6 hx, max_eq_left (h7 hx),
        max_eq_right (by linarith [h8 hx]), sub_zero]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, sub_zero,
        max_eq_left (le_max_right _ _), sub_self]
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator (fn v)) 1 2 ⊤ volume :=
    (memSobolevMultiIndex (A - Q)).congr_ae (htop.2 hind)
  obtain ⟨v', hv', hvv'⟩ := SobolevEuclideanZero.mem_of_indicator_memSobolev (p := 2)
    (by norm_num) hΩ hmem
  rwa [SobolevMultiIndex.ext_of_fn_ae_eq hvv'.symm]

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open and let $\Phi \in H^1_0(\Omega)$. Then there are
$P, Q \in H^1_0(\Omega)$ with $\Phi = P - Q$, $P \ge 0$ and $Q \ge 0$ almost everywhere on
$\Omega$, $\|P\|_{L^2(\Omega)} \le \|\Phi\|_{L^2(\Omega)}$ and
$\|Q\|_{L^2(\Omega)} \le \|\Phi\|_{L^2(\Omega)}$.

The proof takes $P = \Phi^+$ and $Q = \Phi^- = (-\Phi)^+$, which lie in $H^1_0(\Omega)$ by
`SobolevEuclideanZero.posPart_mem`. -/
theorem SobolevEuclideanZero.exists_eq_sub_of_nonneg {Φ : SobolevEuclidean (d + 1) 1 2 Ω}
    (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ∃ P ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, ∃ Q ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      Φ = P - Q ∧
      (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn P x) ∧
      (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Q x) ∧
      ‖weakDeriv P 0‖ ≤ ‖weakDeriv Φ 0‖ ∧ ‖weakDeriv Q 0‖ ≤ ‖weakDeriv Φ 0‖ := by
  obtain ⟨P, hP⟩ := ((memSobolevMultiIndex Φ).posPart one_le_two).exists_sobolevMultiIndex
  obtain ⟨Q, hQ⟩ := ((memSobolevMultiIndex (-Φ)).posPart one_le_two).exists_sobolevMultiIndex
  have hPmem : P ∈ SobolevEuclideanZero (d + 1) 1 2 Ω :=
    SobolevEuclideanZero.posPart_mem (p := 2) (by norm_num) ⟨Φ, hΦ⟩ hP
  have hQmem : Q ∈ SobolevEuclideanZero (d + 1) 1 2 Ω :=
    SobolevEuclideanZero.posPart_mem (p := 2) (by norm_num) ⟨-Φ, neg_mem hΦ⟩ hQ
  have hnegΦ : fn (-Φ) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] -fn Φ := by
    have h1 : weakDeriv (-Φ) 0 = -weakDeriv Φ 0 := by
      rw [← weakDerivL_apply, map_neg, weakDerivL_apply]
    rw [show fn (-Φ) = ⇑(weakDeriv (-Φ) 0) from rfl, h1]
    exact Lp.coeFn_neg _
  refine ⟨P, hPmem, Q, hQmem, ?_, ?_, ?_, ?_, ?_⟩
  · refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
    filter_upwards [Lp.coeFn_sub (weakDeriv P 0) (weakDeriv Q 0), hP, hQ, hnegΦ]
      with x h1 h2 h3 h4
    have e : fn (P - Q) x = fn P x - fn Q x := h1
    rw [e, h2, h3, h4, Pi.neg_apply]
    rcases le_total (fn Φ x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
      ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
      ring
  · filter_upwards [hP] with x hx
    rw [hx]
    exact le_max_right _ _
  · filter_upwards [hQ] with x hx
    rw [hx]
    exact le_max_right _ _
  · refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hP] with x hx
    have e : (weakDeriv P 0) x = max (fn Φ x) 0 := hx
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs]
    change |max (fn Φ x) 0| ≤ |fn Φ x|
    exact abs_le.2 ⟨by linarith [abs_nonneg (fn Φ x), le_max_right (fn Φ x) 0],
      max_le (le_abs_self _) (abs_nonneg _)⟩
  · refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hQ, hnegΦ] with x hx hx'
    have e : (weakDeriv Q 0) x = max (-fn Φ x) 0 := by
      rw [show (weakDeriv Q 0) x = fn Q x from rfl, hx, hx', Pi.neg_apply]
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs]
    change |max (-fn Φ x) 0| ≤ |fn Φ x|
    exact abs_le.2 ⟨by linarith [abs_nonneg (fn Φ x), le_max_right (-fn Φ x) 0],
      max_le (by linarith [neg_abs_le (fn Φ x), le_abs_self (fn Φ x)]) (abs_nonneg _)⟩

end Sandwich
