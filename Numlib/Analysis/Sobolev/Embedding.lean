/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, beside the
Gagliardo–Nirenberg–Sobolev inequality for compactly supported `C¹` functions.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.MeasureTheory.Constructions.Pi
import Numlib.MeasureTheory.Function.LpInterpolation

/-!
# Sobolev inequalities on the whole space

This file proves the Sobolev embeddings of $W^{1,p}(\mathbb{R}^N)$ and $W^{m,p}(\mathbb{R}^N)$,
following [brezis2011functional], §9.3.A: Theorem 9.9, Corollaries 9.10 and 9.11, Theorem 9.12 with
Remarks 11 and 12, Corollary 9.13 with its footnotes 12–14, and Remark 13, together with the step
"$e_n \in C^\infty(\Omega)$" of the proof of Theorem 9.31. For $1 \le p < N$ and the Sobolev
conjugate exponent $p^*$, defined by $1/p^* = 1/p - 1/N$, the **Sobolev–Gagliardo–Nirenberg
inequality** $\|u\|_{p^*} \le C \|\nabla u\|_p$ gives $W^{1,p}(\mathbb{R}^N) \subset
L^q(\mathbb{R}^N)$ for $p \le q \le p^*$. For $p = N \ge 2$ the inclusion holds for every
$q \in [N, \infty)$. For $N < p < \infty$, **Morrey's theorem** gives a continuous representative
$\tilde u$ with
$$|\tilde u(x) - \tilde u(y)| \le C \|x - y\|^{1 - N/p} \|\nabla u\|_p, \qquad |\tilde u(x)| \le C'
  \|u\|_{W^{1,p}},$$
and $\tilde u(x) \to 0$ as $\|x\| \to \infty$.

Repeated application of these first-order results gives Corollary 9.13: $W^{m,p}(\mathbb{R}^N)
\subset L^q(\mathbb{R}^N)$ for $p \le q < \infty$ with $1/p - m/N \le 1/q$, $W^{m,p}(\mathbb{R}^N)
\subset L^\infty(\mathbb{R}^N)$ with a Hölder continuous representative for $m > N/p$, and
$W^{m,p}(\mathbb{R}^N) \subset C^k(\mathbb{R}^N)$ for $k + N/p < m$, with the derivatives of order
$k$ Hölder continuous. The local form gives a $C^k$ representative on $\Omega$ for every function of
$W^{m,p}_{\mathrm{loc}}(\Omega)$. Remark 13 gives $W^{N,1}(\mathbb{R}^N) \subset
L^\infty(\mathbb{R}^N)$. The versions on domains are in `Numlib.Analysis.Sobolev.EmbeddingDomain`,
the compact embeddings (Theorem 9.16) are in `Numlib.Analysis.Sobolev.Compactness`, and the
one-dimensional theory is in `Numlib.Analysis.Sobolev.Interval.Embedding`.

## Main definitions

* `SobolevEuclidean.gnsConst`: the constant $C(p, N)$ of the Sobolev–Gagliardo–Nirenberg inequality
  on $\mathbb{R}^N$.
* `MeasureTheory.morreyConst`, `MeasureTheory.morreySupConst`: the constants
  $C = 4 \mu(B(0,1))^{-1/p} / (1 - N/p)$ and $C' = 2 \mu(B(0,1))^{-1/p} / (1 - N/p)$ of Morrey's
  inequalities.
* `SobolevEuclidean.contRep`: the continuous representative of $u \in W^{1,p}(\mathbb{R}^N)$ for
  $N < p < \infty$, as a bounded continuous function.
* `SobolevEuclidean.toBoundedContinuousMapL`: the bounded linear map $u \mapsto \tilde u$ from
  $W^{1,p}(\mathbb{R}^N)$ to the bounded continuous functions, for $N < p < \infty$.

## Main results

* `HasWeakFDerivOn.exists_seq_contDiff_hasCompactSupport_tendsto_top`: a function
  $f \in W^{1,p}(\mathbb{R}^N)$, $1 \le p < \infty$, with weak derivative $w$ is the limit of smooth
  compactly supported $u_n$ with $u_n \to f$ and $\nabla u_n \to w$ in $L^p$.
* `HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq`: the Sobolev–Gagliardo–Nirenberg inequality
  $\|f\|_{p^*} \le C \|w\|_p$ for $f \in W^{1,p}(\mathbb{R}^N)$, $1 \le p < N$ (Theorem 9.9).
* `SobolevEuclidean.eLpNorm_fn_le_of_eq`, `SobolevEuclidean.isContinuousEmbedding_toLp_of_eq`: the
  same inequality on the space $W^{1,p}(\mathbb{R}^N)$, and $W^{1,p}(\mathbb{R}^N) \hookrightarrow
  L^{p^*}(\mathbb{R}^N)$.
* `SobolevEuclidean.isContinuousEmbedding_toLp_of_le_of_le`: $W^{1,p}(\mathbb{R}^N) \hookrightarrow
  L^q(\mathbb{R}^N)$ for $1 \le p < N$ and $p \le q \le p^*$ (Corollary 9.10).
* `MeasureTheory.exists_forall_eLpNorm_le_of_eq_finrank`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_eq_finrank`: $W^{1,N}(\mathbb{R}^N)
  \hookrightarrow L^q(\mathbb{R}^N)$ for $N \ge 2$ and $N \le q < \infty$ (Corollary 9.11).
* `ContDiff.lintegral_enorm_sub_le_of_mem_closedBall`, `ContDiff.enorm_sub_le_of_lt`,
  `ContDiff.enorm_le_of_lt`: Morrey's estimates for $C^1$ functions, on balls.
* `HasWeakFDerivOn.exists_continuous_holderWith_ae_eq`: Morrey's theorem for $N < p < \infty$, with
  the continuous representative, its Hölder estimate, its sup bound and its decay at infinity
  (Theorem 9.12 with Remarks 11 and 12).
* `SobolevEuclidean.isContinuousEmbedding_toBoundedContinuousMapL`: $W^{1,p}(\mathbb{R}^N)
  \hookrightarrow C_b(\mathbb{R}^N)$ for $N < p < \infty$.
* `SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le`: a bound of
  $W^{m,p}(\mathbb{R}^N)$ in $L^q$ gives $W^{m+1,p}(\mathbb{R}^N) \subset W^{1,q}(\mathbb{R}^N)$.
* `SobolevEuclidean.isContinuousEmbedding_toLp_of_order`: $W^{m,p}(\mathbb{R}^N) \hookrightarrow
  L^q(\mathbb{R}^N)$ for $p \le q < \infty$ with $1/p - m/N \le 1/q$ (Corollary 9.13).
* `SobolevEuclidean.exists_forall_continuous_ae_eq_of_order`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_top_of_order`: for $m > N/p$, a Hölder continuous
  representative and $W^{m,p}(\mathbb{R}^N) \hookrightarrow L^\infty(\mathbb{R}^N)$ (Corollary
  9.13).
* `SobolevEuclidean.exists_contDiff_ae_eq_of_order`, `SobolevEuclidean.exists_contDiff_ae_eq_of_lt`:
  for $k + N/p < m$, a $C^k$ representative with bounded derivatives of order at most $k$ and Hölder
  derivatives of order $k$ (Corollary 9.13).
* `MemSobolevMultiIndexLoc.exists_contDiffOn_of_lt`, `MemSobolevMultiIndexLoc.exists_contDiffOn`: a
  function of $W^{m,p}_{\mathrm{loc}}(\Omega)$ with $k + N/p < m$ has a $C^k$ representative on
  $\Omega$, and a function of $H^m_{\mathrm{loc}}(\Omega)$ for every $m$ has a $C^\infty$
  representative on $\Omega$.
* `SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one`: every
  $u \in W^{N,1}(\mathbb{R}^N)$ has a continuous representative bounded by $\|u\|$ (Remark 13).
* `MeasureTheory.lintegral_prod_comp_succAbove_le`: Gagliardo's lemma in its general form (Lemma
  9.4).

## Proof outline

Each inequality is first proved for $C^1$ (or smooth) compactly supported functions. It passes to
$W^{1,p}(\mathbb{R}^N)$ by density and Fatou's lemma: the smooth approximants converge in $L^p$,
hence almost everywhere along a subsequence. Morrey's estimates on a ball $B$ of radius $r$ come
from the segment bound $|u(z) - u(x)| \le \|z - x\| \int_0^1 |\nabla u(x + t(z - x))| \, dt$,
Fubini's theorem, the homothety $z \mapsto x + t(z - x)$ and Hölder's inequality. In Morrey's
theorem the approximants form a Cauchy sequence of bounded continuous functions, whose limit is the
continuous representative. Corollary 9.13 is proved by induction on $m$, and its $C^k$ clause by
induction on $k$, through the converse of Remark 2
(`HasWeakFDerivOn.exists_contDiffOn_ae_eq_of_continuousOn`). Remark 13 comes from the fundamental
theorem of calculus applied in each coordinate in turn.

## Notation

* $N$ is the dimension of the space $E$, and $\mu$ is an additive Haar measure on $E$; on
  $\mathbb{R}^N$ the measure is Lebesgue measure.
* $\nabla u$ is the derivative of $u$, a function with values in the continuous linear maps
  $E \to F$, and $\|\nabla u\|_p$ is the $L^p$ norm of its operator norm.
* $p^*$ is the Sobolev conjugate exponent, $1/p^* = 1/p - 1/N$, and $N' = N/(N-1)$.
* $W^{k,p}(\Omega)$ is `SobolevEuclidean N k p Ω`, with the norm $\|u\| = (\sum_{|\alpha| \le k}
  \|\partial^\alpha u\|_p^p)^{1/p}$ for $p < \infty$ and $\|u\| = \max_{|\alpha| \le k}
  \|\partial^\alpha u\|_\infty$ for $p = \infty$, and $\partial_i u$ is `SobolevMultiIndex.weakDeriv
  u (MultiIndexLE.single i)`.
* For $u$ in a Sobolev space, $\|u\|_q$ is the $L^q$ norm of its function `SobolevMultiIndex.fn u`,
  and $\|u\|$ without an index is its Sobolev norm.

## Implementation notes

* Each inequality is stated twice: for a function with a weak derivative on the whole space
  (`HasWeakFDerivOn f w ⊤ μ`, on a finite-dimensional real normed space with an additive Haar
  measure, as in Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`), and on the space
  `SobolevEuclidean N k p ⊤`, as a bound on `SobolevMultiIndex.fn u` and as an
  `IsContinuousEmbedding` of the inclusion `SobolevMultiIndex.toLpₗ`.
* Exponents are in `ℝ≥0`. The Sobolev conjugate $p^*$ is given by its defining relation
  `(p' : ℝ)⁻¹ = p⁻¹ - N⁻¹`, as in Mathlib. The spaces carry `[Fact (1 ≤ p)]`.
* The ratios $m/N$, $1/N$ and $N/p$ are real divisions. At $N = 0$ the ratios $m/N$ and $1/N$ are
  $0$.
* Morrey's theorem is stated for finite $p$ only. The case $p = \infty$ is the Lipschitz
  representative of Remark 7, `HasWeakFDerivOn.exists_lipschitzOnWith_ae_eq_of_convex`, and is not
  restated here.
* The proof of Morrey's estimates uses balls instead of the cubes of [brezis2011functional]. The
  homothety $z \mapsto x + t(z - x)$, $0 \le t \le 1$, maps every convex set that contains $x$ into
  itself and scales the Haar measure by $t^N$ (`MeasureTheory.setLIntegral_comp_homothety`), so no
  coordinates are needed. The constants differ from the cube constants of the source.
* The higher-order statements carry the hypothesis $N \ge 2$ or $p > 1$. The chain of first-order
  embeddings cannot start from $W^{1,1}(\mathbb{R})$, because Corollary 9.11 needs $N \ge 2$; the
  one-dimensional case is in `Numlib.Analysis.Sobolev.Interval.Embedding`. Remark 13,
  $W^{N,1}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$, is the one case that the chain misses and
  the source settles. It is proved directly on the smooth approximants. Its step from the derivative
  of order $N$ as a multilinear map to the multi-index derivative $\partial_1 \cdots \partial_N u$
  uses `HasWeakIteratedFDerivOn.lineDeriv` and `multiIndexDirections_multiIndexCount_perm`.
* The standard basis vectors are indexed from $0$: `EuclideanSpace.stdVec N n` is $e_n$ for $n < N$.
  The mixed derivative $\partial_1 \cdots \partial_N$ of the source is the derivative in the
  directions $e_0, \dots, e_{N-1}$.
* Lemma 9.4 (Gagliardo's lemma) in its general form is
  `MeasureTheory.lintegral_prod_comp_succAbove_le`, proved by the induction on $N$ of the source
  with the coordinates split as `Fin.cons s t`. The proof of Theorem 9.9 uses Mathlib's special case
  `MeasureTheory.lintegral_prod_lintegral_pow_le` instead.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

noncomputable section

/-! ### From convergence in the Sobolev norm to convergence of the function and the gradient -/

section Approximation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {w : E → E →L[ℝ] F}
  {p : ℝ≥0∞}

omit [μ.IsAddHaarMeasure] in
/-- Let $E$ be a finite-dimensional real normed space with a measure $\mu$, let $F$ be a real Banach
space, and let $1 \le p < \infty$. If $w$ is a weak derivative of $f : E \to F$ on $E$, then
$\|f\|_p$ is at most the Sobolev norm of order one of $f$, `sobolevNorm f 1 p ⊤ μ`. -/
theorem HasWeakFDerivOn.eLpNorm_le_sobolevNorm_one (h : HasWeakFDerivOn f w ⊤ μ) (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) : eLpNorm f p μ ≤ sobolevNorm f 1 p ⊤ μ := by
  have hloc : LocallyIntegrable f μ :=
    locallyIntegrableOn_univ.1 (by simpa using h.locallyIntegrableOn)
  have hW := hasWeakIteratedFDerivOn_zero (μ := μ) (Ω := ⊤) (locallyIntegrableOn_univ.2 hloc)
  have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖weakIteratedFDeriv 0 f ⊤ μ x‖ₑ := by
    filter_upwards [hW.weakIteratedFDeriv_ae_eq] with x hx
    rw [hx (by simp), enorm_eq_nnnorm, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map]
  calc eLpNorm f p μ ≤ eLpNorm (weakIteratedFDeriv 0 f ⊤ μ) p μ :=
        eLpNorm_mono_enorm_ae hloc.aestronglyMeasurable (hae.mono fun x hx ↦ hx.le)
    _ = eLpNorm (weakIteratedFDeriv 0 f ⊤ μ) p (μ.restrict ((⊤ : Opens E) : Set E)) := by
        rw [Measure.restrict_coe_top]
    _ ≤ sobolevNorm f 1 p ⊤ μ := eLpNorm_weakIteratedFDeriv_le_sobolevNorm hp hp' (Nat.zero_le 1)

omit [μ.IsAddHaarMeasure] in
/-- Let $E$ be a finite-dimensional real normed space with a measure $\mu$, let $F$ be a real Banach
space, and let $1 \le p < \infty$. If $w$ is a weak derivative of $f : E \to F$ on $E$, then
$\|w\|_p$ is at most the Sobolev norm of order one of $f$, `sobolevNorm f 1 p ⊤ μ`. -/
theorem HasWeakFDerivOn.eLpNorm_weakDeriv_le_sobolevNorm_one (h : HasWeakFDerivOn f w ⊤ μ)
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) : eLpNorm w p μ ≤ sobolevNorm f 1 p ⊤ μ := by
  have hloc : LocallyIntegrable w μ :=
    locallyIntegrableOn_univ.1 (by simpa using h.locallyIntegrableOn_weakDeriv)
  have hae : ∀ᵐ x ∂μ, ‖w x‖ₑ = ‖weakIteratedFDeriv 1 f ⊤ μ x‖ₑ := by
    filter_upwards [HasWeakIteratedFDerivOn.weakIteratedFDeriv_ae_eq h] with x hx
    rw [hx (by simp), enorm_eq_nnnorm, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map]
  calc eLpNorm w p μ ≤ eLpNorm (weakIteratedFDeriv 1 f ⊤ μ) p μ :=
        eLpNorm_mono_enorm_ae hloc.aestronglyMeasurable (hae.mono fun x hx ↦ hx.le)
    _ = eLpNorm (weakIteratedFDeriv 1 f ⊤ μ) p (μ.restrict ((⊤ : Opens E) : Set E)) := by
        rw [Measure.restrict_coe_top]
    _ ≤ sobolevNorm f 1 p ⊤ μ := eLpNorm_weakIteratedFDeriv_le_sobolevNorm hp hp' le_rfl

omit [FiniteDimensional ℝ E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- Let $\Omega$ be an open subset of a real normed space $E$ with a measure $\mu$. If $w_1$ and
$w_2$ are weak derivatives of $f_1$ and $f_2$ on $\Omega$, then $w_1 - w_2$ is a weak derivative
of $f_1 - f_2$ on $\Omega$. -/
protected theorem HasWeakFDerivOn.sub {Ω : Opens E} {f₁ f₂ : E → F} {w₁ w₂ : E → E →L[ℝ] F}
    (h₁ : HasWeakFDerivOn f₁ w₁ Ω μ) (h₂ : HasWeakFDerivOn f₂ w₂ Ω μ) :
    HasWeakFDerivOn (f₁ - f₂) (w₁ - w₂) Ω μ := by
  have := HasWeakIteratedFDerivOn.sub h₁ h₂
  unfold HasWeakFDerivOn
  convert this using 2 with x
  simp

omit [CompleteSpace F] in
/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, and let
$\Omega \subseteq E$ be open. A $C^1$ function $g : E \to F$ has its derivative $\nabla g$ as
weak derivative on $\Omega$. -/
theorem ContDiff.hasWeakFDerivOn {Ω : Opens E} {g : E → F} (hg : ContDiff ℝ 1 g) :
    HasWeakFDerivOn g (fderiv ℝ g) Ω μ := by
  have := ContDiffOn.hasWeakIteratedFDerivOn (μ := μ) (Ω := Ω) (m := 1) hg.contDiffOn le_rfl
  unfold HasWeakFDerivOn
  convert this using 2 with x
  rw [iteratedFDeriv_one_eq_symm_fderiv]

/-- **Density of $C_c^\infty$ in $W^{1,p}(\mathbb{R}^N)$, for the function and its gradient.** Let
$E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, let $F$ be a
real Banach space, and let $1 \le p < \infty$. Let $f, w \in L^p$, where $w$ is a weak
derivative of $f$ on $E$. Then there are smooth compactly supported $u_n : E \to F$ with
$$\|u_n - f\|_p \to 0 \quad \text{and} \quad \|\nabla u_n - w\|_p \to 0.$$
This is the whole-space part of Theorem 9.2 of [brezis2011functional], in the form that the
proofs of §9.3 use.

The proof reads the two components of the Sobolev norm of $u_n - f$ in
`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`. -/
theorem HasWeakFDerivOn.exists_seq_contDiff_hasCompactSupport_tendsto_top
    (h : HasWeakFDerivOn f w ⊤ μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : MemLp f p μ)
    (hw : MemLp w p μ) :
    ∃ u : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      Tendsto (fun n ↦ eLpNorm (u n - f) p μ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p μ) atTop (𝓝 0) := by
  have hfs : MemSobolev f 1 p ⊤ μ := h.memSobolev (by simpa [Measure.restrict_coe_top] using hf)
    (by simpa [Measure.restrict_coe_top] using hw)
  obtain ⟨u, hus, huc, hut⟩ := hfs.exists_seq_hasCompactSupport_tendsto_sobolevNorm hp hp'
  refine ⟨u, hus, huc, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hut (fun _ ↦ zero_le)
      fun n ↦ ?_
    exact (((hus n).of_le (by simp)).hasWeakFDerivOn.sub h).eLpNorm_le_sobolevNorm_one hp hp'
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hut (fun _ ↦ zero_le)
      fun n ↦ ?_
    have := (((hus n).of_le (by simp)).hasWeakFDerivOn.sub h).eLpNorm_weakDeriv_le_sobolevNorm_one
      hp hp'
    simpa only [Pi.sub_apply, Pi.sub_def] using this

end Approximation

/-!
### The Sobolev–Gagliardo–Nirenberg inequality on $W^{1,p}(\mathbb{R}^N)$

This is Theorem 9.9 of [brezis2011functional].
-/

section GNS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {w : E → E →L[ℝ] F}

/-- The **Sobolev–Gagliardo–Nirenberg inequality**. Let $E$ be a real normed space of finite
dimension $N$ with an additive Haar measure $\mu$, and let $F$ be a finite-dimensional real
normed space. Let $1 \le p < N$ and let $p^*$ satisfy $1/p^* = 1/p - 1/N$. If $f, w \in L^p$ and
$w$ is a weak derivative of $f$ on $E$, then
$$\|f\|_{p^*} \le C \|w\|_p,$$
where $C$ is Mathlib's constant `MeasureTheory.SNormLESNormFDerivOfEqConst F μ p`. This is
Theorem 9.9 of [brezis2011functional].

For compactly supported $C^1$ functions the inequality is Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`. It passes to $f$ by density and Fatou's lemma:
the approximants of `HasWeakFDerivOn.exists_seq_contDiff_hasCompactSupport_tendsto_top` converge
almost everywhere along a subsequence, and their $L^{p^*}$ norms are eventually at most
$C (\|w\|_p + \delta)$ for every $\delta > 0$. -/
theorem HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq (h : HasWeakFDerivOn f w ⊤ μ)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpN : p < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) (hf : MemLp f p μ) (hw : MemLp w p μ) :
    eLpNorm f p' μ ≤ SNormLESNormFDerivOfEqConst F μ p * eLpNorm w p μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have hn : 0 < finrank ℝ E := by
    have : (0 : ℝ) < finrank ℝ E := lt_of_lt_of_le (by exact_mod_cast zero_lt_one.trans_le hp)
      (by exact_mod_cast hpN.le)
    exact_mod_cast this
  obtain ⟨u, hus, huc, hu0, hu1⟩ :=
    h.exists_seq_contDiff_hasCompactSupport_tendsto_top hp1 ENNReal.coe_ne_top hf hw
  -- an almost everywhere convergent subsequence
  have hmeas : TendstoInMeasure μ u atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (by exact_mod_cast (zero_lt_one.trans_le hp).ne') hu0
  obtain ⟨ns, hns_mono, hns⟩ := hmeas.exists_seq_tendsto_ae
  -- the bound on each approximant
  have hbound : ∀ n, eLpNorm (u n) p' μ
      ≤ SNormLESNormFDerivOfEqConst F μ p * eLpNorm (fderiv ℝ (u n)) p μ := fun n ↦
    eLpNorm_le_eLpNorm_fderiv_of_eq μ ((hus n).of_le (by simp)) (huc n) hp hn hp'
  -- for every `δ > 0`, the approximants are eventually bounded by `C (‖w‖_p + δ)`
  have key : ∀ δ : ℝ≥0∞, 0 < δ → eLpNorm f p' μ
      ≤ SNormLESNormFDerivOfEqConst F μ p * (eLpNorm w p μ + δ) := by
    intro δ hδ
    have hev : ∀ᶠ n in atTop, eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p μ ≤ δ :=
      ENNReal.tendsto_nhds_zero.1 hu1 δ hδ
    refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun n ↦ u (ns n)) ?_
      (fun n ↦ (hus _).continuous.aestronglyMeasurable) hf.aestronglyMeasurable hns
    filter_upwards [hns_mono.tendsto_atTop.eventually hev] with n hn
    refine (hbound (ns n)).trans (mul_le_mul' le_rfl ?_)
    have hsplit : fderiv ℝ (u (ns n)) = (fun x ↦ fderiv ℝ (u (ns n)) x - w x) + w := by
      funext x
      simp
    rw [hsplit]
    exact (eLpNorm_add_le hp1).trans (by rw [add_comm]; exact add_le_add le_rfl hn)
  -- let `δ → 0`
  have hlim : Tendsto (fun δ : ℝ≥0∞ ↦ SNormLESNormFDerivOfEqConst F μ p * (eLpNorm w p μ + δ))
      (𝓝[>] 0) (𝓝 (SNormLESNormFDerivOfEqConst F μ p * eLpNorm w p μ)) := by
    have : Tendsto (fun δ : ℝ≥0∞ ↦ eLpNorm w p μ + δ) (𝓝[>] 0) (𝓝 (eLpNorm w p μ + 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.add tendsto_id)
    rw [add_zero] at this
    exact ENNReal.Tendsto.const_mul this (Or.inr ENNReal.coe_ne_top)
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ ↦ key δ hδ)

/-- Under the hypotheses of `HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq` ($1 \le p < N$,
$1/p^* = 1/p - 1/N$, and $f, w \in L^p$ with $w$ a weak derivative of $f$ on $E$), the function
$f$ lies in $L^{p^*}$. -/
theorem HasWeakFDerivOn.memLp_of_eq (h : HasWeakFDerivOn f w ⊤ μ)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpN : p < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) (hf : MemLp f p μ) (hw : MemLp w p μ) :
    MemLp f p' μ :=
  memLp_iff.2 ((h.eLpNorm_le_eLpNorm_weakFDeriv_of_eq hp hpN hp' hf hw).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hw.eLpNorm_lt_top))

end GNS

/-! ### The Sobolev–Gagliardo–Nirenberg inequality on the space $W^{1,p}(\mathbb{R}^N)$ -/

section Typed

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open SobolevMultiIndex

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and $1 \le p$. For $u \in W^{1,p}(\Omega)$, the
partial derivatives satisfy
$$\sum_{i} \|\partial_i u\|_{L^p(\Omega)} \le N \|u\|.$$
-/
theorem SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (u : SobolevEuclidean N 1 p Ω) :
    ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ ≤ N * ENNReal.ofReal ‖u‖ := by
  calc ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖
      ≤ ∑ _i : Fin N, ENNReal.ofReal ‖u‖ :=
        Finset.sum_le_sum fun i _ ↦ ENNReal.ofReal_le_ofReal (norm_weakDeriv_le u _)
    _ = N * ENNReal.ofReal ‖u‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [Fact (1 ≤ p)] in
/-- For $u \in W^{k,p}(\mathbb{R}^N)$, the function `SobolevMultiIndex.fn u` lies in
$L^p(\mathbb{R}^N)$. -/
theorem SobolevEuclidean.memLp_fn {k : ℕ} (u : SobolevEuclidean N k p ⊤) :
    MemLp (fn u) p volume := by
  simpa [Measure.restrict_coe_top] using SobolevMultiIndex.memLp u

/-- Let $1 \le p$. Every $u \in W^{1,p}(\mathbb{R}^N)$ has a weak derivative $w$ on $\mathbb{R}^N$,
with values in the linear functionals on $\mathbb{R}^N$, such that $w \in L^p$ and
$$\|w\|_p \le \sum_i \|\partial_i u\|_p.$$
-/
theorem SobolevEuclidean.exists_hasWeakFDerivOn (u : SobolevEuclidean N 1 p ⊤) :
    ∃ w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
      HasWeakFDerivOn (fn u) w ⊤ volume ∧ MemLp w p volume ∧
      eLpNorm w p volume ≤ ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ := by
  obtain ⟨w, hw, hwp⟩ := ((memSobolevMultiIndex u).memSobolev).exists_hasWeakFDerivOn
  rw [Measure.restrict_coe_top] at hwp
  exact ⟨w, hw, hwp, SobolevEuclidean.eLpNorm_le_sum_of_hasWeakFDerivOn u hw⟩

end Typed

section TypedGNS

variable {N : ℕ} {p p' : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

open SobolevMultiIndex

variable (N) in
/-- The **constant of the Sobolev–Gagliardo–Nirenberg inequality on $\mathbb{R}^N$**: the constant
$C(p, N)$ of Theorem 9.9 of [brezis2011functional], defined as Mathlib's
`MeasureTheory.SNormLESNormFDerivOfEqConst` for real-valued functions and Lebesgue measure on
$\mathbb{R}^N$. -/
def SobolevEuclidean.gnsConst (p : ℝ) : ℝ≥0 :=
  SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin N))) p

/-- The **Sobolev–Gagliardo–Nirenberg inequality on $W^{1,p}(\mathbb{R}^N)$**. Let $1 \le p < N$ and
let $p^*$ satisfy $1/p^* = 1/p - 1/N$. For every $u \in W^{1,p}(\mathbb{R}^N)$,
$$\|u\|_{p^*} \le C \sum_i \|\partial_i u\|_p,$$
where $C$ is `SobolevEuclidean.gnsConst N p`. This is the inequality (17) of Theorem 9.9 of
[brezis2011functional].

The proof applies `HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq` to the weak derivative
of `SobolevEuclidean.exists_hasWeakFDerivOn`. -/
theorem SobolevEuclidean.eLpNorm_fn_le_of_eq (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclidean N 1 p ⊤) :
    eLpNorm (fn u) (p' : ℝ≥0∞) volume ≤ SobolevEuclidean.gnsConst N p
      * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ := by
  have hp : 1 ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  obtain ⟨w, hw, hwp, hwle⟩ := SobolevEuclidean.exists_hasWeakFDerivOn u
  have hN : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  refine (hw.eLpNorm_le_eLpNorm_weakFDeriv_of_eq hp (by rw [hN]; exact_mod_cast hpN)
    (by rw [hN]; exact hp') (SobolevEuclidean.memLp_fn u) hwp).trans ?_
  exact mul_le_mul' le_rfl hwle

/-- Let $1 \le p < N$ and let $p^*$ satisfy $1/p^* = 1/p - 1/N$. Then $W^{1,p}(\mathbb{R}^N)
\subseteq L^{p^*}(\mathbb{R}^N)$: for every $u \in W^{1,p}(\mathbb{R}^N)$, the function
`SobolevMultiIndex.fn u` lies in $L^{p^*}(\mathbb{R}^N)$. This is the inclusion of Theorem 9.9
of [brezis2011functional]. -/
theorem SobolevEuclidean.memLp_fn_of_eq (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (u : SobolevEuclidean N 1 p ⊤) : MemLp (fn u) (p' : ℝ≥0∞) volume :=
  memLp_iff.2 ((SobolevEuclidean.eLpNorm_fn_le_of_eq hpN hp' u).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.sum_lt_top.2 fun _ _ ↦ ENNReal.ofReal_lt_top)))

/-- Let $1 \le p < N$ and let $p^*$ satisfy $1/p^* = 1/p - 1/N$. For every
$u \in W^{1,p}(\mathbb{R}^N)$,
$$\|u\|_{p^*} \le C N \|u\|,$$
where $C$ is `SobolevEuclidean.gnsConst N p`. This is Theorem 9.9 of [brezis2011functional] with
the bound in the norm of $W^{1,p}(\mathbb{R}^N)$. -/
theorem SobolevEuclidean.eLpNorm_fn_le_norm_of_eq (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (u : SobolevEuclidean N 1 p ⊤) :
    eLpNorm (fn u) (p' : ℝ≥0∞) volume
      ≤ ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N * ‖u‖) := by
  refine (SobolevEuclidean.eLpNorm_fn_le_of_eq hpN hp' u).trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal, mul_assoc]
  exact mul_le_mul' le_rfl (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u)

/-- Let $1 \le p < N$ and let $p^*$ satisfy $1/p^* = 1/p - 1/N$. Then $W^{1,p}(\mathbb{R}^N)
\hookrightarrow L^{p^*}(\mathbb{R}^N)$ is a continuous embedding: the inclusion
`SobolevMultiIndex.toLpₗ` is injective and bounded. This is the "continuous injection" of
Theorem 9.9 of [brezis2011functional]. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_eq [Fact (1 ≤ (p' : ℝ≥0∞))] (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_of_eq hpN hp' u) := by
  refine isContinuousEmbedding_toLpₗ _ (C := SobolevEuclidean.gnsConst N p * N)
    fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (show (0 : ℝ) ≤ SobolevEuclidean.gnsConst N p * N * ‖u‖ by positivity)]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  exact (eLpNorm_restrict_coe_top (fn u) (p' : ℝ≥0∞)).trans_le
    (SobolevEuclidean.eLpNorm_fn_le_norm_of_eq hpN hp' u)

end TypedGNS

/-!
### The intermediate exponents

This is Corollary 9.10 of [brezis2011functional].
-/

section Interpolation

/-- For $a, b \in [0, \infty]$ and $0 \le \theta \le 1$,
$$a^\theta b^{1 - \theta} \le a + b.$$

This is the form of Young's inequality that the proof of Corollary 9.10 of
[brezis2011functional] uses to turn the interpolation inequality $\|u\|_q \le \|u\|_p^\theta
\|u\|_{p^*}^{1 - \theta}$ into $\|u\|_q \le \|u\|_p + \|u\|_{p^*}$. -/
theorem ENNReal.rpow_mul_rpow_one_sub_le_add (a b : ℝ≥0∞) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    a ^ θ * b ^ (1 - θ) ≤ a + b := by
  calc a ^ θ * b ^ (1 - θ) ≤ (a + b) ^ θ * (a + b) ^ (1 - θ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow le_self_add hθ₀)
          (ENNReal.rpow_le_rpow le_add_self (by linarith))
    _ = a + b := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hθ₀ (by linarith), add_sub_cancel, ENNReal.rpow_one]

/-- The **interpolation inequality in additive form**. Let $f$ be an almost everywhere strongly
measurable function on a measure space, and let $0 < p \le r \le q \le \infty$. Then
$$\|f\|_r \le \|f\|_p + \|f\|_q.$$
This is used in the proof of Corollary 9.10 of [brezis2011functional]. -/
theorem MeasureTheory.eLpNorm_le_eLpNorm_add_eLpNorm_of_le_of_le {α G : Type*}
    [MeasurableSpace α] {ν : Measure α} [NormedAddCommGroup G] {f : α → G}
    (hf : AEStronglyMeasurable f ν) {p q r : ℝ≥0∞} (hp : p ≠ 0) (hpr : p ≤ r) (hrq : r ≤ q) :
    eLpNorm f r ν ≤ eLpNorm f p ν + eLpNorm f q ν := by
  obtain ⟨θ, hθ₀, hθ₁, hr⟩ := exists_inv_eq_ofReal_mul_inv_add hp hpr hrq
  exact (eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hf hθ₀ hθ₁ hr).trans
    (ENNReal.rpow_mul_rpow_one_sub_le_add _ _ hθ₀ hθ₁)

end Interpolation

section TypedGNSLe

variable {N : ℕ} {p p' q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

open SobolevMultiIndex

/-- Let $1 \le p \le \infty$. For $u \in W^{k,p}(\mathbb{R}^N)$, the $L^p$ norm of the function
`SobolevMultiIndex.fn u` is at most the norm $\|u\|$ of $u$ in $W^{k,p}(\mathbb{R}^N)$. -/
theorem SobolevEuclidean.eLpNorm_fn_le_ofReal_norm {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : SobolevEuclidean N k p ⊤) : eLpNorm (fn u) p volume ≤ ENNReal.ofReal ‖u‖ := by
  have h : ‖weakDeriv u 0‖ = (eLpNorm (fn u) p volume).toReal := by
    rw [Lp.norm_def, eLpNorm_restrict_coe_top]
    rfl
  rw [← ENNReal.ofReal_toReal (SobolevEuclidean.memLp_fn u).eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (h ▸ norm_weakDeriv_le u 0)

/-- Let $1 \le p < N$, let $p^*$ satisfy $1/p^* = 1/p - 1/N$, and let $p \le q \le p^*$. For every
$u \in W^{1,p}(\mathbb{R}^N)$,
$$\|u\|_q \le (1 + C N) \|u\|,$$
where $C$ is `SobolevEuclidean.gnsConst N p`. This is the bound of Corollary 9.10 of
[brezis2011functional].

The proof combines the interpolation inequality between $p$ and $p^*$ with Theorem 9.9. -/
theorem SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p')
    (u : SobolevEuclidean N 1 p ⊤) :
    eLpNorm (fn u) (q : ℝ≥0∞) volume
      ≤ ENNReal.ofReal ((1 + SobolevEuclidean.gnsConst N p * N) * ‖u‖) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    have : (1 : ℝ≥0∞) ≤ p := Fact.out
    exact (zero_lt_one.trans_le this).ne'
  calc eLpNorm (fn u) (q : ℝ≥0∞) volume
      ≤ eLpNorm (fn u) p volume + eLpNorm (fn u) (p' : ℝ≥0∞) volume :=
        eLpNorm_le_eLpNorm_add_eLpNorm_of_le_of_le
          (SobolevEuclidean.memLp_fn u).aestronglyMeasurable hp0 (by exact_mod_cast hpq)
          (by exact_mod_cast hqp')
    _ ≤ ENNReal.ofReal ‖u‖ + ENNReal.ofReal (SobolevEuclidean.gnsConst N p * N * ‖u‖) :=
        add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
          (SobolevEuclidean.eLpNorm_fn_le_norm_of_eq hpN hp' u)
    _ = ENNReal.ofReal ((1 + SobolevEuclidean.gnsConst N p * N) * ‖u‖) := by
        rw [← ENNReal.ofReal_add (norm_nonneg _) (by positivity)]
        congr 1
        ring

/-- Let $1 \le p < N$, let $p^*$ satisfy $1/p^* = 1/p - 1/N$, and let $p \le q \le p^*$. Then
$W^{1,p}(\mathbb{R}^N) \subseteq L^q(\mathbb{R}^N)$: for every $u \in W^{1,p}(\mathbb{R}^N)$,
the function `SobolevMultiIndex.fn u` lies in $L^q(\mathbb{R}^N)$. This is the inclusion of
Corollary 9.10 of [brezis2011functional]. -/
theorem SobolevEuclidean.memLp_fn_of_le_of_le (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (hpq : p ≤ q) (hqp' : q ≤ p') (u : SobolevEuclidean N 1 p ⊤) :
    MemLp (fn u) (q : ℝ≥0∞) volume :=
  memLp_iff.2 ((SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' u).trans_lt
    ENNReal.ofReal_lt_top)

/-- Let $1 \le p < N$, let $p^*$ satisfy $1/p^* = 1/p - 1/N$, and let $p \le q \le p^*$. Then
$W^{1,p}(\mathbb{R}^N) \hookrightarrow L^q(\mathbb{R}^N)$ is a continuous embedding along
`SobolevMultiIndex.toLpₗ`. This is Corollary 9.10 of [brezis2011functional]. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_le_of_le [Fact (1 ≤ (q : ℝ≥0∞))]
    (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using
          SobolevEuclidean.memLp_fn_of_le_of_le hpN hp' hpq hqp' u) := by
  refine isContinuousEmbedding_toLpₗ _ (C := 1 + SobolevEuclidean.gnsConst N p * N) fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (show (0 : ℝ) ≤ (1 + SobolevEuclidean.gnsConst N p * N) * ‖u‖ by positivity)]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  exact (eLpNorm_restrict_coe_top (fn u) (q : ℝ≥0∞)).trans_le
    (SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' u)

end TypedGNSLe

/-!
### Morrey's estimate for $C^1$ functions

This is the analytic core of Theorem 9.12 of [brezis2011functional], on balls instead of the cubes
of the source. For $x$ in a closed ball $B$ of radius $r$ and $u \in C^1$,
$$\int_B |u(z) - u(x)| \, dz \le \frac{2r}{1 - N/p} \mu(B)^{1 - 1/p} \|\nabla u\|_{L^p(B)}.$$
The proof uses the segment bound $|u(z) - u(x)| \le \|z - x\| \int_0^1 |\nabla u(x + t(z - x))| \,
dt$, Fubini's theorem, the homothety $z \mapsto x + t(z - x)$ of ratio $t$, which maps $B$ into
itself and scales the measure by $t^N$, and Hölder's inequality on the image.
-/

section MorreyC1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The **segment bound**. Let $E$ be a real normed space, let $F$ be a real Banach space, and let
$u : E \to F$ be $C^1$. For all $x, z \in E$,
$$\|u(z) - u(x)\| \le \|z - x\| \int_0^1 \|\nabla u(x + t(z - x))\| \, dt.$$
This is the inequality (26) of the proof of Theorem 9.12 of [brezis2011functional].

The integral is a Lebesgue integral over $(0, 1]$ of the operator norm. -/
theorem ContDiff.enorm_sub_le_enorm_mul_lintegral_fderiv (hu : ContDiff ℝ 1 u) (x z : E) :
    ‖u z - u x‖ₑ ≤ ‖z - x‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • (z - x))‖ₑ := by
  have hd : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t ↦ u (x + t • (z - x)))
      (fderiv ℝ u (x + t • (z - x)) (z - x)) t := fun t ↦ by
    have := (hd (x + t • (z - x))).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (z - x)).const_add x)
    simpa [Function.comp_def] using this
  have hcont : Continuous fun t : ℝ ↦ fderiv ℝ u (x + t • (z - x)) (z - x) := by
    have : Continuous fun t : ℝ ↦ fderiv ℝ u (x + t • (z - x)) :=
      (hu.continuous_fderiv one_ne_zero).comp (by fun_prop)
    exact this.clm_apply continuous_const
  have hFTC : u z - u x = ∫ t in (0 : ℝ)..1, fderiv ℝ u (x + t • (z - x)) (z - x) := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
      (hcont.intervalIntegrable 0 1)
    simpa using this.symm
  rw [hFTC, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  refine lintegral_mono fun t ↦ ?_
  rw [mul_comm]
  exact ContinuousLinearMap.le_opENorm _ _

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Let $E$ be a real normed space. The homothety of centre $x$ and ratio $t \neq 0$,
$z \mapsto x + t(z - x)$, is injective. -/
theorem AffineMap.homothety_injective_of_ne_zero (x : E) {t : ℝ} (ht : t ≠ 0) :
    Function.Injective (AffineMap.homothety x t) :=
  AffineMap.homothety_injective x ht

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space with its Borel $\sigma$-algebra. The image of a measurable set
under the homothety of centre $x$ and ratio $t \neq 0$ is measurable. -/
theorem MeasurableSet.image_homothety {s : Set E} (hs : MeasurableSet s) (x : E) {t : ℝ}
    (ht : t ≠ 0) : MeasurableSet (AffineMap.homothety x t '' s) := by
  have h : AffineMap.homothety x t '' s = AffineMap.homothety x t⁻¹ ⁻¹' s := by
    refine congrFun (Set.image_eq_preimage_of_inverse (f := ⇑(AffineMap.homothety x t))
      (g := ⇑(AffineMap.homothety x t⁻¹)) (fun z ↦ ?_) fun z ↦ ?_) s
    · rw [← AffineMap.homothety_mul_apply, inv_mul_cancel₀ ht, AffineMap.homothety_one,
        AffineMap.id_apply]
    · rw [← AffineMap.homothety_mul_apply, mul_inv_cancel₀ ht, AffineMap.homothety_one,
        AffineMap.id_apply]
  rw [h]
  exact hs.preimage (AffineMap.homothety_continuous x t⁻¹).measurable

/-- **A Haar measure under a homothety.** Let $E$ be a real normed space of finite dimension $N$
with an additive Haar measure $\mu$. The pushforward of $\mu$ by the homothety of centre $x$ and
ratio $t \neq 0$ is $|t^N|^{-1} \mu$. -/
theorem MeasureTheory.Measure.map_homothety (x : E) {t : ℝ} (ht : t ≠ 0) :
    μ.map (AffineMap.homothety x t) = ENNReal.ofReal |(t ^ finrank ℝ E)⁻¹| • μ := by
  have hφ : (AffineMap.homothety x t : E → E)
      = (fun y ↦ y + x) ∘ (fun y ↦ t • y) ∘ fun z ↦ z + -x := by
    funext z
    simp [AffineMap.homothety_apply, sub_eq_add_neg]
  rw [hφ, ← Measure.map_map (measurable_add_const x)
    ((measurable_const_smul t).comp (measurable_add_const (-x))),
    ← Measure.map_map (measurable_const_smul t) (measurable_add_const (-x)),
    map_add_right_eq_self μ (-x), Measure.map_addHaar_smul μ ht,
    Measure.map_smul _ (measurable_add_const x).aemeasurable, map_add_right_eq_self μ x]

/-- **Change of variables under a homothety.** Let $E$ be a real normed space of finite dimension
$N$ with an additive Haar measure $\mu$. Let $G : E \to [0, \infty]$ be measurable, let
$t \neq 0$, and let $s \subseteq E$ be measurable. Then
$$\int_s G(x + t(z - x)) \, d\mu(z) = |t^N|^{-1} \int_{x + t(s - x)} G(y) \, d\mu(y).$$
This is the substitution $y = tx$ of the proof of Theorem 9.12 of [brezis2011functional]. -/
theorem MeasureTheory.setLIntegral_comp_homothety {G : E → ℝ≥0∞} (hG : Measurable G) (x : E)
    {t : ℝ} (ht : t ≠ 0) {s : Set E} (hs : MeasurableSet s) :
    ∫⁻ z in s, G (AffineMap.homothety x t z) ∂μ
      = ENNReal.ofReal |(t ^ finrank ℝ E)⁻¹| * ∫⁻ y in AffineMap.homothety x t '' s, G y ∂μ := by
  have hinj := AffineMap.homothety_injective_of_ne_zero x ht
  calc ∫⁻ z in s, G (AffineMap.homothety x t z) ∂μ
      = ∫⁻ z in AffineMap.homothety x t ⁻¹' (AffineMap.homothety x t '' s),
          G (AffineMap.homothety x t z) ∂μ := by rw [preimage_image_eq _ hinj]
    _ = ∫⁻ y in AffineMap.homothety x t '' s, G y ∂(μ.map (AffineMap.homothety x t)) :=
        (setLIntegral_map (hs.image_homothety x ht) hG
          (AffineMap.homothety_continuous x t).measurable).symm
    _ = ENNReal.ofReal |(t ^ finrank ℝ E)⁻¹| * ∫⁻ y in AffineMap.homothety x t '' s, G y ∂μ := by
        rw [Measure.map_homothety x ht, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Let $s$ be a convex subset of a real normed space, let $x \in s$, and let $t \in [0, 1]$. The
homothety of centre $x$ and ratio $t$ maps $s$ into itself. -/
theorem Convex.image_homothety_subset {s : Set E} (hs : Convex ℝ s) {x : E} (hx : x ∈ s) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : AffineMap.homothety x t '' s ⊆ s := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  rw [add_comm]
  exact hs.add_smul_sub_mem hx hz ht

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedSpace ℝ F] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- **Hölder's inequality on a subset.** Let $\mu$ be a measure, let $g$ be almost everywhere
strongly measurable, let $1 \le p < \infty$, and let $S \subseteq B$. Then
$$\int_S \|g\| \, d\mu \le \|g\|_{L^p(B)} \, \mu(S)^{1 - 1/p}.$$
-/
theorem MeasureTheory.lintegral_enorm_le_eLpNorm_mul_measure_rpow {g : E → F}
    (hg : AEStronglyMeasurable g μ) {p : ℝ≥0} (hp : 1 ≤ p) {S B : Set E} (hSB : S ⊆ B) :
    ∫⁻ y in S, ‖g y‖ₑ ∂μ
      ≤ eLpNorm g p (μ.restrict B) * μ S ^ (1 - 1 / (p : ℝ)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  rw [← eLpNorm_one_eq_lintegral_enorm (hg.restrict)]
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hg.restrict).trans ?_
  rw [Measure.restrict_apply_univ]
  have h : 1 / (1 : ℝ≥0∞).toReal - 1 / (p : ℝ≥0∞).toReal = 1 - 1 / (p : ℝ) := by simp
  rw [h]
  exact mul_le_mul' (eLpNorm_mono_measure _ (Measure.restrict_mono hSB le_rfl)) le_rfl

/-- Let $N$ be a natural number and $p$ a real number with $N < p$. Then
$$\int_0^1 t^{-N/p} \, dt = \frac{1}{1 - N/p},$$
as a Lebesgue integral over $(0, 1]$. -/
theorem MeasureTheory.lintegral_Ioc_ofReal_rpow_neg_div {N : ℕ} {p : ℝ} (hp : N < p) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(N / p)))
      = ENNReal.ofReal (1 / (1 - N / p)) := by
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hexp : -1 < -(N / p) := by
    rw [neg_lt_neg_iff, div_lt_one hp0]
    exact hp
  have hint : IntervalIntegrable (fun t : ℝ ↦ t ^ (-(N / p))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hexp
  rw [← ofReal_integral_eq_lintegral_ofReal hint.1 (ae_restrict_of_forall_mem measurableSet_Ioc
    fun t ht ↦ Real.rpow_nonneg ht.1.le _), ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hexp)]
  congr 1
  have h1 : -(N / p) + 1 = 1 - N / p := by ring
  rw [h1, Real.one_rpow, Real.zero_rpow (sub_pos.2 ((div_lt_one hp0).2 hp)).ne', sub_zero, one_div]

/-- For real $t > 0$, a natural number $N$ and a real $p \neq 0$,
$$(t^N)^{-1} (t^N)^{1 - 1/p} = t^{-N/p}.$$
-/
theorem Real.inv_pow_mul_pow_rpow_eq_rpow_neg_div {t : ℝ} (ht : 0 < t) (N : ℕ) {p : ℝ}
    (hp : p ≠ 0) : (t ^ N)⁻¹ * (t ^ N) ^ (1 - 1 / p) = t ^ (-(N / p)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1
  field_simp
  ring

/-- **Morrey's mean estimate on a ball, $C^1$ case.** Let $E$ be a real normed space of finite
dimension $N$ with an additive Haar measure $\mu$, let $F$ be a real Banach space, and let
$u : E \to F$ be $C^1$. Let $1 \le p < \infty$ with $N < p$, let $B$ be the closed ball of
centre $c$ and radius $r > 0$, and let $x \in B$. Then
$$\int_B \|u(z) - u(x)\| \, d\mu(z) \le \frac{2r}{1 - N/p} \, \mu(B)^{1 - 1/p} \, \|\nabla
  u\|_{L^p(B)}.$$
This is the estimate (27) of the proof of Theorem 9.12 of [brezis2011functional], with a ball
instead of a cube.

The source bounds the mean value $|\bar u - u(x)|$ over the cube. Here the integral of
$\|u(z) - u(x)\|$ is bounded instead, because the later proofs do not need the mean value. -/
theorem ContDiff.lintegral_enorm_sub_le_of_mem_closedBall (hu : ContDiff ℝ 1 u) {p : ℝ≥0}
    (hp1 : 1 ≤ p) (hp : finrank ℝ E < p) {c x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ closedBall c r) :
    ∫⁻ z in closedBall c r, ‖u z - u x‖ₑ ∂μ
      ≤ ENNReal.ofReal (2 * r / (1 - finrank ℝ E / p)) * (μ (closedBall c r) ^ (1 - 1 / (p : ℝ))
        * eLpNorm (fderiv ℝ u) p (μ.restrict (closedBall c r))) := by
  set N := finrank ℝ E with hN
  set B := closedBall c r with hB
  set G : E → ℝ≥0∞ := fun y ↦ ‖fderiv ℝ u y‖ₑ with hGdef
  have hGm : Measurable G := (hu.continuous_fderiv one_ne_zero).enorm.measurable
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hexp : (0 : ℝ) ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp0]
    exact_mod_cast hp1
  have hBm : MeasurableSet B := measurableSet_closedBall
  -- Step 1: the segment bound, integrated over the ball
  have h1 : ∫⁻ z in B, ‖u z - u x‖ₑ ∂μ ≤ ENNReal.ofReal (2 * r)
      * ∫⁻ z in B, (∫⁻ t in Ioc (0 : ℝ) 1, G (AffineMap.homothety x t z)) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ((ae_restrict_iff' hBm).2 (Eventually.of_forall fun z hz ↦ ?_))
    refine (hu.enorm_sub_le_enorm_mul_lintegral_fderiv x z).trans (mul_le_mul' ?_ (le_of_eq ?_))
    · rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖z - x‖ ≤ ‖z - c‖ + ‖c - x‖ := norm_sub_le_norm_sub_add_norm_sub z c x
        _ ≤ r + r := add_le_add (mem_closedBall_iff_norm.1 hz)
          (by rw [norm_sub_rev]; exact mem_closedBall_iff_norm.1 hx)
        _ = 2 * r := by ring
    · refine setLIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
      simp [hGdef, AffineMap.homothety_apply, add_comm]
  -- Step 2: Fubini
  have h2 : ∫⁻ z in B, (∫⁻ t in Ioc (0 : ℝ) 1, G (AffineMap.homothety x t z)) ∂μ
      = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in B, G (AffineMap.homothety x t z) ∂μ := by
    refine lintegral_lintegral_swap (f := fun z (t : ℝ) ↦ G (AffineMap.homothety x t z)) ?_
    have hc : Continuous (Function.uncurry fun z (t : ℝ) ↦ AffineMap.homothety x t z) := by
      simp only [Function.uncurry_def, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      fun_prop
    exact (hGm.comp hc.measurable).aemeasurable
  -- Step 3: for each `t ∈ (0, 1]`, change variables and apply Hölder's inequality
  have h3 : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ z in B, G (AffineMap.homothety x t z) ∂μ
      ≤ ENNReal.ofReal (t ^ (-(N / (p : ℝ))))
        * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B)) := by
    intro t ht
    rw [setLIntegral_comp_homothety hGm x ht.1.ne' hBm]
    have himg : AffineMap.homothety x t '' B ⊆ B :=
      (convex_closedBall c r).image_homothety_subset hx ⟨ht.1.le, ht.2⟩
    have hmeas : μ (AffineMap.homothety x t '' B) = ENNReal.ofReal (t ^ N) * μ B := by
      rw [Measure.addHaar_image_homothety, abs_of_nonneg (pow_nonneg ht.1.le _)]
    calc ENNReal.ofReal |(t ^ N)⁻¹| * ∫⁻ y in AffineMap.homothety x t '' B, G y ∂μ
        ≤ ENNReal.ofReal |(t ^ N)⁻¹| * (eLpNorm (fderiv ℝ u) p (μ.restrict B)
            * μ (AffineMap.homothety x t '' B) ^ (1 - 1 / (p : ℝ))) :=
          mul_le_mul' le_rfl (lintegral_enorm_le_eLpNorm_mul_measure_rpow
            (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable hp1 himg)
      _ = ENNReal.ofReal (t ^ (-(N / (p : ℝ))))
            * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B)) := by
          rw [hmeas, ENNReal.mul_rpow_of_nonneg _ _ hexp,
            abs_of_nonneg (inv_nonneg.2 (pow_nonneg ht.1.le _)),
            ENNReal.ofReal_rpow_of_nonneg (pow_nonneg ht.1.le _) hexp, mul_comm (eLpNorm _ _ _),
            mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg ht.1.le _)),
            Real.inv_pow_mul_pow_rpow_eq_rpow_neg_div ht.1 N hp0.ne']
  -- Step 4: integrate in `t`
  have hm : Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ (-(N / (p : ℝ)))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  calc ∫⁻ z in B, ‖u z - u x‖ₑ ∂μ
      ≤ ENNReal.ofReal (2 * r)
          * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in B, G (AffineMap.homothety x t z) ∂μ := by
        rw [← h2]
        exact h1
    _ ≤ ENNReal.ofReal (2 * r) * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(N / (p : ℝ))))
          * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B)) :=
        mul_le_mul' le_rfl (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall h3)))
    _ = ENNReal.ofReal (2 * r) * (ENNReal.ofReal (1 / (1 - N / p))
          * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B))) := by
        rw [lintegral_mul_const _ hm, lintegral_Ioc_ofReal_rpow_neg_div (N := N) (p := (p : ℝ)) hp]
    _ = ENNReal.ofReal (2 * r / (1 - N / p))
          * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_one_div]

variable (μ) in
/-- The **constant of Morrey's inequality**. For a measure $\mu$ on a real normed space $E$ of
finite dimension $N$, and an exponent $p > N$,
$$C(p, N) = \frac{4}{1 - N/p} \, \mu(B(0,1))^{-1/p},$$
where $B(0,1)$ is the open unit ball. With this constant, $\|u(x) - u(y)\| \le C \|x - y\|^{1 -
N/p} \|\nabla u\|_p$ for $C^1$ functions $u$ (`ContDiff.enorm_sub_le_of_lt`).

The constant of [brezis2011functional] is $2 \cdot 2^{1 - N/p} / (1 - N/p)$, for cubes; balls
give this constant. The factor $4/(1 - N/p)$ is a real number converted to $[0, \infty]$, so it
is $0$ when $1 - N/p \le 0$. The constant is finite (`MeasureTheory.morreyConst_ne_top`). -/
def MeasureTheory.morreyConst (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 / (1 - finrank ℝ E / p)) * μ (ball (0 : E) 1) ^ (-(1 / p))

variable (μ) in
/-- The **constant of the sup bound of Morrey's theorem**. For a measure $\mu$ on a real normed
space $E$ of finite dimension $N$, and an exponent $p > N$,
$$C'(p, N) = \frac{2}{1 - N/p} \, \mu(B(0,1))^{-1/p},$$
where $B(0,1)$ is the open unit ball. With this constant,
$\|u(x)\| \le C' (\|u\|_p + \|\nabla u\|_p)$ for $C^1$ functions $u$
(`ContDiff.enorm_le_of_lt`).

The factor $2/(1 - N/p)$ is a real number converted to $[0, \infty]$, so it is $0$ when
$1 - N/p \le 0$. The constant is finite (`MeasureTheory.morreySupConst_ne_top`). -/
def MeasureTheory.morreySupConst (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 / (1 - finrank ℝ E / p)) * μ (ball (0 : E) 1) ^ (-(1 / p))

variable (μ) in
omit [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- For an additive Haar measure $\mu$ on a finite-dimensional real normed space and every real $p$,
the constant `MeasureTheory.morreyConst μ p` of Morrey's inequality is finite. -/
theorem MeasureTheory.morreyConst_ne_top (p : ℝ) : morreyConst μ p ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg' (measure_ball_pos μ 0 one_pos) measure_ball_lt_top.ne)

variable (μ) in
omit [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- For an additive Haar measure $\mu$ on a finite-dimensional real normed space and every real $p$,
the constant `MeasureTheory.morreySupConst μ p` of the sup bound of Morrey's theorem is finite. -/
theorem MeasureTheory.morreySupConst_ne_top (p : ℝ) : morreySupConst μ p ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg' (measure_ball_pos μ 0 one_pos) measure_ball_lt_top.ne)

omit [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Let $\mu$ be an additive Haar measure on a finite-dimensional real normed space, let $B$ be a
closed ball of radius $r > 0$, and let $p$ be real. Then
$$\frac{\mu(B)^{1 - 1/p}}{\mu(B)} = \mu(B)^{-1/p}.$$
-/
theorem MeasureTheory.Measure.closedBall_rpow_div_self {x : E} {r : ℝ} (hr : 0 < r) (p : ℝ) :
    μ (closedBall x r) ^ (1 - 1 / p) / μ (closedBall x r) = μ (closedBall x r) ^ (-(1 / p)) := by
  have h0 : μ (closedBall x r) ≠ 0 := (measure_closedBall_pos μ x hr).ne'
  have ht : μ (closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [div_eq_mul_inv, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ h0 ht]
  congr 1
  ring

/-- **Morrey's inequality for a $C^1$ function.** Let $E$ be a real normed space of finite dimension
$N$ with an additive Haar measure $\mu$, let $F$ be a real Banach space, and let $u : E \to F$
be $C^1$. Let $1 \le p < \infty$ with $N < p$. For all $x, y \in E$,
$$\|u(x) - u(y)\| \le C(p, N) \, \|x - y\|^{1 - N/p} \, \|\nabla u\|_{L^p(B)},$$
where $B$ is the closed ball of centre $x$ and radius $\|x - y\|$ and $C(p, N)$ is
`MeasureTheory.morreyConst μ p`. This is the inequality (25) of the proof of Theorem 9.12 of
[brezis2011functional], which the source states for $u \in C_c^1$; here $u$ need not have
compact support.

Both points lie in $B$, and $\|u(x) - u(y)\| \le \|u(z) - u(x)\| + \|u(z) - u(y)\|$ for every
$z \in B$. Integration over $B$ reduces the bound to
`ContDiff.lintegral_enorm_sub_le_of_mem_closedBall`, applied twice. -/
theorem ContDiff.enorm_sub_le_of_lt (hu : ContDiff ℝ 1 u) {p : ℝ≥0} (hp1 : 1 ≤ p)
    (hp : finrank ℝ E < p) (x y : E) :
    ‖u x - u y‖ₑ ≤ morreyConst μ p * ENNReal.ofReal (‖x - y‖ ^ (1 - finrank ℝ E / (p : ℝ)))
      * eLpNorm (fderiv ℝ u) p (μ.restrict (closedBall x ‖x - y‖)) := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  set N := finrank ℝ E with hN
  set r := ‖x - y‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  set B := closedBall x r with hB
  have hxB : x ∈ B := mem_closedBall_self hr0.le
  have hyB : y ∈ B := by
    rw [hB, mem_closedBall, dist_eq_norm, norm_sub_rev]
  have hμB0 : μ B ≠ 0 := (measure_closedBall_pos μ x hr0).ne'
  have hμBt : μ B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hpN : (0 : ℝ) < 1 - N / p := sub_pos.2 ((div_lt_one hp0).2 hp)
  have hcont : Continuous u := hu.continuous
  -- the triangle inequality integrated over the ball
  have key : ‖u x - u y‖ₑ * μ B ≤ ∫⁻ z in B, ‖u z - u x‖ₑ ∂μ + ∫⁻ z in B, ‖u z - u y‖ₑ ∂μ := by
    rw [← lintegral_add_left (f := fun z ↦ ‖u z - u x‖ₑ)
      (hcont.sub continuous_const).enorm.measurable, ← setLIntegral_const]
    refine lintegral_mono fun z ↦ ?_
    calc ‖u x - u y‖ₑ = ‖(u z - u y) - (u z - u x)‖ₑ := by congr 1; abel
      _ ≤ ‖u z - u y‖ₑ + ‖u z - u x‖ₑ := enorm_sub_le
      _ = ‖u z - u x‖ₑ + ‖u z - u y‖ₑ := add_comm _ _
  have hx' := hu.lintegral_enorm_sub_le_of_mem_closedBall (μ := μ) hp1 hp hr0 hxB
  have hy' := hu.lintegral_enorm_sub_le_of_mem_closedBall (μ := μ) hp1 hp hr0 hyB
  rw [← hB] at hx' hy'
  set D := eLpNorm (fderiv ℝ u) p (μ.restrict B) with hD
  have h2 : ‖u x - u y‖ₑ * μ B
      ≤ ENNReal.ofReal (4 * r / (1 - N / p)) * (μ B ^ (1 - 1 / (p : ℝ)) * D) := by
    refine (key.trans (add_le_add hx' hy')).trans (le_of_eq ?_)
    rw [← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two]
    congr 2
    ring
  have h3 : ‖u x - u y‖ₑ
      ≤ ENNReal.ofReal (4 * r / (1 - N / p)) * (μ B ^ (1 - 1 / (p : ℝ)) * D) / μ B :=
    (ENNReal.le_div_iff_mul_le (Or.inl hμB0) (Or.inl hμBt)).2 h2
  have h4 : ENNReal.ofReal (4 * r / (1 - N / p)) * (μ B ^ (1 - 1 / (p : ℝ)) * D) / μ B
      = ENNReal.ofReal (4 * r / (1 - N / p)) * (μ B ^ (-(1 / (p : ℝ))) * D) := by
    rw [← Measure.closedBall_rpow_div_self (μ := μ) hr0, ← hB, ENNReal.div_eq_inv_mul,
      ENNReal.div_eq_inv_mul]
    ring
  refine (h3.trans_eq h4).trans (le_of_eq ?_)
  -- the measure of the ball, and the powers of `r`
  have hμB : μ B = ENNReal.ofReal (r ^ N) * μ (ball 0 1) := Measure.addHaar_closedBall μ x hr0.le
  have hrN : ENNReal.ofReal (r ^ N) ^ (-(1 / (p : ℝ))) = ENNReal.ofReal (r ^ (-(N / (p : ℝ)))) := by
    rw [ENNReal.ofReal_rpow_of_pos (pow_pos hr0 _), ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    congr 2
    ring
  have hr' : 4 * r / (1 - N / p) * r ^ (-(N / (p : ℝ)))
      = 4 / (1 - N / p) * r ^ (1 - N / (p : ℝ)) := by
    rw [show (1 - N / (p : ℝ)) = 1 + -(N / (p : ℝ)) by ring, Real.rpow_add hr0, Real.rpow_one]
    ring
  rw [morreyConst, hμB, ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne,
    hrN, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hr',
    ENNReal.ofReal_mul (by positivity)]
  ring

/-- **The sup bound for a $C^1$ function.** Let $E$ be a real normed space of finite dimension $N$
with an additive Haar measure $\mu$, let $F$ be a real Banach space, and let $u : E \to F$ be
$C^1$. Let $1 \le p < \infty$ with $N < p$. For every $x \in E$,
$$\|u(x)\| \le C'(p, N) \left( \|u\|_p + \|\nabla u\|_p \right),$$
where $C'(p, N)$ is `MeasureTheory.morreySupConst μ p`. This is the inequality (24) of the proof
of Theorem 9.12 of [brezis2011functional], which the source states for $u \in C_c^1$; here $u$
need not have compact support.

On the closed unit ball $B$ about $x$, $\|u(x)\| \le \|u(z) - u(x)\| + \|u(z)\|$ for every
$z \in B$. After integration over $B$, `ContDiff.lintegral_enorm_sub_le_of_mem_closedBall`
bounds the first term and Hölder's inequality bounds the second. -/
theorem ContDiff.enorm_le_of_lt (hu : ContDiff ℝ 1 u) {p : ℝ≥0} (hp1 : 1 ≤ p)
    (hp : finrank ℝ E < p) (x : E) :
    ‖u x‖ₑ ≤ morreySupConst μ p * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) := by
  set N := finrank ℝ E with hN
  set B := closedBall x 1 with hB
  have hxB : x ∈ B := mem_closedBall_self zero_le_one
  have hμB0 : μ B ≠ 0 := (measure_closedBall_pos μ x one_pos).ne'
  have hμBt : μ B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hpN : (0 : ℝ) < 1 - N / p := sub_pos.2 ((div_lt_one hp0).2 hp)
  have hcont : Continuous u := hu.continuous
  have key : ‖u x‖ₑ * μ B ≤ ∫⁻ z in B, ‖u z - u x‖ₑ ∂μ + ∫⁻ z in B, ‖u z‖ₑ ∂μ := by
    rw [← lintegral_add_left (f := fun z ↦ ‖u z - u x‖ₑ)
      (hcont.sub continuous_const).enorm.measurable, ← setLIntegral_const]
    refine lintegral_mono fun z ↦ ?_
    calc ‖u x‖ₑ = ‖u z - (u z - u x)‖ₑ := by congr 1; abel
      _ ≤ ‖u z‖ₑ + ‖u z - u x‖ₑ := enorm_sub_le
      _ = ‖u z - u x‖ₑ + ‖u z‖ₑ := add_comm _ _
  have h1 := hu.lintegral_enorm_sub_le_of_mem_closedBall (μ := μ) hp1 hp one_pos hxB
  rw [← hB] at h1
  have h2 : ∫⁻ z in B, ‖u z‖ₑ ∂μ ≤ eLpNorm u p (μ.restrict B) * μ B ^ (1 - 1 / (p : ℝ)) :=
    lintegral_enorm_le_eLpNorm_mul_measure_rpow hcont.aestronglyMeasurable hp1 subset_rfl
  have hC : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 / (1 - N / p)) := by
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ((le_div_iff₀ hpN).2 ?_)
    have : (0 : ℝ) ≤ N / p := by positivity
    linarith
  have hsum : ‖u x‖ₑ * μ B ≤ ENNReal.ofReal (2 / (1 - N / p)) * μ B ^ (1 - 1 / (p : ℝ))
      * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) := by
    set C := ENNReal.ofReal (2 / (1 - N / p)) with hCdef
    calc ‖u x‖ₑ * μ B ≤ (∫⁻ z in B, ‖u z - u x‖ₑ ∂μ) + ∫⁻ z in B, ‖u z‖ₑ ∂μ := key
      _ ≤ ENNReal.ofReal (2 * 1 / (1 - N / p))
            * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p (μ.restrict B))
          + eLpNorm u p (μ.restrict B) * μ B ^ (1 - 1 / (p : ℝ)) := add_le_add h1 h2
      _ ≤ C * μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm (fderiv ℝ u) p μ
          + C * μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm u p μ := by
          refine add_le_add ?_ ?_
          · rw [mul_one, mul_assoc]
            exact mul_le_mul' le_rfl
              (mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self))
          · calc eLpNorm u p (μ.restrict B) * μ B ^ (1 - 1 / (p : ℝ))
                ≤ 1 * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm u p μ) := by
                  rw [one_mul, mul_comm]
                  exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)
              _ ≤ C * (μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm u p μ) := mul_le_mul' hC le_rfl
              _ = C * μ B ^ (1 - 1 / (p : ℝ)) * eLpNorm u p μ := by ring
      _ = C * μ B ^ (1 - 1 / (p : ℝ)) * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) := by ring
  have h3 : ‖u x‖ₑ ≤ ENNReal.ofReal (2 / (1 - N / p)) * μ B ^ (1 - 1 / (p : ℝ))
      * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) / μ B :=
    (ENNReal.le_div_iff_mul_le (Or.inl hμB0) (Or.inl hμBt)).2 hsum
  have h4 : ENNReal.ofReal (2 / (1 - N / p)) * μ B ^ (1 - 1 / (p : ℝ))
      * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) / μ B
      = ENNReal.ofReal (2 / (1 - N / p)) * (μ B ^ (-(1 / (p : ℝ)))
        * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ)) := by
    rw [← Measure.closedBall_rpow_div_self (μ := μ) one_pos, ← hB, ENNReal.div_eq_inv_mul,
      ENNReal.div_eq_inv_mul]
    ring
  refine (h3.trans_eq h4).trans (le_of_eq ?_)
  have hμB : μ B = μ (ball 0 1) := by
    rw [hB, Measure.addHaar_closedBall μ x zero_le_one, one_pow, ENNReal.ofReal_one, one_mul]
  rw [morreySupConst, hμB, mul_assoc]

end MorreyC1

/-!
### Morrey's theorem on $W^{1,p}(\mathbb{R}^N)$, $N < p < \infty$

This is Theorem 9.12 of [brezis2011functional].
-/

section ENNRealLimits

/-- Let $a, b, K \in [0, \infty]$ with $K < \infty$. If $a \le K (b + \delta)$ for every
$\delta > 0$, then $a \le K b$. -/
theorem ENNReal.le_mul_of_forall_pos_le_mul_add {a b K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * (b + δ)) : a ≤ K * b := by
  have hlim : Tendsto (fun δ : ℝ≥0∞ ↦ K * (b + δ)) (𝓝[>] 0) (𝓝 (K * b)) := by
    have : Tendsto (fun δ : ℝ≥0∞ ↦ b + δ) (𝓝[>] 0) (𝓝 (b + 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.add tendsto_id)
    rw [add_zero] at this
    exact ENNReal.Tendsto.const_mul this (Or.inr hK)
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ ↦ h δ hδ)

/-- Let $1 \le p \le \infty$. For all functions $f$ and $g$ on a measure space with values in a
normed group,
$$\|f\|_p \le \|f - g\|_p + \|g\|_p.$$
-/
theorem MeasureTheory.eLpNorm_le_eLpNorm_sub_add {α G : Type*} [MeasurableSpace α] {ν : Measure α}
    [NormedAddCommGroup G] {p : ℝ≥0∞} (hp : 1 ≤ p) (f g : α → G) :
    eLpNorm f p ν ≤ eLpNorm (fun x ↦ f x - g x) p ν + eLpNorm g p ν := by
  have hsplit : f = (fun x ↦ f x - g x) + g := by
    funext x
    simp
  conv_lhs => rw [hsplit]
  exact eLpNorm_add_le hp

end ENNRealLimits

section Morrey

open scoped BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {w : E → E →L[ℝ] F}

/-- **Morrey's theorem.** Let $E$ be a real normed space of finite dimension $N$ with an additive
Haar measure $\mu$, and let $F$ be a real Banach space. Let $1 \le p < \infty$ with $N < p$, and
let $f, w \in L^p$, where $w$ is a weak derivative of $f$ on $E$. Then there is a continuous
$\tilde u : E \to F$ with $f = \tilde u$ almost everywhere and, for all $x, y \in E$,
$$\|\tilde u(x) - \tilde u(y)\| \le C \|x - y\|^{1 - N/p} \|w\|_p, \qquad \|\tilde u(x)\| \le C'
  (\|f\|_p + \|w\|_p),$$
and $\tilde u(x) \to 0$ as $x$ leaves every compact set. Here $C$ is
`MeasureTheory.morreyConst μ p` and $C'$ is `MeasureTheory.morreySupConst μ p`. This is Theorem
9.12 of [brezis2011functional], with the inequalities (25) and (24), the continuous
representative of Remark 11 and the decay at infinity of Remark 12.

The proof makes the "standard density argument" of the source explicit. The smooth compactly
supported approximants $u_n \to f$, $\nabla u_n \to w$ in $L^p$ satisfy (24) for their
differences, so they form a Cauchy sequence in the Banach space of bounded continuous functions.
The limit $\tilde u$ is continuous, equals $f$ almost everywhere, satisfies (25) and (24), and
is a uniform limit of compactly supported functions. -/
theorem HasWeakFDerivOn.exists_continuous_holderWith_ae_eq (h : HasWeakFDerivOn f w ⊤ μ)
    {p : ℝ≥0} (hp1 : 1 ≤ p) (hp : finrank ℝ E < p) (hf : MemLp f p μ) (hw : MemLp w p μ) :
    ∃ ũ : E → F, Continuous ũ ∧ f =ᵐ[μ] ũ ∧
      (∀ x y, ‖ũ x - ũ y‖ₑ ≤ morreyConst μ p
        * ENNReal.ofReal (‖x - y‖ ^ (1 - finrank ℝ E / (p : ℝ))) * eLpNorm w p μ) ∧
      (∀ x, ‖ũ x‖ₑ ≤ morreySupConst μ p * (eLpNorm f p μ + eLpNorm w p μ)) ∧
      Tendsto ũ (cocompact E) (𝓝 0) := by
  have hp1' : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp1
  obtain ⟨u, hus, huc, hu0, hu1⟩ :=
    h.exists_seq_contDiff_hasCompactSupport_tendsto_top hp1' ENNReal.coe_ne_top hf hw
  have hu1' : ∀ n, ContDiff ℝ 1 (u n) := fun n ↦ (hus n).of_le (by simp)
  -- the approximants as bounded continuous functions
  choose M hM using fun n ↦ (huc n).exists_bound_of_continuous (hus n).continuous
  let U : ℕ → E →ᵇ F := fun n ↦
    BoundedContinuousFunction.ofNormedAddCommGroup (u n) (hus n).continuous (M n) (hM n)
  have hU : ∀ n x, U n x = u n x := fun n x ↦ rfl
  set C' := morreySupConst μ p with hC'
  have hC't : C' ≠ ⊤ := morreySupConst_ne_top μ p
  -- the sup bound (24) for a difference of two approximants
  have hdiff : ∀ n m x, ‖u n x - u m x‖ₑ ≤ C' * (eLpNorm (u n - u m) p μ
      + eLpNorm (fun x ↦ fderiv ℝ (u n) x - fderiv ℝ (u m) x) p μ) := by
    intro n m x
    have := ((hu1' n).sub (hu1' m)).enorm_le_of_lt (μ := μ) hp1 hp x
    have e : (fderiv ℝ fun x ↦ u n x - u m x) = fun x ↦ fderiv ℝ (u n) x - fderiv ℝ (u m) x := by
      funext y
      exact fderiv_sub ((hu1' n).differentiable one_ne_zero y)
        ((hu1' m).differentiable one_ne_zero y)
    rw [e] at this
    exact this
  -- the approximants are Cauchy in the sup norm
  have hcauchy : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ0, hδ1, hδ⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧ δ < 1 ∧ (C' * (4 * δ)).toReal < ε := by
      have : Tendsto (fun δ : ℝ≥0∞ ↦ (C' * (4 * δ)).toReal) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun δ : ℝ≥0∞ ↦ C' * (4 * δ)) (𝓝[>] 0) (𝓝 (C' * (4 * 0))) :=
          tendsto_nhdsWithin_of_tendsto_nhds
            (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul tendsto_id (Or.inr (by simp)))
              (Or.inr hC't))
        rw [mul_zero, mul_zero] at h1
        exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      have h1 : ∀ᶠ δ : ℝ≥0∞ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
      have h2 : ∀ᶠ δ : ℝ≥0∞ in 𝓝[>] 0, δ < 1 :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
      obtain ⟨δ, hδ, hδε, hδ1⟩ := ((this.eventually (gt_mem_nhds hε)).and (h1.and h2)).exists
      exact ⟨δ, hδε, hδ1, hδ⟩
    have hev0 : ∀ᶠ n in atTop, eLpNorm (u n - f) p μ ≤ δ := ENNReal.tendsto_nhds_zero.1 hu0 δ hδ0
    have hev1 : ∀ᶠ n in atTop, eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p μ ≤ δ :=
      ENNReal.tendsto_nhds_zero.1 hu1 δ hδ0
    obtain ⟨N₀, hN₀⟩ := (hev0.and hev1).exists_forall_of_atTop
    refine ⟨N₀, fun m hm n hn ↦ ?_⟩
    have hbound : dist (U m) (U n) ≤ (C' * (4 * δ)).toReal := by
      refine (BoundedContinuousFunction.dist_le ENNReal.toReal_nonneg).2 fun x ↦ ?_
      rw [hU, hU, dist_eq_norm, ← toReal_enorm]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top hC't
        (ENNReal.mul_ne_top (by simp) hδ1.ne_top)) ((hdiff m n x).trans ?_)
      refine mul_le_mul' le_rfl ?_
      have e1 : eLpNorm (u m - u n) p μ ≤ δ + δ := by
        have : u m - u n = (u m - f) - (u n - f) := by abel
        rw [this]
        exact (eLpNorm_sub_le hp1').trans (add_le_add (hN₀ m hm).1 (hN₀ n hn).1)
      have e2 : eLpNorm (fun x ↦ fderiv ℝ (u m) x - fderiv ℝ (u n) x) p μ ≤ δ + δ := by
        have : (fun x ↦ fderiv ℝ (u m) x - fderiv ℝ (u n) x)
            = (fun x ↦ fderiv ℝ (u m) x - w x) - fun x ↦ fderiv ℝ (u n) x - w x := by
          funext x
          simp
        rw [this]
        exact (eLpNorm_sub_le hp1').trans (add_le_add (hN₀ m hm).2 (hN₀ n hn).2)
      calc eLpNorm (u m - u n) p μ + eLpNorm (fun x ↦ fderiv ℝ (u m) x - fderiv ℝ (u n) x) p μ
          ≤ (δ + δ) + (δ + δ) := add_le_add e1 e2
        _ = 4 * δ := by ring
    exact hbound.trans_lt hδ
  -- the uniform limit
  obtain ⟨Ũ, hŨ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hpt : ∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (Ũ x)) := fun x ↦
    ((continuous_eval_const x).tendsto Ũ).comp hŨ
  refine ⟨Ũ, Ũ.continuous, ?_, ?_, ?_, ?_⟩
  -- it equals `f` almost everywhere
  · have hmeas : TendstoInMeasure μ u atTop f :=
      tendstoInMeasure_of_tendsto_eLpNorm (by exact_mod_cast (zero_lt_one.trans_le hp1).ne') hu0
    obtain ⟨ns, hns_mono, hns⟩ := hmeas.exists_seq_tendsto_ae
    filter_upwards [hns] with x hx
    exact tendsto_nhds_unique hx ((hpt x).comp hns_mono.tendsto_atTop)
  -- the Hölder estimate (25)
  · intro x y
    refine ENNReal.le_mul_of_forall_pos_le_mul_add
      (ENNReal.mul_ne_top (morreyConst_ne_top μ p) ENNReal.ofReal_ne_top) fun δ hδ ↦ ?_
    have hlim : Tendsto (fun n ↦ ‖u n x - u n y‖ₑ) atTop (𝓝 ‖Ũ x - Ũ y‖ₑ) :=
      (continuous_enorm.tendsto _).comp ((hpt x).sub (hpt y))
    refine le_of_tendsto hlim ?_
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hu1 δ hδ] with n hn
    refine ((hu1' n).enorm_sub_le_of_lt (μ := μ) hp1 hp x y).trans (mul_le_mul' le_rfl ?_)
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    refine (eLpNorm_le_eLpNorm_sub_add hp1' _ w).trans ?_
    rw [add_comm]
    exact add_le_add le_rfl hn
  -- the sup bound (24)
  · intro x
    refine ENNReal.le_mul_of_forall_pos_le_mul_add hC't fun δ hδ ↦ ?_
    have hlim : Tendsto (fun n ↦ ‖u n x‖ₑ) atTop (𝓝 ‖Ũ x‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hpt x)
    refine le_of_tendsto hlim ?_
    have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hu0 (δ / 2) hδ2,
      ENNReal.tendsto_nhds_zero.1 hu1 (δ / 2) hδ2] with n hn0 hn1
    refine ((hu1' n).enorm_le_of_lt (μ := μ) hp1 hp x).trans (mul_le_mul' le_rfl ?_)
    calc eLpNorm (u n) p μ + eLpNorm (fderiv ℝ (u n)) p μ
        ≤ (eLpNorm (fun x ↦ u n x - f x) p μ + eLpNorm f p μ)
          + (eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p μ + eLpNorm w p μ) :=
          add_le_add (eLpNorm_le_eLpNorm_sub_add hp1' _ f) (eLpNorm_le_eLpNorm_sub_add hp1' _ w)
      _ ≤ (δ / 2 + eLpNorm f p μ) + (δ / 2 + eLpNorm w p μ) :=
          add_le_add (add_le_add hn0 le_rfl) (add_le_add hn1 le_rfl)
      _ = eLpNorm f p μ + eLpNorm w p μ + δ := by
          rw [add_add_add_comm, ENNReal.add_halves, add_comm]
  -- the decay at infinity (Remark 12)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.1 hŨ ε hε).exists
    refine mem_cocompact.2 ⟨tsupport (u n), huc n, fun x hx ↦ ?_⟩
    have hx0 : u n x = 0 := image_eq_zero_of_notMem_tsupport hx
    change dist ‖Ũ x‖ 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    calc ‖Ũ x‖ = ‖U n x - Ũ x‖ := by rw [hU, hx0, zero_sub, norm_neg]
      _ ≤ dist (U n) Ũ := by rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist x
      _ < ε := hn

end Morrey

/-!
### Morrey's theorem on the space $W^{1,p}(\mathbb{R}^N)$

This part also gives the bounded linear map from $W^{1,p}(\mathbb{R}^N)$ to the bounded continuous
functions.
-/

section TypedMorrey

open scoped BoundedContinuousFunction
open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- **Morrey's theorem on $W^{1,p}(\mathbb{R}^N)$.** Let $1 \le p < \infty$ with $N < p$. Every
$u \in W^{1,p}(\mathbb{R}^N)$ has a continuous representative
$\tilde u : \mathbb{R}^N \to \mathbb{R}$, equal to `SobolevMultiIndex.fn u` almost everywhere,
such that for all $x, y$
$$|\tilde u(x) - \tilde u(y)| \le C \|x - y\|^{1 - N/p} \sum_i \|\partial_i u\|_p, \qquad
  |\tilde u(x)| \le C' (N + 1) \|u\|,$$
and $\tilde u(x) \to 0$ as $\|x\| \to \infty$. Here $C$ and $C'$ are `MeasureTheory.morreyConst`
and `MeasureTheory.morreySupConst` for Lebesgue measure. This is Theorem 9.12 of
[brezis2011functional] with Remarks 11 and 12. -/
theorem SobolevEuclidean.exists_continuous_ae_eq_of_lt (hp : N < p)
    (u : SobolevEuclidean N 1 p ⊤) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧ fn u =ᵐ[volume] ũ ∧
      (∀ x y, ‖ũ x - ũ y‖ₑ ≤ morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p
        * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
        * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖) ∧
      (∀ x, ‖ũ x‖ₑ ≤ morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)
        * ENNReal.ofReal ‖u‖) ∧
      Tendsto ũ (cocompact (EuclideanSpace ℝ (Fin N))) (𝓝 0) := by
  have hp1 : 1 ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hN : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  obtain ⟨w, hw, hwp, hwle⟩ := SobolevEuclidean.exists_hasWeakFDerivOn u
  obtain ⟨ũ, hc, hae, hhold, hsup, hdecay⟩ := hw.exists_continuous_holderWith_ae_eq hp1
    (by rw [hN]; exact_mod_cast hp) (SobolevEuclidean.memLp_fn u) hwp
  refine ⟨ũ, hc, hae, fun x y ↦ ?_, fun x ↦ ?_, hdecay⟩
  · rw [hN] at hhold
    exact (hhold x y).trans (mul_le_mul' le_rfl hwle)
  · refine (hsup x).trans ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    calc eLpNorm (fn u) p volume + eLpNorm w p volume
        ≤ ENNReal.ofReal ‖u‖ + N * ENNReal.ofReal ‖u‖ :=
          add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
            (hwle.trans (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u))
      _ = (N + 1) * ENNReal.ofReal ‖u‖ := by ring

/-- Let $1 \le p$ and $u \in W^{1,p}(\mathbb{R}^N)$. If a function
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ satisfies $|\tilde u(x)| \le C' (N + 1) \|u\|$ in
$[0, \infty]$ for all $x$, where $C'$ is `MeasureTheory.morreySupConst` for Lebesgue measure,
then $|\tilde u(x)| \le c \|u\|$ for all $x$, where $c$ is the real number $C' (N + 1)$. -/
theorem SobolevEuclidean.norm_le_of_enorm_le_morreySupConst
    (u : SobolevEuclidean N 1 p ⊤) {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (h : ∀ x, ‖ũ x‖ₑ ≤ morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)
      * ENNReal.ofReal ‖u‖) (x : EuclideanSpace ℝ (Fin N)) :
    ‖ũ x‖ ≤ (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal
      * ‖u‖ := by
  have hK : morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (morreySupConst_ne_top _ _) (by simp)
  rw [← toReal_enorm, ← ENNReal.toReal_ofReal (norm_nonneg u), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) (h x)

/-- The **continuous representative** of $u \in W^{1,p}(\mathbb{R}^N)$, for $1 \le p < \infty$ with
$N < p$: the function $\tilde u$ of `SobolevEuclidean.exists_continuous_ae_eq_of_lt`, as a
bounded continuous function on $\mathbb{R}^N$.

Two continuous functions that agree almost everywhere agree everywhere, so $\tilde u$ does not
depend on the choice (`SobolevEuclidean.contRep_eq_of_ae_eq`), and $u \mapsto \tilde u$ is
linear (`SobolevEuclidean.toBoundedContinuousMapL`). -/
noncomputable def SobolevEuclidean.contRep (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    EuclideanSpace ℝ (Fin N) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose
    (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.1 _
    (SobolevEuclidean.norm_le_of_enorm_le_morreySupConst u
      (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.2.1)

/-- For $1 \le p < \infty$ with $N < p$ and $u \in W^{1,p}(\mathbb{R}^N)$, the function
`SobolevMultiIndex.fn u` equals the continuous representative `SobolevEuclidean.contRep` of $u$
almost everywhere. -/
theorem SobolevEuclidean.fn_ae_eq_contRep (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    fn u =ᵐ[volume] SobolevEuclidean.contRep hp u :=
  (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.1

/-- **The Hölder estimate for the continuous representative.** Let $1 \le p < \infty$ with $N < p$,
and let $\tilde u$ be the continuous representative of $u \in W^{1,p}(\mathbb{R}^N)$. For all
$x, y$,
$$|\tilde u(x) - \tilde u(y)| \le C \|x - y\|^{1 - N/p} \sum_i \|\partial_i u\|_p,$$
where $C$ is `MeasureTheory.morreyConst` for Lebesgue measure. This is the inequality (25) of
[brezis2011functional], §9.3. -/
theorem SobolevEuclidean.enorm_contRep_sub_le (hp : N < p) (u : SobolevEuclidean N 1 p ⊤)
    (x y : EuclideanSpace ℝ (Fin N)) :
    ‖SobolevEuclidean.contRep hp u x - SobolevEuclidean.contRep hp u y‖ₑ
      ≤ morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p
        * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
        * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ :=
  (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.1 x y

/-- **The sup bound for the continuous representative.** Let $1 \le p < \infty$ with $N < p$, and
let $\tilde u$ be the continuous representative of $u \in W^{1,p}(\mathbb{R}^N)$. For every $x$,
$$|\tilde u(x)| \le C' (N + 1) \|u\|,$$
where $C'$ is `MeasureTheory.morreySupConst` for Lebesgue measure. This is the inequality (24)
of [brezis2011functional], §9.3. -/
theorem SobolevEuclidean.norm_contRep_apply_le (hp : N < p) (u : SobolevEuclidean N 1 p ⊤)
    (x : EuclideanSpace ℝ (Fin N)) :
    ‖SobolevEuclidean.contRep hp u x‖
      ≤ (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal
        * ‖u‖ :=
  SobolevEuclidean.norm_le_of_enorm_le_morreySupConst u
    (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.2.1 x

/-- Let $1 \le p < \infty$ with $N < p$. The continuous representative $\tilde u$ of
$u \in W^{1,p}(\mathbb{R}^N)$ satisfies $\tilde u(x) \to 0$ as $\|x\| \to \infty$. This is
Remark 12 of [brezis2011functional], Chapter 9. -/
theorem SobolevEuclidean.tendsto_contRep_cocompact (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    Tendsto (SobolevEuclidean.contRep hp u) (cocompact (EuclideanSpace ℝ (Fin N))) (𝓝 0) :=
  (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.2.2

/-- Let $1 \le p < \infty$ with $N < p$, and let $u \in W^{1,p}(\mathbb{R}^N)$. A bounded continuous
function $g$ that equals `SobolevMultiIndex.fn u` almost everywhere is the continuous
representative `SobolevEuclidean.contRep` of $u$.

Two continuous functions that agree almost everywhere for Lebesgue measure are equal. -/
theorem SobolevEuclidean.contRep_eq_of_ae_eq (hp : N < p) (u : SobolevEuclidean N 1 p ⊤)
    {g : EuclideanSpace ℝ (Fin N) →ᵇ ℝ} (hg : fn u =ᵐ[volume] g) :
    SobolevEuclidean.contRep hp u = g :=
  BoundedContinuousFunction.ext <| congrFun <| Measure.eq_of_ae_eq (μ := volume)
    ((SobolevEuclidean.fn_ae_eq_contRep hp u).symm.trans hg)
    (SobolevEuclidean.contRep hp u).continuous g.continuous

/-- Let $1 \le p < \infty$ with $N < p$. The sup norm of the continuous representative $\tilde u$ of
$u \in W^{1,p}(\mathbb{R}^N)$ satisfies $\|\tilde u\|_\infty \le C' (N + 1) \|u\|$, where $C'$
is `MeasureTheory.morreySupConst` for Lebesgue measure. -/
theorem SobolevEuclidean.norm_contRep_le (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    ‖SobolevEuclidean.contRep hp u‖
      ≤ (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal
        * ‖u‖ :=
  (BoundedContinuousFunction.norm_le (by positivity)).2
    (SobolevEuclidean.norm_contRep_apply_le hp u)

variable (N p) in
/-- **The map $W^{1,p}(\mathbb{R}^N) \to C_b(\mathbb{R}^N)$.** For $1 \le p < \infty$ with $N < p$,
this is the bounded linear map $u \mapsto \tilde u$ that sends $u$ to its continuous
representative of Morrey's theorem, with $\|\tilde u\|_\infty \le C' (N + 1) \|u\|$.

Theorem 9.12 of [brezis2011functional] reads $W^{1,p}(\mathbb{R}^N) \subset
L^\infty(\mathbb{R}^N)$ along this map. The construction follows
`SobolevIntervalLp.toContinuousMap`. -/
noncomputable def SobolevEuclidean.toBoundedContinuousMapL (hp : N < p) :
    SobolevEuclidean N 1 p ⊤ →L[ℝ] (EuclideanSpace ℝ (Fin N) →ᵇ ℝ) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := SobolevEuclidean.contRep hp
      map_add' := fun u v ↦ SobolevEuclidean.contRep_eq_of_ae_eq hp (u + v) <| by
        refine (eventuallyEq_restrict_coe_top_iff.1 (fn_add u v)).trans ?_
        filter_upwards [SobolevEuclidean.fn_ae_eq_contRep hp u,
          SobolevEuclidean.fn_ae_eq_contRep hp v] with x hu hv
        simp [hu, hv]
      map_smul' := fun c u ↦ SobolevEuclidean.contRep_eq_of_ae_eq hp (c • u) <| by
        refine (eventuallyEq_restrict_coe_top_iff.1 (fn_smul c u)).trans ?_
        filter_upwards [SobolevEuclidean.fn_ae_eq_contRep hp u] with x hu
        simp [hu] }
    ⟨_, SobolevEuclidean.norm_contRep_le hp⟩

/-- For $1 \le p < \infty$ with $N < p$, the map `SobolevEuclidean.toBoundedContinuousMapL` sends
$u$ to its continuous representative `SobolevEuclidean.contRep`. -/
@[simp]
theorem SobolevEuclidean.toBoundedContinuousMapL_apply (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    SobolevEuclidean.toBoundedContinuousMapL N p hp u = SobolevEuclidean.contRep hp u :=
  rfl

/-- For $1 \le p < \infty$ with $N < p$ and $u \in W^{1,p}(\mathbb{R}^N)$, the function
`SobolevMultiIndex.fn u` equals the image of $u$ under
`SobolevEuclidean.toBoundedContinuousMapL` almost everywhere. -/
theorem SobolevEuclidean.fn_ae_eq_toBoundedContinuousMapL (hp : N < p)
    (u : SobolevEuclidean N 1 p ⊤) :
    fn u =ᵐ[volume] SobolevEuclidean.toBoundedContinuousMapL N p hp u :=
  SobolevEuclidean.fn_ae_eq_contRep hp u

/-- Let $1 \le p < \infty$ with $N < p$. The image $\tilde u$ of $u \in W^{1,p}(\mathbb{R}^N)$ under
`SobolevEuclidean.toBoundedContinuousMapL` satisfies $\|\tilde u\|_\infty \le C' (N + 1) \|u\|$,
where $C'$ is `MeasureTheory.morreySupConst` for Lebesgue measure. This is the bound (24) of
Theorem 9.12 of [brezis2011functional]. -/
theorem SobolevEuclidean.norm_toBoundedContinuousMapL_apply_le (hp : N < p)
    (u : SobolevEuclidean N 1 p ⊤) :
    ‖SobolevEuclidean.toBoundedContinuousMapL N p hp u‖
      ≤ (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal
        * ‖u‖ :=
  SobolevEuclidean.norm_contRep_le hp u

/-- For $1 \le p < \infty$ with $N < p$, the map `SobolevEuclidean.toBoundedContinuousMapL` is
injective: the continuous representative determines the element of $W^{1,p}(\mathbb{R}^N)$. -/
theorem SobolevEuclidean.toBoundedContinuousMapL_injective (hp : N < p) :
    Function.Injective (SobolevEuclidean.toBoundedContinuousMapL N p hp) := fun u v huv ↦ by
  refine ext_of_fn_ae_eq (eventuallyEq_restrict_coe_top_iff.2 ?_)
  refine (SobolevEuclidean.fn_ae_eq_toBoundedContinuousMapL hp u).trans ?_
  rw [huv]
  exact (SobolevEuclidean.fn_ae_eq_toBoundedContinuousMapL hp v).symm

/-- For $1 \le p < \infty$ with $N < p$, the map $W^{1,p}(\mathbb{R}^N) \to C_b(\mathbb{R}^N)$,
$u \mapsto \tilde u$, is a continuous embedding. This is "$W^{1,p}(\mathbb{R}^N) \subset
L^\infty(\mathbb{R}^N)$ with continuous injection" of Theorem 9.12 of [brezis2011functional]. -/
theorem SobolevEuclidean.isContinuousEmbedding_toBoundedContinuousMapL (hp : N < p) :
    IsContinuousEmbedding (SobolevEuclidean.toBoundedContinuousMapL N p hp).toLinearMap :=
  ⟨SobolevEuclidean.toBoundedContinuousMapL_injective hp, _,
    SobolevEuclidean.norm_toBoundedContinuousMapL_apply_le hp⟩

/-- Let $1 \le p < \infty$ with $N < p$. For every $u \in W^{1,p}(\mathbb{R}^N)$, the function
`SobolevMultiIndex.fn u` is essentially bounded, with
$$\|u\|_\infty \le C' (N + 1) \|u\|,$$
where $C'$ is `MeasureTheory.morreySupConst` for Lebesgue measure. This is
$W^{1,p}(\mathbb{R}^N) \subseteq L^\infty(\mathbb{R}^N)$ of Theorem 9.12 of
[brezis2011functional], with the bound. -/
theorem SobolevEuclidean.eLpNorm_fn_top_le_of_lt (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    eLpNorm (fn u) ⊤ volume ≤ morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p
      * (N + 1) * ENNReal.ofReal ‖u‖ := by
  rw [eLpNorm_congr_ae (SobolevEuclidean.fn_ae_eq_contRep hp u)]
  refine (eLpNorm_le_of_ae_enorm_bound
    (SobolevEuclidean.contRep hp u).continuous.aestronglyMeasurable (Eventually.of_forall
      (SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u).choose_spec.2.2.2.1)).trans ?_
  simp

/-- Let $1 \le p < \infty$ with $N < p$. Then $W^{1,p}(\mathbb{R}^N) \subseteq
L^\infty(\mathbb{R}^N)$: for every $u \in W^{1,p}(\mathbb{R}^N)$, the function
`SobolevMultiIndex.fn u` lies in $L^\infty(\mathbb{R}^N)$. This is the inclusion of Theorem 9.12
of [brezis2011functional]. -/
theorem SobolevEuclidean.memLp_fn_top_of_lt (hp : N < p) (u : SobolevEuclidean N 1 p ⊤) :
    MemLp (fn u) ⊤ volume :=
  memLp_iff.2 ((SobolevEuclidean.eLpNorm_fn_top_le_of_lt hp u).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (morreySupConst_ne_top _ _).lt_top (by simp))
      ENNReal.ofReal_lt_top))

end TypedMorrey

/-!
### The limiting case $p = N$

This is Corollary 9.11 of [brezis2011functional]. For $u \in C_c^1$, the Gagliardo–Nirenberg–Sobolev
inequality for $p = 1$, applied to $\|u\|^\gamma$ with $\gamma > 1$, gives the inequality (20) of
the source,
$$\|u\|_{\gamma N'}^\gamma \le C \gamma \|u\|_{(\gamma - 1) N'}^{\gamma - 1} \|\nabla u\|_N, \qquad
  N' = \frac{N}{N - 1}.$$
Young's inequality turns it into (21), $\|u\|_{\gamma N'} \le K (\|u\|_{(\gamma - 1) N'} + \|\nabla
u\|_N)$. Induction on $\gamma = N, N + 1, \dots$ and the interpolation inequality between
consecutive exponents cover every $q \in [N, \infty)$.
-/

section LimitingCase

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F}

/-- Let $E$ be a real normed space of finite dimension $N \ge 2$ with an additive Haar measure
$\mu$, and let $F$ be a real inner product space. Let $u : E \to F$ be $C^1$ with compact
support, let $N' = N/(N - 1)$, and let $\gamma > 1$. Then
$$\|u\|_{\gamma N'}^\gamma \le C \gamma \, \|u\|_{(\gamma - 1) N'}^{\gamma - 1} \, \|\nabla
  u\|_N,$$
where $C$ is Mathlib's constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ N'`. This is the
inequality (20) of the proof of Corollary 9.11 of [brezis2011functional].

The proof applies Mathlib's inequality for $p = 1$ to $\|u\|^\gamma$, whose derivative is
bounded by $\gamma \|u\|^{\gamma - 1} \|\nabla u\|$, and then Hölder's inequality with the
exponents $N'$ and $N$. The exponent $N'$ is `NNReal.conjExponent N`. -/
theorem ContDiff.eLpNorm_rpow_le_of_hasCompactSupport (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) (hN : 2 ≤ finrank ℝ E) {γ : ℝ≥0} (hγ : 1 < γ) :
    eLpNorm u ((γ * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ ^ (γ : ℝ)
      ≤ eLpNormLESNormFDerivOneConst μ (NNReal.conjExponent (finrank ℝ E)) * γ
        * eLpNorm u (((γ - 1) * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ
          ^ ((γ : ℝ) - 1)
        * eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ := by
  set n : ℕ := finrank ℝ E with hn
  set n' : ℝ≥0 := NNReal.conjExponent n with hn'
  have hn1 : (1 : ℝ≥0) < n := by exact_mod_cast hN
  have hnn' : NNReal.HolderConjugate n n' := .conjExponent hn1
  have hn0 : (n : ℝ≥0) ≠ 0 := hnn'.pos.ne'
  have hn'0 : n' ≠ 0 := hnn'.symm.pos.ne'
  have hγ0 : γ ≠ 0 := (zero_lt_one.trans hγ).ne'
  have hγ0r : (γ : ℝ) ≠ 0 := by exact_mod_cast hγ0
  have hγ1 : (0 : ℝ) < (γ : ℝ) - 1 := by
    rw [sub_pos]
    exact_mod_cast hγ
  have hγ1' : γ - 1 ≠ 0 := (tsub_pos_of_lt hγ).ne'
  have hγ1c : ((γ - 1 : ℝ≥0) : ℝ) = (γ : ℝ) - 1 := NNReal.coe_sub hγ.le
  have hu' : Continuous u := hu.continuous
  have hd : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hfd : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  -- the function `‖u‖^γ`
  set v : E → ℝ := fun x ↦ ‖u x‖ ^ (γ : ℝ) with hv
  have hvs : ContDiff ℝ 1 v := hu.norm_rpow (by exact_mod_cast hγ)
  have hvc : HasCompactSupport v := h2u.norm.rpow_const hγ0r
  set C := eLpNormLESNormFDerivOneConst μ n' with hC
  -- the left side is the `L^{N'}` norm of `v`
  have h1 : eLpNorm u ((γ * n' : ℝ≥0) : ℝ≥0∞) μ ^ (γ : ℝ) = eLpNorm v n' μ := by
    rw [eLpNorm_nnreal_eq_lintegral (mul_ne_zero hγ0 hn'0) hu'.aestronglyMeasurable,
      eLpNorm_nnreal_eq_lintegral hn'0 hvs.continuous.aestronglyMeasurable, ← ENNReal.rpow_mul]
    congr 1
    · refine lintegral_congr fun x ↦ ?_
      rw [hv, Real.enorm_rpow_of_nonneg (norm_nonneg _) (NNReal.coe_nonneg γ), enorm_norm,
        ← ENNReal.rpow_mul, NNReal.coe_mul]
    · push_cast
      field_simp
  -- measurability of the two factors of Hölder's inequality
  have hm1 : Measurable fun x ↦ ‖u x‖ₑ ^ ((γ : ℝ) - 1) := by
    borelize F
    exact (hu'.measurable.enorm).pow_const _
  have hm2 : Measurable fun x ↦ ‖fderiv ℝ u x‖ₑ := hfd.measurable.enorm
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hnn'.symm.coe hm1.aemeasurable
    hm2.aemeasurable
  simp only [Pi.mul_apply] at hholder
  calc eLpNorm u ((γ * n' : ℝ≥0) : ℝ≥0∞) μ ^ (γ : ℝ) = eLpNorm v n' μ := h1
    _ ≤ C * eLpNorm (fderiv ℝ v) 1 μ := eLpNorm_le_eLpNorm_fderiv_one μ hvs hvc hnn'
    _ = C * ∫⁻ x, ‖fderiv ℝ v x‖ₑ ∂μ := by
        rw [eLpNorm_one_eq_lintegral_enorm (hvs.continuous_fderiv one_ne_zero).aestronglyMeasurable]
    _ ≤ C * (γ * ∫⁻ x, ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x‖ₑ ∂μ) := by
        rw [← lintegral_const_mul (r := (γ : ℝ≥0∞))
          (f := fun x ↦ ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x‖ₑ) (hm1.mul hm2)]
        refine mul_le_mul' le_rfl (lintegral_mono fun x ↦ ?_)
        simpa only [mul_assoc] using enorm_fderiv_norm_rpow_le hd hγ (x := x)
    _ ≤ C * (γ * ((∫⁻ x, (‖u x‖ₑ ^ ((γ : ℝ) - 1)) ^ (n' : ℝ) ∂μ) ^ (1 / (n' : ℝ))
          * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (n : ℝ) ∂μ) ^ (1 / (n : ℝ)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hholder)
    _ = C * γ * eLpNorm u (((γ - 1) * n' : ℝ≥0) : ℝ≥0∞) μ ^ ((γ : ℝ) - 1)
          * eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ := by
        rw [eLpNorm_nnreal_eq_lintegral hn0 hfd.aestronglyMeasurable,
          eLpNorm_nnreal_eq_lintegral (mul_ne_zero hγ1' hn'0) hu'.aestronglyMeasurable,
          ← ENNReal.rpow_mul, mul_assoc, mul_assoc]
        have hexp : 1 / (((γ - 1) * n' : ℝ≥0) : ℝ) * ((γ : ℝ) - 1) = 1 / (n' : ℝ) := by
          rw [NNReal.coe_mul, hγ1c]
          field_simp
        have hint : ∫⁻ x, ‖u x‖ₑ ^ (((γ - 1) * n' : ℝ≥0) : ℝ) ∂μ
            = ∫⁻ x, (‖u x‖ₑ ^ ((γ : ℝ) - 1)) ^ (n' : ℝ) ∂μ :=
          lintegral_congr fun x ↦ by rw [← ENNReal.rpow_mul, NNReal.coe_mul, hγ1c]
        rw [hexp, hint, NNReal.coe_natCast]

/-- Let $E$ be a real normed space of finite dimension $N \ge 2$ with an additive Haar measure
$\mu$, let $F$ be a real inner product space, let $N' = N/(N - 1)$, and let $\gamma > 1$. Then
there is a finite $K$ such that every $C^1$ function $u : E \to F$ with compact support
satisfies
$$\|u\|_{\gamma N'} \le K \left( \|u\|_{(\gamma - 1) N'} + \|\nabla u\|_N \right).$$
This is the inequality (21) of the proof of Corollary 9.11 of [brezis2011functional].

It follows from (20), `ContDiff.eLpNorm_rpow_le_of_hasCompactSupport`, by Young's inequality in
the form $b^\theta c^{1 - \theta} \le b + c$. -/
theorem MeasureTheory.exists_forall_eLpNorm_le_of_hasCompactSupport_of_one_lt (hN : 2 ≤ finrank ℝ E)
    {γ : ℝ≥0} (hγ : 1 < γ) : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : E → F, ContDiff ℝ 1 u →
      HasCompactSupport u →
      eLpNorm u ((γ * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ
        ≤ K * (eLpNorm u (((γ - 1) * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ) := by
  set n' : ℝ≥0 := NNReal.conjExponent (finrank ℝ E) with hn'
  set C : ℝ≥0∞ := eLpNormLESNormFDerivOneConst μ n' * γ with hC
  have hγr : (0 : ℝ) < γ := by exact_mod_cast zero_lt_one.trans hγ
  have hγr1 : (0 : ℝ) < (γ : ℝ) - 1 := by
    rw [sub_pos]
    exact_mod_cast hγ
  refine ⟨C ^ (1 / (γ : ℝ)), ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top), fun u hu h2u ↦ ?_⟩
  have h20 := hu.eLpNorm_rpow_le_of_hasCompactSupport (μ := μ) h2u hN hγ
  rw [← hn', ← hC] at h20
  set A := eLpNorm u ((γ * n' : ℝ≥0) : ℝ≥0∞) μ with hA
  set B := eLpNorm u (((γ - 1) * n' : ℝ≥0) : ℝ≥0∞) μ with hB
  set D := eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ with hD
  calc A = (A ^ (γ : ℝ)) ^ (1 / (γ : ℝ)) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hγr.ne', ENNReal.rpow_one]
    _ ≤ (C * B ^ ((γ : ℝ) - 1) * D) ^ (1 / (γ : ℝ)) := ENNReal.rpow_le_rpow h20 (by positivity)
    _ = C ^ (1 / (γ : ℝ)) * (B ^ (((γ : ℝ) - 1) / γ) * D ^ (1 - ((γ : ℝ) - 1) / γ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_assoc]
        congr 3
        · ring
        · field_simp
          ring
    _ ≤ C ^ (1 / (γ : ℝ)) * (B + D) :=
        mul_le_mul' le_rfl (ENNReal.rpow_mul_rpow_one_sub_le_add _ _ (by positivity)
          ((div_le_one hγr).2 (by linarith)))

/-- Let $E$ be a real normed space of finite dimension $N \ge 2$ with an additive Haar measure
$\mu$, let $F$ be a real inner product space, and let $N' = N/(N - 1)$. For every natural number
$m$ there is a finite $K$ such that every $C^1$ function $u : E \to F$ with compact support
satisfies
$$\|u\|_{(N - 1 + m) N'} \le K \left( \|u\|_N + \|\nabla u\|_N \right).$$
This is the induction of the proof of Corollary 9.11 of [brezis2011functional], "reiterating
this argument with $m = N + 1$, $m = N + 2$, etc.".

The case $m = 0$ holds because $(N - 1) N' = N$. Each step is the inequality (21) with
$\gamma = N + m$. -/
theorem MeasureTheory.exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank_aux
    (hN : 2 ≤ finrank ℝ E) (m : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u (((finrank ℝ E - 1 + m : ℕ) * NNReal.conjExponent (finrank ℝ E) : ℝ≥0) : ℝ≥0∞) μ
        ≤ K * (eLpNorm u ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ) := by
  set n : ℕ := finrank ℝ E with hn
  set n' : ℝ≥0 := NNReal.conjExponent n with hn'
  have hn1 : (1 : ℝ≥0) < n := by exact_mod_cast hN
  have hnn' : NNReal.HolderConjugate n n' := .conjExponent hn1
  induction m with
  | zero =>
    refine ⟨1, ENNReal.one_ne_top, fun u _ _ ↦ ?_⟩
    have : ((n - 1 + 0 : ℕ) : ℝ≥0) * n' = n := by
      rw [add_zero, Nat.cast_tsub, Nat.cast_one, hnn'.sub_one_mul_conj]
    rw [this, one_mul]
    exact le_self_add
  | succ m ih =>
    obtain ⟨K, hK, hKu⟩ := ih
    have hγ : (1 : ℝ≥0) < ((n - 1 + (m + 1) : ℕ) : ℝ≥0) := by
      have : 2 ≤ n - 1 + (m + 1) := by omega
      exact_mod_cast this
    obtain ⟨K', hK', hK'u⟩ :=
      exists_forall_eLpNorm_le_of_hasCompactSupport_of_one_lt (μ := μ) (F := F) hN hγ
    refine ⟨K' * (K + 1), ENNReal.mul_ne_top hK' (ENNReal.add_ne_top.2 ⟨hK, ENNReal.one_ne_top⟩),
      fun u hu h2u ↦ ?_⟩
    have hsub : ((n - 1 + (m + 1) : ℕ) : ℝ≥0) - 1 = ((n - 1 + m : ℕ) : ℝ≥0) := by
      rw [show n - 1 + (m + 1) = (n - 1 + m) + 1 by omega, Nat.cast_succ, add_tsub_cancel_right]
    calc eLpNorm u (((n - 1 + (m + 1) : ℕ) * n' : ℝ≥0) : ℝ≥0∞) μ
        ≤ K' * (eLpNorm u (((((n - 1 + (m + 1) : ℕ) : ℝ≥0) - 1) * n' : ℝ≥0) : ℝ≥0∞) μ
            + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) := hK'u u hu h2u
      _ ≤ K' * (K * (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ)
            + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) := by
          rw [hsub]
          exact mul_le_mul' le_rfl (add_le_add (hKu u hu h2u) le_rfl)
      _ ≤ K' * (K + 1) * (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ
            + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) := by
          rw [mul_assoc, add_mul, one_mul]
          exact mul_le_mul' le_rfl (add_le_add le_rfl le_add_self)

/-- Let $E$ be a real normed space of finite dimension $N \ge 2$ with an additive Haar measure
$\mu$, let $F$ be a real inner product space, and let $N \le q < \infty$. Then there is a finite
$K$ such that every $C^1$ function $u : E \to F$ with compact support satisfies
$$\|u\|_q \le K \left( \|u\|_N + \|\nabla u\|_N \right).$$
This is the inequality (23) of the proof of Corollary 9.11 of [brezis2011functional].

The proof interpolates between the exponent $N$ and an exponent $(N - 1 + m) N' \ge q$ of
`MeasureTheory.exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank_aux`. -/
theorem MeasureTheory.exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank
    (hN : 2 ≤ finrank ℝ E) {q : ℝ≥0} (hq : (finrank ℝ E : ℝ≥0) ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u q μ ≤ K * (eLpNorm u ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ
        + eLpNorm (fderiv ℝ u) ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ) := by
  set n : ℕ := finrank ℝ E with hn
  set n' : ℝ≥0 := NNReal.conjExponent n with hn'
  have hn1 : (1 : ℝ≥0) < n := by exact_mod_cast hN
  have hnn' : NNReal.HolderConjugate n n' := .conjExponent hn1
  have hn'1 : 1 ≤ n' := hnn'.symm.lt.le
  obtain ⟨K, hK, hKu⟩ :=
    exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank_aux (μ := μ) (F := F) hN ⌈q⌉₊
  have hqle : q ≤ ((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) * n' := by
    calc q ≤ (⌈q⌉₊ : ℝ≥0) := Nat.le_ceil q
      _ ≤ ((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) := by exact_mod_cast Nat.le_add_left _ _
      _ = ((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) * 1 := (mul_one _).symm
      _ ≤ ((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) * n' := mul_le_mul' le_rfl hn'1
  refine ⟨1 + K, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hK⟩, fun u hu h2u ↦ ?_⟩
  have hn0 : ((n : ℝ≥0) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hnn'.pos.ne'
  calc eLpNorm u q μ
      ≤ eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm u ((((n - 1 + ⌈q⌉₊ : ℕ) : ℝ≥0) * n' : ℝ≥0) : ℝ≥0∞) μ :=
        eLpNorm_le_eLpNorm_add_eLpNorm_of_le_of_le hu.continuous.aestronglyMeasurable hn0
          (by exact_mod_cast hq) (by exact_mod_cast hqle)
    _ ≤ (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ)
          + K * (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) :=
        add_le_add le_self_add (hKu u hu h2u)
    _ = (1 + K) * (eLpNorm u ((n : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm (fderiv ℝ u) ((n : ℝ≥0) : ℝ≥0∞) μ) := by ring

variable [CompleteSpace F]

/-- **The limiting case $p = N$ of the Sobolev embedding.** Let $E$ be a real normed space of finite
dimension $N \ge 2$ with an additive Haar measure $\mu$, let $F$ be a real Hilbert space, and
let $N \le q < \infty$. Then there is a finite $K$ such that, for all $f, w \in L^N$ where $w$
is a weak derivative of $f$ on $E$,
$$\|f\|_q \le K \left( \|f\|_N + \|w\|_N \right).$$
In particular $W^{1,N}(\mathbb{R}^N) \subseteq L^q(\mathbb{R}^N)$ with continuous injection.
This is Corollary 9.11 of [brezis2011functional].

The inequality for $C_c^1$ functions,
`MeasureTheory.exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank`, extends to $f$ by
density and Fatou's lemma, as in the proof of
`HasWeakFDerivOn.eLpNorm_le_eLpNorm_weakFDeriv_of_eq`. -/
theorem MeasureTheory.exists_forall_eLpNorm_le_of_eq_finrank (hN : 2 ≤ finrank ℝ E) {q : ℝ≥0}
    (hq : (finrank ℝ E : ℝ≥0) ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (f : E → F) (w : E → E →L[ℝ] F), HasWeakFDerivOn f w ⊤ μ →
      MemLp f ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ → MemLp w ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ →
      eLpNorm f q μ ≤ K * (eLpNorm f ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ
        + eLpNorm w ((finrank ℝ E : ℝ≥0) : ℝ≥0∞) μ) := by
  set n : ℕ := finrank ℝ E with hn
  obtain ⟨K, hK, hKu⟩ :=
    exists_forall_eLpNorm_le_of_hasCompactSupport_of_eq_finrank (μ := μ) (F := F) hN hq
  refine ⟨K, hK, fun f w h hf hw ↦ ?_⟩
  have hn1 : (1 : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast (one_le_two.trans hN)
  obtain ⟨u, hus, huc, hu0, hu1⟩ :=
    h.exists_seq_contDiff_hasCompactSupport_tendsto_top hn1 ENNReal.coe_ne_top hf hw
  have hmeas : TendstoInMeasure μ u atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le hn1).ne' hu0
  obtain ⟨ns, hns_mono, hns⟩ := hmeas.exists_seq_tendsto_ae
  refine ENNReal.le_mul_of_forall_pos_le_mul_add hK fun δ hδ ↦ ?_
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  have hev0 := ENNReal.tendsto_nhds_zero.1 hu0 (δ / 2) hδ2
  have hev1 := ENNReal.tendsto_nhds_zero.1 hu1 (δ / 2) hδ2
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun n ↦ u (ns n)) ?_
    (fun n ↦ (hus _).continuous.aestronglyMeasurable) hf.aestronglyMeasurable hns
  filter_upwards [hns_mono.tendsto_atTop.eventually hev0,
    hns_mono.tendsto_atTop.eventually hev1] with k hk0 hk1
  refine (hKu _ ((hus _).of_le (by simp)) (huc _)).trans (mul_le_mul' le_rfl ?_)
  calc eLpNorm (u (ns k)) ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm (fderiv ℝ (u (ns k))) ((n : ℝ≥0) : ℝ≥0∞) μ
      ≤ (eLpNorm (fun x ↦ u (ns k) x - f x) ((n : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm f ((n : ℝ≥0) : ℝ≥0∞) μ)
        + (eLpNorm (fun x ↦ fderiv ℝ (u (ns k)) x - w x) ((n : ℝ≥0) : ℝ≥0∞) μ
          + eLpNorm w ((n : ℝ≥0) : ℝ≥0∞) μ) :=
        add_le_add (eLpNorm_le_eLpNorm_sub_add hn1 _ f) (eLpNorm_le_eLpNorm_sub_add hn1 _ w)
    _ ≤ (δ / 2 + eLpNorm f ((n : ℝ≥0) : ℝ≥0∞) μ) + (δ / 2 + eLpNorm w ((n : ℝ≥0) : ℝ≥0∞) μ) :=
        add_le_add (add_le_add hk0 le_rfl) (add_le_add hk1 le_rfl)
    _ = eLpNorm f ((n : ℝ≥0) : ℝ≥0∞) μ + eLpNorm w ((n : ℝ≥0) : ℝ≥0∞) μ + δ := by
        rw [add_add_add_comm, ENNReal.add_halves, add_comm]

end LimitingCase

section TypedLimitingCase

open SobolevMultiIndex

variable {N : ℕ} {q : ℝ≥0}

/-- Let $N \ge 2$ and $N \le q < \infty$. Then there is a finite $K$ such that every
$u \in W^{1,N}(\mathbb{R}^N)$ satisfies
$$\|u\|_q \le K \|u\|.$$
This is the bound of Corollary 9.11 of [brezis2011functional]. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N 1 N ⊤,
      eLpNorm (fn u) q volume ≤ K * ENNReal.ofReal ‖u‖ := by
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  obtain ⟨K, hK, hKu⟩ := exists_forall_eLpNorm_le_of_eq_finrank
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin N)))) (F := ℝ) (by rw [hfin]; exact hN)
    (q := q) (by rw [hfin]; exact hq)
  rw [hfin, ENNReal.coe_natCast] at hKu
  refine ⟨K * (N + 1), ENNReal.mul_ne_top hK (by simp), fun u ↦ ?_⟩
  obtain ⟨w, hw, hwp, hwle⟩ := SobolevEuclidean.exists_hasWeakFDerivOn u
  refine (hKu _ w hw (SobolevEuclidean.memLp_fn u) hwp).trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  calc eLpNorm (fn u) N volume + eLpNorm w N volume
      ≤ ENNReal.ofReal ‖u‖ + N * ENNReal.ofReal ‖u‖ :=
        add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
          (hwle.trans (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u))
    _ = (N + 1) * ENNReal.ofReal ‖u‖ := by ring

/-- Let $N \ge 2$ and $N \le q < \infty$. Then $W^{1,N}(\mathbb{R}^N) \subseteq L^q(\mathbb{R}^N)$:
for every $u \in W^{1,N}(\mathbb{R}^N)$, the function `SobolevMultiIndex.fn u` lies in
$L^q(\mathbb{R}^N)$. This is the inclusion of Corollary 9.11 of [brezis2011functional]. -/
theorem SobolevEuclidean.memLp_fn_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))] (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) (u : SobolevEuclidean N 1 N ⊤) : MemLp (fn u) q volume := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  exact memLp_iff.2 ((hKu u).trans_lt (ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top))

/-- Let $N \ge 2$ and $N \le q < \infty$. Then $W^{1,N}(\mathbb{R}^N) \hookrightarrow
L^q(\mathbb{R}^N)$ is a continuous embedding along `SobolevMultiIndex.toLpₗ`. This is Corollary
9.11 of [brezis2011functional]. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    [Fact (1 ≤ (q : ℝ≥0∞))] (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 N ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using
          SobolevEuclidean.memLp_fn_of_eq_finrank hN hq u) := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  refine isContinuousEmbedding_toLpₗ _ (C := K.toReal) fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (norm_nonneg u), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) ?_
  exact (eLpNorm_restrict_coe_top (fn u) (q : ℝ≥0∞)).trans_le (hKu u)

end TypedLimitingCase

/-! ### Lifting an $L^q$ bound at order $m$ to $W^{1,q}$ at order $m + 1$ -/

section Lift

open SobolevMultiIndex

variable {N m : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $1 \le p \le \infty$ and $1 \le q \le \infty$,
and let $K < \infty$. Suppose that every $v \in W^{m,p}(\Omega)$ satisfies
$\|v\|_{L^q(\Omega)} \le K \|v\|$. Then for every $u \in W^{m+1,p}(\Omega)$ there is
$w \in W^{1,q}(\Omega)$ whose function equals that of $u$ almost everywhere on $\Omega$, with
$$\|w\| \le (N + 1) K \|u\|.$$
This is the inductive step of the proof of Corollary 9.15 of [brezis2011functional] ("repeated
application of Corollary 9.14"), and the domain form of the inductive step of Corollary 9.13. -/
theorem SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ v : SobolevEuclidean N m p Ω, eLpNorm (fn v) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖v‖)
    (u : SobolevEuclidean N (m + 1) p Ω) :
    ∃ w : SobolevEuclidean N 1 q Ω,
      fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u ∧
      ‖w‖ ≤ (N + 1) * K.toReal * ‖u‖ := by
  classical
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : SobolevEuclidean N m p Ω,
      v₀ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume
        (Nat.le_succ m) u :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin N → SobolevEuclidean N m p Ω,
      v = fun i ↦ partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume i u :=
    ⟨_, rfl⟩
  have hv₀fn : fn v₀ = fn u := by rw [hv₀]; rfl
  have hv₀n : ‖v₀‖ ≤ ‖u‖ := by rw [hv₀]; exact norm_toLowerOrder_le _ u
  have hvn : ∀ i, ‖v i‖ ≤ ‖u‖ := fun i ↦ by rw [hv]; exact norm_partialDeriv_le i u
  have hvd : ∀ i, HasWeakIteratedLineDerivOn ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
      (fn u) (fn (v i)) Ω volume := fun i ↦ by
    rw [hv]
    exact hasWeakIteratedLineDerivOn_fn_partialDeriv i u
  -- the `L^q` bounds
  have hK' : ∀ v : SobolevEuclidean N m p Ω,
      eLpNorm (fn v) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        ≤ ENNReal.ofReal (K.toReal * ‖v‖) := fun v ↦ by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
    exact h v
  have h0 : MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
    rw [← hv₀fn]
    exact memLp_iff.2 ((hK' v₀).trans_lt ENNReal.ofReal_lt_top)
  have hi : ∀ i, MemLp (fn (v i)) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    fun i ↦ memLp_iff.2 ((hK' (v i)).trans_lt ENNReal.ofReal_lt_top)
  -- `fn u ∈ W^{1,q}(Ω)`
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn u) 1 q Ω
      volume := by
    refine ⟨h0, fun β hβ ↦ ?_⟩
    rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with hz | ⟨i, hi'⟩
    · obtain rfl : β = 0 := congrArg Subtype.val hz
      exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
        (h0.locallyIntegrableOn hq1), h0⟩
    · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi'
      exact ⟨fn (v i), (hvd i).of_perm (multiIndexTuple_single_perm _ i).symm, hi i⟩
  obtain ⟨w, hw⟩ := hmem.exists_sobolevMultiIndex
  refine ⟨w, hw, ?_⟩
  -- the bound on `‖w‖` through its components
  have hw0 : ‖weakDeriv w 0‖ ≤ K.toReal * ‖u‖ := by
    rw [Lp.norm_def, weakDeriv_zero]
    calc (eLpNorm (fn w) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        = (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
          rw [eLpNorm_congr_ae hw]
      _ ≤ (ENNReal.ofReal (K.toReal * ‖v₀‖)).toReal := by
          rw [← hv₀fn]
          exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hK' v₀)
      _ ≤ K.toReal * ‖u‖ := by
          rw [ENNReal.toReal_ofReal (by positivity)]
          exact mul_le_mul_of_nonneg_left hv₀n ENNReal.toReal_nonneg
  have hwi : ∀ i, ‖weakDeriv w (MultiIndexLE.single i)‖ ≤ K.toReal * ‖u‖ := fun i ↦ by
    have hwd : HasWeakIteratedLineDerivOn ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
        (fn u) (weakDeriv w (MultiIndexLE.single i)) Ω volume :=
      ((hasWeakIteratedLineDerivOn w (MultiIndexLE.single i)).of_perm
        (multiIndexTuple_single_perm _ i)).congr_ae hw (Filter.EventuallyEq.refl _ _)
    have hae : (weakDeriv w (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn (v i) :=
      (ae_restrict_iff' Ω.isOpen.measurableSet).2 (hwd.ae_eq (hvd i))
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    calc (eLpNorm (fn (v i)) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ (ENNReal.ofReal (K.toReal * ‖v i‖)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hK' (v i))
      _ ≤ K.toReal * ‖u‖ := by
          rw [ENNReal.toReal_ofReal (by positivity)]
          exact mul_le_mul_of_nonneg_left (hvn i) ENNReal.toReal_nonneg
  calc ‖w‖ ≤ ∑ α, ‖weakDeriv w α‖ := by
        rw [← Submodule.norm_coe]
        exact PiLp.norm_le_sum_norm _
    _ = ‖weakDeriv w 0‖ + ∑ i, ‖weakDeriv w (MultiIndexLE.single i)‖ :=
        MultiIndexLE.sum_univ_one _
    _ ≤ K.toReal * ‖u‖ + ∑ _i : Fin N, K.toReal * ‖u‖ :=
        add_le_add hw0 (Finset.sum_le_sum fun i _ ↦ hwi i)
    _ = (N + 1) * K.toReal * ‖u‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Let $1 \le p \le \infty$ and $1 \le q \le \infty$, and let $K < \infty$. Suppose that every
$v \in W^{m,p}(\mathbb{R}^N)$ satisfies $\|v\|_q \le K \|v\|$. Then for every
$u \in W^{m+1,p}(\mathbb{R}^N)$ there is $w \in W^{1,q}(\mathbb{R}^N)$ whose function equals
that of $u$ almost everywhere, with
$$\|w\| \le (N + 1) K \|u\|.$$
This is the inductive step of the proof of Corollary 9.13 of [brezis2011functional] ("repeated
applications").

The function $u$ and its partial derivatives $\partial_i u$ lie in $W^{m,p}(\mathbb{R}^N)$,
hence in $L^q(\mathbb{R}^N)$, and $\partial_i u$ is the weak derivative of $u$. The statement is
the case $\Omega = \mathbb{R}^N$ of
`SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le`. -/
theorem SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le {K : ℝ≥0∞}
    (hK : K ≠ ⊤)
    (h : ∀ v : SobolevEuclidean N m p ⊤, eLpNorm (fn v) q volume ≤ K * ENNReal.ofReal ‖v‖)
    (u : SobolevEuclidean N (m + 1) p ⊤) :
    ∃ w : SobolevEuclidean N 1 q ⊤, fn w =ᵐ[volume] fn u ∧ ‖w‖ ≤ (N + 1) * K.toReal * ‖u‖ := by
  obtain ⟨w, hw, hwn⟩ :=
    SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le (Ω := ⊤) hK
      (fun v ↦ by simpa only [Opens.coe_top, Measure.restrict_univ] using h v) u
  exact ⟨w, by simpa only [Opens.coe_top, Measure.restrict_univ] using hw, hwn⟩

end Lift

/-!
### The $L^q$ clauses of the higher-order embeddings

This is Corollary 9.13 of [brezis2011functional].
-/

section HigherOrderLq

open SobolevMultiIndex

variable {N : ℕ}

/-- **The first-order embeddings in one statement.** Let $1 \le p \le q < \infty$ with
$1/p - 1/N \le 1/q$, and let $N \ge 2$ or $p > 1$. Then there is a finite $K$ such that every
$u \in W^{1,p}(\mathbb{R}^N)$ satisfies
$$\|u\|_q \le K \|u\|.$$
This is Corollary 9.13 of [brezis2011functional] for $m = 1$.

The proof uses Corollary 9.10 when $p < N$ (then $q \le p^*$), Corollary 9.11 when $p = N$, and
Morrey's theorem interpolated with $L^p$ when $p > N$. The case $N = p = 1$ is excluded, because
Corollary 9.11 does not apply there. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N 1 p ⊤,
      eLpNorm (fn u) q volume ≤ K * ENNReal.ofReal ‖u‖ := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hq0 : (0 : ℝ) < q := hp0.trans_le (by exact_mod_cast hpq)
  rcases lt_trichotomy p N with hpN | hpN | hpN
  · -- `p < N`: Corollary 9.10
    have hN0 : (0 : ℝ) < N := hp0.trans (by exact_mod_cast hpN)
    obtain ⟨p', hp'⟩ : ∃ p' : ℝ≥0, (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ :=
      ⟨(p⁻¹ - (N : ℝ≥0)⁻¹)⁻¹, by
        rw [NNReal.coe_inv, NNReal.coe_sub (by
          exact_mod_cast (inv_strictAnti₀ (zero_lt_one.trans_le hp1) hpN).le), inv_inv]
        simp⟩
    have hp'0 : (0 : ℝ) < (p' : ℝ)⁻¹ := by
      rw [hp', sub_pos]
      exact inv_strictAnti₀ hp0 (by exact_mod_cast hpN)
    have hqp' : q ≤ p' := by
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ (inv_pos.1 hp'0) hq0, hp']
      exact hq
    exact ⟨ENNReal.ofReal (1 + SobolevEuclidean.gnsConst N p * N), ENNReal.ofReal_ne_top,
      fun u ↦ by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' u⟩
  · -- `p = N`: Corollary 9.11
    subst hpN
    have hN2 : 2 ≤ N := by
      rcases hN with hN | hN
      · exact hN
      · exact_mod_cast hN
    have hfin : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
    obtain ⟨K, hK, hKu⟩ := exists_forall_eLpNorm_le_of_eq_finrank
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin N)))) (F := ℝ) (by rw [hfin]; exact hN2)
      (q := q) (by rw [hfin]; exact hpq)
    rw [hfin] at hKu
    refine ⟨K * (N + 1), ENNReal.mul_ne_top hK (by simp), fun u ↦ ?_⟩
    obtain ⟨w, hw, hwp, hwle⟩ := SobolevEuclidean.exists_hasWeakFDerivOn u
    refine (hKu _ w hw (SobolevEuclidean.memLp_fn u) hwp).trans ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    calc eLpNorm (fn u) (N : ℝ≥0) volume + eLpNorm w (N : ℝ≥0) volume
        ≤ ENNReal.ofReal ‖u‖ + N * ENNReal.ofReal ‖u‖ :=
          add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
            (hwle.trans (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u))
      _ = (N + 1) * ENNReal.ofReal ‖u‖ := by ring
  · -- `p > N`: Morrey, interpolated with `L^p`
    refine ⟨1 + morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1),
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
        ENNReal.mul_ne_top (morreySupConst_ne_top _ _) (by simp)⟩, fun u ↦ ?_⟩
    calc eLpNorm (fn u) q volume
        ≤ eLpNorm (fn u) p volume + eLpNorm (fn u) ⊤ volume :=
          eLpNorm_le_eLpNorm_add_eLpNorm_of_le_of_le
            (SobolevEuclidean.memLp_fn u).aestronglyMeasurable (by exact_mod_cast hp0.ne')
            (by exact_mod_cast hpq) le_top
      _ ≤ ENNReal.ofReal ‖u‖ + morreySupConst volume p * (N + 1) * ENNReal.ofReal ‖u‖ :=
          add_le_add (SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u)
            (SobolevEuclidean.eLpNorm_fn_top_le_of_lt hpN u)
      _ = (1 + morreySupConst volume p * (N + 1)) * ENNReal.ofReal ‖u‖ := by ring

/-- Let $0 < p \le q$ and let $m$ be a natural number with $1/p - (m + 1)/N \le 1/q$. Then there is
an exponent $r$ with $p \le r \le q$,
$$\frac{1}{p} - \frac{m}{N} \le \frac{1}{r} \quad \text{and} \quad \frac{1}{r} - \frac{1}{N} \le
  \frac{1}{q}.$$
This is the intermediate exponent of the inductive step of Corollary 9.13 of
[brezis2011functional].

The proof takes $1/r = \max(1/p - m/N, 1/q)$. -/
theorem NNReal.exists_intermediate_sobolev_exponent {p q : ℝ≥0} (m : ℕ) (hp0 : 0 < p)
    (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - (m + 1 : ℕ) / N ≤ (q : ℝ)⁻¹) :
    ∃ r : ℝ≥0, p ≤ r ∧ r ≤ q ∧ (p : ℝ)⁻¹ - m / N ≤ (r : ℝ)⁻¹ ∧
      (r : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hq0 : (0 : ℝ) < q := hp0'.trans_le (by exact_mod_cast hpq)
  have hqinv : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.2 hq0
  have hmax : (0 : ℝ) < max ((p : ℝ)⁻¹ - m / N) (q : ℝ)⁻¹ := lt_max_of_lt_right hqinv
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ) = (max ((p : ℝ)⁻¹ - m / N) (q : ℝ)⁻¹)⁻¹ :=
    ⟨(max ((p : ℝ)⁻¹ - m / N) (q : ℝ)⁻¹)⁻¹.toNNReal, Real.coe_toNNReal _ (by positivity)⟩
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, hr, ← inv_le_inv₀ (inv_pos.2 hmax) hp0', inv_inv]
    refine max_le (sub_le_self _ (by positivity)) ?_
    exact inv_anti₀ hp0' (by exact_mod_cast hpq)
  · rw [← NNReal.coe_le_coe, hr, ← inv_le_inv₀ hq0 (inv_pos.2 hmax), inv_inv]
    exact le_max_right _ _
  · rw [hr, inv_inv]
    exact le_max_left _ _
  · rw [hr, inv_inv]
    rcases le_total ((p : ℝ)⁻¹ - m / N) (q : ℝ)⁻¹ with h | h
    · rw [max_eq_right h]
      exact sub_le_self _ (by positivity)
    · rw [max_eq_left h]
      refine le_trans (le_of_eq ?_) hq
      push_cast
      rw [add_div]
      ring

/-- **The higher-order $L^q$ embeddings.** Let $m$ be a natural number, let $1 \le p \le q < \infty$
with $1/p - m/N \le 1/q$, and let $N \ge 2$ or $p > 1$. Then there is a finite $K$ such that
every $u \in W^{m,p}(\mathbb{R}^N)$ satisfies
$$\|u\|_q \le K \|u\|.$$
This contains the first two clauses of Corollary 9.13 of [brezis2011functional]:
$W^{m,p}(\mathbb{R}^N) \subset L^q(\mathbb{R}^N)$ for $1/q = 1/p - m/N$ when $1/p - m/N > 0$,
and for every $q \in [p, \infty)$ when $1/p - m/N \le 0$.

The proof is by induction on $m$, through
`SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le` and the first-order
statement `SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le`, with the intermediate
exponent $1/r = \max(1/p - m/N, 1/q)$. The source proves the corollary by "repeated applications
of Theorem 9.9, Corollary 9.11 and Theorem 9.12". -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order (m : ℕ) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N m p ⊤,
      eLpNorm (fn u) q volume ≤ K * ENNReal.ofReal ‖u‖ := by
  induction m generalizing p q with
  | zero =>
    have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
    have hq0 : (0 : ℝ) < q := hp0.trans_le (by exact_mod_cast hpq)
    obtain rfl : q = p := by
      refine le_antisymm ?_ hpq
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hp0 hq0]
      simpa using hq
    exact ⟨1, ENNReal.one_ne_top, fun u ↦ by
      rw [one_mul]
      exact SobolevEuclidean.eLpNorm_fn_le_ofReal_norm u⟩
  | succ m ih =>
    have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
    obtain ⟨r, hpr, hrq, hr₁, hr₂⟩ :=
      NNReal.exists_intermediate_sobolev_exponent (N := N) m (zero_lt_one.trans_le hp1) hpq hq
    have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
    have hNr : 2 ≤ N ∨ 1 < r := hN.imp id fun h ↦ h.trans_le hpr
    obtain ⟨K₁, hK₁, hK₁u⟩ := ih (q := r) hN hpr hr₁
    obtain ⟨K₂, hK₂, hK₂u⟩ :=
      SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le (N := N) hNr hrq hr₂
    refine ⟨K₂ * ((N + 1) * K₁), ENNReal.mul_ne_top hK₂ (ENNReal.mul_ne_top (by simp) hK₁),
      fun u ↦ ?_⟩
    obtain ⟨w, hw, hwn⟩ :=
      SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le hK₁ hK₁u u
    rw [← eLpNorm_congr_ae hw]
    refine (hK₂u w).trans ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    calc ENNReal.ofReal ‖w‖ ≤ ENNReal.ofReal ((N + 1) * K₁.toReal * ‖u‖) :=
          ENNReal.ofReal_le_ofReal hwn
      _ = (N + 1) * K₁ * ENNReal.ofReal ‖u‖ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_toReal hK₁]
          congr 2
          rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one,
            ENNReal.ofReal_natCast]

end HigherOrderLq

/-!
### The continuous representative at every order

This is part of Corollary 9.13 of [brezis2011functional].
-/

section HigherOrderContinuous

open SobolevMultiIndex

variable {N : ℕ}

/-- Let $1 \le p < \infty$ with $N < p$, and let $\tilde u$ be the continuous representative of
$u \in W^{1,p}(\mathbb{R}^N)$. For all $x, y$,
$$|\tilde u(x) - \tilde u(y)| \le C N \|u\| \, \|x - y\|^{1 - N/p},$$
where $C$ is `MeasureTheory.morreyConst` for Lebesgue measure, as a real number. This is the
Hölder estimate (25) of [brezis2011functional], §9.3, in the norm of $W^{1,p}(\mathbb{R}^N)$. -/
theorem SobolevEuclidean.norm_contRep_sub_le {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : N < p)
    (u : SobolevEuclidean N 1 p ⊤) (x y : EuclideanSpace ℝ (Fin N)) :
    ‖SobolevEuclidean.contRep hp u x - SobolevEuclidean.contRep hp u y‖
      ≤ (morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * N).toReal * ‖u‖
        * ‖x - y‖ ^ (1 - N / (p : ℝ)) := by
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ≥0∞,
    K₁ = morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * N := ⟨_, rfl⟩
  have hK₁t : K₁ ≠ ⊤ := by
    rw [hK₁]
    exact ENNReal.mul_ne_top (morreyConst_ne_top _ _) (by simp)
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have h1 : ‖SobolevEuclidean.contRep hp u x - SobolevEuclidean.contRep hp u y‖ₑ
      ≤ K₁ * ENNReal.ofReal ‖u‖ * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ))) := by
    rw [hK₁]
    refine (SobolevEuclidean.enorm_contRep_sub_le hp u x y).trans ?_
    calc morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
          * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖
        ≤ morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
            * (N * ENNReal.ofReal ‖u‖) :=
          mul_le_mul' le_rfl (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le u)
      _ = _ := by ring
  rw [← hK₁, ← toReal_enorm]
  refine (ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK₁t ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
    h1).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal (by positivity)]

/-- Let $p > 0$ and let $m$ be a natural number with $N/p < m + 1$. Then there is an exponent
$r \ge p$ with $N < r$ and $1/p - m/N \le 1/r$ such that, if $(m + 1) - N/p < 1$, then
$$1 - \frac{N}{r} = (m + 1) - \frac{N}{p}.$$
This is the exponent of the step of Corollary 9.13 of [brezis2011functional] that gives the
continuous representative.

The condition $1/p - m/N \le 1/r$ gives $W^{m+1,p}(\mathbb{R}^N) \subseteq
W^{1,r}(\mathbb{R}^N)$ by `SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order`. The last
condition says that the Hölder exponent $1 - N/r$ of Morrey's theorem is the sharp exponent
$(m + 1) - N/p$ when the latter is less than $1$. -/
theorem NNReal.exists_morrey_exponent {p : ℝ≥0} (m : ℕ) (hp0 : 0 < p)
    (hm : (N : ℝ) / p < (m + 1 : ℕ)) :
    ∃ r : ℝ≥0, p ≤ r ∧ N < r ∧ (p : ℝ)⁻¹ - m / N ≤ (r : ℝ)⁻¹ ∧
      ((m + 1 : ℕ) - N / (p : ℝ) < 1 → 1 - N / (r : ℝ) = (m + 1 : ℕ) - N / (p : ℝ)) := by
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  push_cast at hm ⊢
  rcases lt_or_ge (m : ℝ) (N / p) with h | h
  · -- the sharp case `1/r = 1/p − m/N`
    have hN0 : (0 : ℝ) < N := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · exact absurd h (not_lt.2 (by simp [hN]))
      · exact_mod_cast hN
    have hpos : 0 < (p : ℝ)⁻¹ - m / N := by
      rw [sub_pos, div_lt_iff₀ hN0, inv_mul_eq_div, lt_div_iff₀ hp0']
      rwa [lt_div_iff₀ hp0'] at h
    obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ) = ((p : ℝ)⁻¹ - m / N)⁻¹ :=
      ⟨((p : ℝ)⁻¹ - m / N)⁻¹.toNNReal, Real.coe_toNNReal _ (by positivity)⟩
    have hrinv : (r : ℝ)⁻¹ = (p : ℝ)⁻¹ - m / N := by rw [hr, inv_inv]
    have hr0 : (0 : ℝ) < r := by rw [hr]; exact inv_pos.2 hpos
    refine ⟨r, ?_, ?_, hrinv.symm.le, fun _ ↦ ?_⟩
    · rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hr0 hp0', hrinv]
      exact sub_le_self _ (by positivity)
    · have : (N : ℝ) < r := by
        refine (inv_lt_inv₀ hr0 hN0).1 ?_
        rw [hrinv, sub_lt_iff_lt_add, inv_eq_one_div (N : ℝ), ← add_div, inv_eq_one_div,
          div_lt_div_iff₀ hp0' hN0, one_mul, add_comm]
        rwa [div_lt_iff₀ hp0'] at hm
      exact_mod_cast this
    · rw [div_eq_mul_inv (N : ℝ) (r : ℝ), hrinv]
      field_simp
      ring
  · -- `1/p − m/N ≤ 0`: take `r = p + N`
    refine ⟨p + N, le_self_add, ?_, ?_, fun h1 ↦ absurd h (not_le.2 (by linarith))⟩
    · rw [← NNReal.coe_lt_coe]
      push_cast
      linarith
    · push_cast
      rcases Nat.eq_zero_or_pos N with hN | hN
      · simp [hN]
      · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
        refine le_trans ?_ (inv_pos.2 (by positivity)).le
        rw [sub_nonpos, le_div_iff₀ hN0, inv_mul_eq_div, div_le_iff₀ hp0']
        rwa [div_le_iff₀ hp0'] at h

/-- **The continuous representative at every order.** Let $1 \le p < \infty$, let $m$ be a natural
number with $N/p < m$, and let $N \ge 2$ or $p > 1$. Then there are $C \ge 0$ and
$\theta \in (0, 1]$, with $\theta = m - N/p$ when $m - N/p < 1$, such that every
$u \in W^{m,p}(\mathbb{R}^N)$ has a continuous representative $\tilde u$ with, for all $x, y$,
$$|\tilde u(x)| \le C \|u\|, \qquad |\tilde u(x) - \tilde u(y)| \le C \|u\| \, \|x -
  y\|^\theta.$$
In particular $W^{m,p}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$ when $1/p - m/N < 0$. This
is the third clause of Corollary 9.13 of [brezis2011functional], and the case $k = 0$ of its
$C^k$ clause.

For $N \ge 1$ the condition $N/p < m$ is $1/p - m/N < 0$. The proof gives $W^{m,p}(\mathbb{R}^N)
\subseteq W^{1,r}(\mathbb{R}^N)$ for an $r > N$, with $1/r = 1/p - (m - 1)/N$ when this is
positive (`NNReal.exists_morrey_exponent`,
`SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order`), and then applies Morrey's theorem. -/
theorem SobolevEuclidean.exists_forall_continuous_ae_eq_of_order {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p < 1 → θ = m - N / p) ∧
      ∀ u : SobolevEuclidean N m p ⊤, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume] ũ ∧ (∀ x, ‖ũ x‖ ≤ C * ‖u‖) ∧
        ∀ x y, ‖ũ x - ũ y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ≥0) < p := zero_lt_one.trans_le hp1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    refine ⟨m - 1, ?_⟩
    have : 0 < m := by exact_mod_cast (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ N / p) hm)
    omega
  obtain ⟨r, hpr, hNr, hr₁, hθ⟩ := NNReal.exists_morrey_exponent (N := N) m' hp0 hm
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
  obtain ⟨K₁, hK₁, hK₁u⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order (N := N) m' hN hpr hr₁
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ,
    C₁ = (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) r * (N + 1)).toReal :=
    ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ,
    C₂ = (morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) r * N).toReal := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (N + 1) * K₁.toReal := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := hC₁ ▸ ENNReal.toReal_nonneg
  have hC₂0 : 0 ≤ C₂ := hC₂ ▸ ENNReal.toReal_nonneg
  have hD0 : 0 ≤ D := hD ▸ by positivity
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (Nat.cast_nonneg N) (by exact_mod_cast hNr)
  refine ⟨max C₁ C₂ * D, 1 - N / r, by positivity, ?_, ?_, hθ, fun u ↦ ?_⟩
  · exact sub_pos.2 ((div_lt_one hr0).2 (by exact_mod_cast hNr))
  · exact sub_le_self _ (by positivity)
  obtain ⟨w, hw, hwn⟩ :=
    SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_le hK₁ hK₁u u
  rw [← hD] at hwn
  refine ⟨SobolevEuclidean.contRep hNr w, (SobolevEuclidean.contRep hNr w).continuous,
    hw.symm.trans (SobolevEuclidean.fn_ae_eq_contRep hNr w), fun x ↦ ?_, fun x y ↦ ?_⟩
  · calc ‖SobolevEuclidean.contRep hNr w x‖ ≤ C₁ * ‖w‖ := by
          rw [hC₁]
          exact SobolevEuclidean.norm_contRep_apply_le hNr w x
      _ ≤ C₁ * (D * ‖u‖) := mul_le_mul_of_nonneg_left hwn hC₁0
      _ ≤ max C₁ C₂ * D * ‖u‖ := by
          rw [← mul_assoc]
          gcongr
          exact le_max_left _ _
  · calc ‖SobolevEuclidean.contRep hNr w x - SobolevEuclidean.contRep hNr w y‖
        ≤ C₂ * ‖w‖ * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by
          rw [hC₂]
          exact SobolevEuclidean.norm_contRep_sub_le hNr w x y
      _ ≤ C₂ * (D * ‖u‖) * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by gcongr
      _ ≤ max C₁ C₂ * D * ‖u‖ * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by
          rw [← mul_assoc]
          gcongr
          exact le_max_right _ _

/-- Let $1 \le p < \infty$, let $m$ be a natural number with $N/p < m$, and let $N \ge 2$ or
$p > 1$. Then there is a finite $K$ such that every $u \in W^{m,p}(\mathbb{R}^N)$ satisfies
$$\|u\|_\infty \le K \|u\|.$$
This is the bound of the third clause of Corollary 9.13 of [brezis2011functional],
$W^{m,p}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$ for $1/p - m/N < 0$. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_top_le_of_order {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N m p ⊤,
      eLpNorm (fn u) ⊤ volume ≤ K * ENNReal.ofReal ‖u‖ := by
  obtain ⟨C, θ, hC0, -, -, -, hC⟩ := SobolevEuclidean.exists_forall_continuous_ae_eq_of_order hN hm
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, hb, -⟩ := hC u
  rw [eLpNorm_congr_ae hae, ← ENNReal.ofReal_mul hC0]
  refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal (C * ‖u‖))
    hc.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hb x)

/-- Let $1 \le p < \infty$, let $m$ be a natural number with $N/p < m$, and let $N \ge 2$ or
$p > 1$. Then $W^{m,p}(\mathbb{R}^N) \subseteq L^\infty(\mathbb{R}^N)$: for every
$u \in W^{m,p}(\mathbb{R}^N)$, the function `SobolevMultiIndex.fn u` lies in
$L^\infty(\mathbb{R}^N)$. This is the inclusion of the third clause of Corollary 9.13 of
[brezis2011functional]. -/
theorem SobolevEuclidean.memLp_fn_top_of_order {m : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) (u : SobolevEuclidean N m p ⊤) :
    MemLp (fn u) ⊤ volume := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_top_le_of_order hN hm
  exact memLp_iff.2 ((hKu u).trans_lt (ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top))

/-- Let $1 \le p < \infty$, let $m$ be a natural number with $N/p < m$, and let $N \ge 2$ or
$p > 1$. Then $W^{m,p}(\mathbb{R}^N) \hookrightarrow L^\infty(\mathbb{R}^N)$ is a continuous
embedding along `SobolevMultiIndex.toLpₗ`. This is the third clause of Corollary 9.13 of
[brezis2011functional]. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_top_of_order {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m p ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_top_of_order hN hm u) := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_top_le_of_order hN hm
  refine isContinuousEmbedding_toLpₗ _ (C := K.toReal) fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (norm_nonneg u), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) ?_
  exact (eLpNorm_restrict_coe_top (fn u) ⊤).trans_le (hKu u)

/-- Let $m$ be a natural number, let $1 \le p \le q < \infty$ with $1/p - m/N \le 1/q$, and let
$N \ge 2$ or $p > 1$. Then $W^{m,p}(\mathbb{R}^N) \subseteq L^q(\mathbb{R}^N)$: for every
$u \in W^{m,p}(\mathbb{R}^N)$, the function `SobolevMultiIndex.fn u` lies in
$L^q(\mathbb{R}^N)$. This contains the first two clauses of Corollary 9.13 of
[brezis2011functional]: $1/q = 1/p - m/N$ when $1/p - m/N > 0$, and every $q \in [p, \infty)$
when $1/p - m/N \le 0$.

The clause for $L^\infty$ is `SobolevEuclidean.memLp_fn_top_of_order`. -/
theorem SobolevEuclidean.memLp_fn_of_order {m : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹)
    (u : SobolevEuclidean N m p ⊤) : MemLp (fn u) q volume := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order m hN hpq hq
  exact memLp_iff.2 ((hKu u).trans_lt (ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top))

/-- Let $m$ be a natural number, let $1 \le p \le q < \infty$ with $1/p - m/N \le 1/q$, and let
$N \ge 2$ or $p > 1$. Then $W^{m,p}(\mathbb{R}^N) \hookrightarrow L^q(\mathbb{R}^N)$ is a
continuous embedding along `SobolevMultiIndex.toLpₗ`. This is Corollary 9.13 of
[brezis2011functional], "all these injections are continuous", for the first two clauses. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_order {m : ℕ} {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m p ⊤ volume
      fun u ↦ by
        simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_of_order hN hpq hq u) := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order m hN hpq hq
  refine isContinuousEmbedding_toLpₗ _ (C := K.toReal) fun u ↦ ?_
  rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ← ENNReal.toReal_ofReal
    (norm_nonneg u), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) ?_
  exact (eLpNorm_restrict_coe_top (fn u) (q : ℝ≥0∞)).trans_le (hKu u)

end HigherOrderContinuous

/-!
### The $C^k$ representative

This is part of Corollary 9.13 of [brezis2011functional].
-/

section HigherOrderContDiff

open SobolevMultiIndex

variable {N : ℕ}

/-- A continuous linear functional $T$ on $\mathbb{R}^N$ is the sum $T = \sum_i T(e_i) \, \pi_i$,
where $e_i$ are the standard basis vectors and $\pi_i$ are the coordinate projections. -/
theorem ContinuousLinearMap.eq_sum_apply_single_smul_proj
    (T : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) :
    T = ∑ i, T (EuclideanSpace.single i 1) • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i := by
  ext v
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr v]
  simp [EuclideanSpace.basisFun_repr, mul_comm]

/-- Let $g : G \to G'$ be a continuous linear map between real normed spaces, and let $a, b$ be
continuous multilinear maps with values in $G$. Then
$$\|g \circ a - g \circ b\| \le \|g\| \, \|a - b\|.$$
-/
theorem ContinuousLinearMap.norm_compContinuousMultilinearMap_sub_le {ι G G' : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (g : G →L[ℝ] G') (a b : ContinuousMultilinearMap ℝ E G) :
    ‖g.compContinuousMultilinearMap a - g.compContinuousMultilinearMap b‖ ≤ ‖g‖ * ‖a - b‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have e : (g.compContinuousMultilinearMap a - g.compContinuousMultilinearMap b) m
      = g ((a - b) m) := by
    simp
  rw [e, mul_assoc]
  exact g.le_opNorm_of_le ((a - b).le_opNorm m)

/-- Let $g_i : E \to \mathbb{R}$, $i$ in a finite set, be $C^k$ at a point $x$, let $P_i \in F$, and
let $j \le k$. Then the $j$-th derivative at $x$ of $y \mapsto \sum_i g_i(y) P_i$ is
$$D^j \Big( \sum_i g_i P_i \Big)(x) = \sum_i D^j g_i(x) \, P_i,$$
that is, the sum of the compositions of $D^j g_i(x)$ with the maps $c \mapsto c P_i$. This is
the pointwise form of `iteratedFDeriv_fun_sum_smul_const`. -/
theorem iteratedFDeriv_fun_sum_smul_const_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
    {g : ι → E → ℝ} {k : ℕ} {x : E} (hg : ∀ i, ContDiffAt ℝ k (g i) x) (P : ι → F) {j : ℕ}
    (hj : j ≤ k) :
    iteratedFDeriv ℝ j (fun x ↦ ∑ i, g i x • P i) x
      = ∑ i, ((ContinuousLinearMap.id ℝ ℝ).smulRight (P i)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j (g i) x) := by
  have hjk : (j : ℕ∞ω) ≤ k := by exact_mod_cast hj
  rw [iteratedFDeriv_fun_sum_apply (f := fun i x ↦ g i x • P i) (u := Finset.univ) fun i _ ↦
    (((hg i).smul contDiffAt_const).of_le hjk)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have e : (fun x ↦ g i x • P i) = ((ContinuousLinearMap.id ℝ ℝ).smulRight (P i)) ∘ g i := by
    funext y
    simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left _ (hg i) hjk]

/-- Let $g_i : E \to \mathbb{R}$, $i$ in a finite set, be $C^k$, let $P_i \in F$, and let $j \le k$.
Then at every $x$ the $j$-th derivative of $y \mapsto \sum_i g_i(y) P_i$ is
$$D^j \Big( \sum_i g_i P_i \Big)(x) = \sum_i D^j g_i(x) \, P_i,$$
that is, the sum of the compositions of $D^j g_i(x)$ with the maps $c \mapsto c P_i$. -/
theorem iteratedFDeriv_fun_sum_smul_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] {g : ι → E → ℝ} {k : ℕ}
    (hg : ∀ i, ContDiff ℝ k (g i)) (P : ι → F) {j : ℕ} (hj : j ≤ k) (x : E) :
    iteratedFDeriv ℝ j (fun x ↦ ∑ i, g i x • P i) x
      = ∑ i, ((ContinuousLinearMap.id ℝ ℝ).smulRight (P i)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j (g i) x) :=
  iteratedFDeriv_fun_sum_smul_const_of_contDiffAt (fun i ↦ (hg i).contDiffAt) P hj

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and let $u \in W^{m+1,p}(\Omega)$. If
$g_i = \partial_i u$ almost everywhere on $\Omega$ for each $i$, then
$x \mapsto \sum_i g_i(x) \, \pi_i$, where $\pi_i$ are the coordinate projections, is a weak
derivative of $u$ on $\Omega$.

Here $\partial_i u$ is the function of `SobolevMultiIndex.partialDeriv`, and the weak derivative
has values in the linear functionals on $\mathbb{R}^N$. -/
theorem SobolevEuclidean.hasWeakFDerivOn_sum_smul_proj {m : ℕ} {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (u : SobolevEuclidean N (m + 1) p Ω)
    {g : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hg : ∀ i, fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume i u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g i) :
    HasWeakFDerivOn (fn u) (fun x ↦ ∑ i, g i x • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i) Ω volume := by
  obtain ⟨w', hw'⟩ := ((memSobolevMultiIndex (toLowerOrder ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume (by omega : 1 ≤ m + 1) u)).memSobolev)
    |>.exists_hasWeakFDerivOn
  have hw'' : HasWeakFDerivOn (fn u) w' Ω volume := hw'.1
  have hcomp : ∀ i, (fun x ↦ w' x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g i := by
    intro i
    have h2 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u)
        (fun x ↦ w' x (EuclideanSpace.single i 1)) Ω volume := by
      have := HasWeakIteratedFDerivOn.lineDeriv hw'' ![EuclideanSpace.single i 1]
      simpa using this
    have h3 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u) (g i) Ω volume := by
      have := (hasWeakIteratedLineDerivOn_fn_partialDeriv i u).congr_ae
        (Filter.EventuallyEq.refl _ _) (hg i)
      simpa using this
    exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h2.ae_eq h3)
  have hae : w' =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ ∑ i, g i x • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i := by
    have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
        ∀ i, w' x (EuclideanSpace.single i 1) = g i x := ae_all_iff.2 hcomp
    filter_upwards [hall] with x hx
    rw [ContinuousLinearMap.eq_sum_apply_single_smul_proj (w' x)]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hx i]
  unfold HasWeakFDerivOn at hw'' ⊢
  refine hw''.congr_ae (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hae] with x hx
  simp only [hx]

/-- **The $C^k$ representative, in the form of the induction.** Let $1 \le p < \infty$, let $k$ and
$m$ be natural numbers with $k + N/p < m$, and let $N \ge 2$ or $p > 1$. Then there are
$C \ge 0$ and $\theta \in (0, 1]$, with $\theta = m - N/p - k$ when $m - N/p - k < 1$, such that
every $u \in W^{m,p}(\mathbb{R}^N)$ has a $C^k$ representative $\tilde u$ with, for all $x, y$,
$$\|D^j \tilde u(x)\| \le C \|u\| \quad (j \le k), \qquad \|D^k \tilde u(x) - D^k \tilde u(y)\|
  \le C \|u\| \, \|x - y\|^\theta.$$
This is the $C^k$ clause of Corollary 9.13 of [brezis2011functional].

The proof is by induction on $k$. The function $u$ and its partial derivatives $\partial_i u$
lie in $W^{m-1,p}(\mathbb{R}^N)$ and have $C^{k-1}$ representatives $\tilde u$ and $\tilde g_i$.
The function $x \mapsto \sum_i \tilde g_i(x) \pi_i$ is a continuous weak derivative of
$\tilde u$, so $\tilde u$ is $C^1$ with this derivative
(`HasWeakFDerivOn.exists_contDiffOn_ae_eq_of_continuousOn`, Remark 2 of the source), hence
$C^k$. Its derivatives of order $j + 1$ are assembled from those of order $j$ of the
$\tilde g_i$. -/
theorem SobolevEuclidean.exists_forall_contDiff_ae_eq_of_order (k : ℕ) {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p - k < 1 → θ = m - N / p - k) ∧
      ∀ u : SobolevEuclidean N m p ⊤, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ k ũ ∧
        fn u =ᵐ[volume] ũ ∧ (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * ‖u‖) ∧
        ∀ x y, ‖iteratedFDeriv ℝ k ũ x - iteratedFDeriv ℝ k ũ y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  induction k generalizing m with
  | zero =>
    rw [Nat.cast_zero, zero_add] at hm
    obtain ⟨C, θ, hC0, hθ0, hθ1, hθ, hC⟩ :=
      SobolevEuclidean.exists_forall_continuous_ae_eq_of_order hN hm
    refine ⟨C, θ, hC0, hθ0, hθ1, fun h ↦ ?_, fun u ↦ ?_⟩
    · rw [Nat.cast_zero, sub_zero] at h ⊢
      exact hθ h
    obtain ⟨ũ, hc, hae, hb, hh⟩ := hC u
    refine ⟨ũ, contDiff_zero.2 hc, hae, fun j hj x ↦ ?_, fun x y ↦ ?_⟩
    · obtain rfl : j = 0 := Nat.le_zero.1 hj
      rw [norm_iteratedFDeriv_zero]
      exact hb x
    · rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
        LinearIsometryEquiv.norm_map]
      exact hh x y
  | succ k ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
      refine ⟨m - 1, ?_⟩
      have : 0 < m := by
        have h0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
        exact_mod_cast h0
      omega
    have hm' : (k : ℝ) + N / p < m' := by
      push_cast at hm
      linarith
    obtain ⟨C₀, θ, hC₀, hθ0, hθ1, hθ, hC⟩ := ih hm'
    have hθ' : ((m' + 1 : ℕ) : ℝ) - N / p - ((k + 1 : ℕ) : ℝ) < 1 →
        θ = ((m' + 1 : ℕ) : ℝ) - N / p - ((k + 1 : ℕ) : ℝ) := by
      intro h
      push_cast at h ⊢
      rw [hθ (by linarith)]
      ring
    obtain ⟨L, hL⟩ : ∃ L : Fin N → (ℝ →L[ℝ] (EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)),
      L = fun i ↦ (ContinuousLinearMap.id ℝ ℝ).smulRight (PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i) :=
      ⟨_, rfl⟩
    have hL0 : 0 ≤ ∑ i, ‖L i‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    refine ⟨C₀ * (1 + ∑ i, ‖L i‖), θ, by positivity, hθ0, hθ1, hθ', fun u ↦ ?_⟩
    -- the lower-order elements
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : SobolevEuclidean N m' p ⊤,
        v₀ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p ⊤ volume
          (Nat.le_succ m') u :=
      ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin N → SobolevEuclidean N m' p ⊤,
        v = fun i ↦ partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p ⊤ volume i u :=
      ⟨_, rfl⟩
    have hv₀fn : fn v₀ = fn u := by rw [hv₀]; rfl
    have hv₀n : ‖v₀‖ ≤ ‖u‖ := by rw [hv₀]; exact norm_toLowerOrder_le _ u
    have hvn : ∀ i, ‖v i‖ ≤ ‖u‖ := fun i ↦ by rw [hv]; exact norm_partialDeriv_le i u
    obtain ⟨ũ, hũc, hũae, hũb, hũh⟩ := hC v₀
    rw [hv₀fn] at hũae
    choose g hgc hgae hgb hgh using fun i ↦ hC (v i)
    -- the tensor weak derivative of `fn u`, continuous
    obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
        w = fun x ↦ ∑ i, g i x • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i := ⟨_, rfl⟩
    have hwc : ContDiff ℝ k w := by
      rw [hw]
      exact ContDiff.sum fun i _ ↦ (hgc i).smul contDiff_const
    have hweak : HasWeakFDerivOn (fn u) w ⊤ volume := by
      rw [hw]
      exact SobolevEuclidean.hasWeakFDerivOn_sum_smul_proj u fun i ↦ by
        have h := hgae i
        rw [hv] at h
        exact eventuallyEq_restrict_coe_top_iff.2 h
    have hDw : ∀ j ≤ k, ∀ x, iteratedFDeriv ℝ j w x
        = ∑ i, (L i).compContinuousMultilinearMap (iteratedFDeriv ℝ j (g i) x) := by
      intro j hj x
      rw [hw, hL]
      exact iteratedFDeriv_fun_sum_smul_const hgc _ hj x
    -- `ũ` is `C¹` with derivative `w`
    obtain ⟨v', hv'c, hv'ae, hv'd⟩ :=
      hweak.exists_contDiffOn_ae_eq_of_continuousOn hwc.continuous.continuousOn
    have hv'ũ : v' = ũ :=
      Measure.eq_of_ae_eq (μ := volume)
        ((eventuallyEq_restrict_coe_top_iff.1 hv'ae).symm.trans hũae)
        (by simpa using hv'c.continuousOn) hũc.continuous
    have hd : ∀ x, HasFDerivAt ũ (w x) x := fun x ↦ hv'ũ ▸ hv'd x (by simp)
    have hfd : fderiv ℝ ũ = w := funext fun x ↦ (hd x).fderiv
    have hũc' : ContDiff ℝ (k + 1) ũ :=
      contDiff_succ_iff_fderiv.2 ⟨fun x ↦ (hd x).differentiableAt, by simp, by rw [hfd]; exact hwc⟩
    refine ⟨ũ, hũc', hũae, fun j hj x ↦ ?_, fun x y ↦ ?_⟩
    · -- the bounds on the derivatives of order `≤ k + 1`
      rcases j with _ | j
      · calc ‖iteratedFDeriv ℝ 0 ũ x‖ ≤ C₀ * ‖v₀‖ := hũb 0 (Nat.zero_le _) x
          _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by
              calc C₀ * ‖v₀‖ ≤ C₀ * ‖u‖ := mul_le_mul_of_nonneg_left hv₀n hC₀
                _ = C₀ * 1 * ‖u‖ := by ring
                _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by gcongr; linarith
      · have hjk : j ≤ k := Nat.succ_le_succ_iff.1 hj
        rw [← norm_iteratedFDeriv_fderiv, hfd, hDw j hjk x]
        calc ‖∑ i, (L i).compContinuousMultilinearMap (iteratedFDeriv ℝ j (g i) x)‖
            ≤ ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ j (g i) x‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
                ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
          _ ≤ ∑ i, ‖L i‖ * (C₀ * ‖u‖) := Finset.sum_le_sum fun i _ ↦
              mul_le_mul_of_nonneg_left ((hgb i j hjk x).trans
                (mul_le_mul_of_nonneg_left (hvn i) hC₀)) (norm_nonneg _)
          _ = C₀ * (∑ i, ‖L i‖) * ‖u‖ := by rw [← Finset.sum_mul]; ring
          _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by gcongr; linarith
    · -- the Hölder estimate on the top derivative
      rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map, hfd, hDw k le_rfl x,
        hDw k le_rfl y, ← Finset.sum_sub_distrib]
      calc ‖∑ i, ((L i).compContinuousMultilinearMap (iteratedFDeriv ℝ k (g i) x)
              - (L i).compContinuousMultilinearMap (iteratedFDeriv ℝ k (g i) y))‖
          ≤ ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ k (g i) x - iteratedFDeriv ℝ k (g i) y‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
              ContinuousLinearMap.norm_compContinuousMultilinearMap_sub_le _ _ _)
        _ ≤ ∑ i, ‖L i‖ * (C₀ * ‖u‖ * ‖x - y‖ ^ θ) := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_left ((hgh i x y).trans (by gcongr; exact hvn i)) (norm_nonneg _)
        _ = C₀ * (∑ i, ‖L i‖) * ‖u‖ * ‖x - y‖ ^ θ := by rw [← Finset.sum_mul]; ring
        _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ * ‖x - y‖ ^ θ := by gcongr; linarith

end HigherOrderContDiff

/-! ### The $C^k$ clause of Corollary 9.13, and the local $C^k$ representatives -/

section HigherOrderCorollaries

open SobolevMultiIndex

variable {N : ℕ}

/-- **The $C^k$ clause of the Sobolev embedding.** Let $1 \le p < \infty$, let $N \ge 2$ or $p > 1$,
and let $m$ and $k$ be natural numbers with
$$0 < m - N/p - k < 1.$$
Then there is $C \ge 0$ such that every $u \in W^{m,p}(\mathbb{R}^N)$ has a $C^k$ representative
$\tilde u$ with, for all $x, y$,
$$\|D^j \tilde u(x)\| \le C \|u\| \quad (j \le k), \qquad \|D^k \tilde u(x) - D^k \tilde u(y)\|
  \le C \|u\| \, \|x - y\|^{m - N/p - k}.$$
In particular $W^{m,p}(\mathbb{R}^N) \subset C^k(\mathbb{R}^N)$, up to the choice of a
representative. This is the $C^k$ clause of Corollary 9.13 of [brezis2011functional], with its
footnotes 13 and 14.

The source states the clause for $m - N/p > 0$ not an integer, with
$k = \lfloor m - N/p \rfloor$ and $\theta = m - N/p - k$. The hypothesis $0 < m - N/p - k < 1$
is this condition. -/
theorem SobolevEuclidean.exists_contDiff_ae_eq_of_order {m k : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hθ0 : 0 < (m : ℝ) - N / p - k)
    (hθ1 : (m : ℝ) - N / p - k < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N m p ⊤, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ,
      ContDiff ℝ k ũ ∧ fn u =ᵐ[volume] ũ ∧
      (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * ‖u‖) ∧
      ∀ x y, ‖iteratedFDeriv ℝ k ũ x - iteratedFDeriv ℝ k ũ y‖
        ≤ C * ‖u‖ * ‖x - y‖ ^ ((m : ℝ) - N / p - k) := by
  obtain ⟨C, θ, hC0, -, -, hθ, hC⟩ :=
    SobolevEuclidean.exists_forall_contDiff_ae_eq_of_order (N := N) k (m := m) hN (by linarith)
  obtain rfl := hθ hθ1
  exact ⟨C, hC0, hC⟩

/-- **The $C^k$ clause without the non-integer restriction.** Let $1 \le p < \infty$, let $k$ and
$m$ be natural numbers with $k + N/p < m$, and let $N \ge 2$ or $p > 1$. Then there are
$C \ge 0$ and $\theta \in (0, 1]$ such that every $u \in W^{m,p}(\mathbb{R}^N)$ has a $C^k$
representative $\tilde u$ with, for all $x, y$,
$$\|D^j \tilde u(x)\| \le C \|u\| \quad (j \le k), \qquad \|D^k \tilde u(x) - D^k \tilde u(y)\|
  \le C \|u\| \, \|x - y\|^\theta.$$
This follows from Corollary 9.13 of [brezis2011functional], and it is the form that the proofs
of Theorems 10.1 and 10.8 of the source use.

The heat equation needs $H^{2\ell}(\mathbb{R}^N) \subseteq C^k(\mathbb{R}^N)$ for
$k + N/2 < 2\ell$, where $2\ell - N/2$ is an integer for every even $N$. -/
theorem SobolevEuclidean.exists_contDiff_ae_eq_of_lt {m k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ∀ u : SobolevEuclidean N m p ⊤,
      ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ k ũ ∧ fn u =ᵐ[volume] ũ ∧
      (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * ‖u‖) ∧
      ∀ x y, ‖iteratedFDeriv ℝ k ũ x - iteratedFDeriv ℝ k ũ y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  obtain ⟨C, θ, hC0, hθ0, hθ1, -, hC⟩ :=
    SobolevEuclidean.exists_forall_contDiff_ae_eq_of_order (N := N) k hN hm
  exact ⟨C, θ, hC0, hθ0, hθ1, hC⟩

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The local $C^k$ representative.** Let $\Omega \subseteq \mathbb{R}^N$ be open, let
$1 \le p < \infty$, let $k$ and $m$ be natural numbers with $k + N/p < m$, and let $N \ge 2$ or
$p > 1$. If $f \in W^{m,p}_{\mathrm{loc}}(\Omega)$, then there is a function $\tilde u$ of class
$C^k$ on $\Omega$ with $f = \tilde u$ almost everywhere on $\Omega$.

On a ball $B$ with closure in $\Omega$, $\theta f \in W^{m,p}(\mathbb{R}^N)$ for a test function
$\theta$ equal to $1$ on $B$ (`MemSobolevMultiIndexLoc.smul_testFunction`). This function has a
$C^k$ representative by `SobolevEuclidean.exists_contDiff_ae_eq_of_lt`. The local
representatives glue (`MeasureTheory.exists_continuousOn_ae_eq_of_forall_exists_ball`), and the
class $C^k$ on $\Omega$ is a local property. -/
theorem MemSobolevMultiIndexLoc.exists_contDiffOn_of_lt {m k : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m)
    {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f m p Ω volume) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ k ũ Ω ∧
      f =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ := by
  obtain ⟨C, θ, -, -, -, hC⟩ := SobolevEuclidean.exists_contDiff_ae_eq_of_lt (N := N) hN hm
  -- the local representatives
  have hP : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∃ r > 0,
      ball x r ⊆ (Ω : Set (EuclideanSpace ℝ (Fin N))) ∧ ∃ g : EuclideanSpace ℝ (Fin N) → ℝ,
        ContDiffOn ℝ k g (ball x r) ∧ ContinuousOn g (ball x r) ∧
        f =ᵐ[volume.restrict (ball x r)] g := by
    intro x hx
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
    obtain ⟨φ, hφ⟩ : ∃ φ : ContDiffBump x, φ = ⟨ε / 4, ε / 2, by positivity, by linarith⟩ :=
      ⟨_, rfl⟩
    have hIn : φ.rIn = ε / 4 := by rw [hφ]
    have hOut : φ.rOut = ε / 2 := by rw [hφ]
    have hsupp : tsupport φ ⊆ Ω := by
      rw [φ.tsupport_eq, hOut]
      exact (closedBall_subset_ball (by linarith)).trans hεΩ
    obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : 𝓓(Ω, ℝ), ϑ = ⟨φ, φ.contDiff (n := ⊤), φ.hasCompactSupport, hsupp⟩ :=
      ⟨_, rfl⟩
    have hϑ1 : ∀ y ∈ ball x (ε / 4), ϑ y = 1 := fun y hy ↦ by
      rw [hϑ, TestFunction.coe_mk]
      exact φ.one_of_mem_closedBall (hIn ▸ ball_subset_closedBall hy)
    have hmem := MemSobolevMultiIndexLoc.smul_testFunction (Fact.out) hf ϑ
    obtain ⟨U, hU⟩ := hmem.exists_sobolevMultiIndex
    rw [eventuallyEq_restrict_coe_top_iff] at hU
    obtain ⟨ũ, hũc, hũae, -, -⟩ := hC U
    refine ⟨ε / 4, by positivity, (ball_subset_ball (by linarith)).trans hεΩ, ũ, hũc.contDiffOn,
      hũc.continuous.continuousOn, ?_⟩
    have h1 : f =ᵐ[volume.restrict (ball x (ε / 4))]
        (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun y ↦ ϑ y • f y := by
      refine ae_restrict_of_forall_mem measurableSet_ball fun y hy ↦ ?_
      rw [Set.indicator_of_mem (hεΩ (ball_subset_ball (by linarith) hy)), hϑ1 y hy, one_smul]
    exact h1.trans (ae_restrict_of_ae (hU.symm.trans hũae))
  obtain ⟨v, -, hfv, hloc⟩ := exists_continuousOn_ae_eq_of_forall_exists_ball (μ := volume) (Ω := Ω)
    (u := f) (fun g s ↦ ContDiffOn ℝ k g s) hP
  refine ⟨v, contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_, hfv⟩
  obtain ⟨r, hr, -, g, hg, hvg⟩ := hloc x hx
  exact ⟨ball x r, isOpen_ball, mem_ball_self hr,
    (hg.mono inter_subset_right).congr fun y hy ↦ hvg hy.2⟩

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open. If $f \in H^m_{\mathrm{loc}}(\Omega)$ for every
natural number $m$, then there is a function $\tilde u$ of class $C^\infty$ on $\Omega$ with
$f = \tilde u$ almost everywhere on $\Omega$. This is the step "$e_n \in \bigcap_m H^m(\omega)$
for all $\omega \subset\subset \Omega$, as a consequence $e_n \in C^\infty(\Omega)$" of the
proof of Theorem 9.31 of [brezis2011functional].

The $C^k$ representatives of `MemSobolevMultiIndexLoc.exists_contDiffOn_of_lt` are continuous on
$\Omega$ and equal almost everywhere, hence equal on $\Omega$. So the $C^0$ representative is
$C^k$ for every $k$. -/
theorem MemSobolevMultiIndexLoc.exists_contDiffOn {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : ∀ m, MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f m 2 Ω volume) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ ∞ ũ Ω ∧
      f =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ := by
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  have hN : 2 ≤ N ∨ 1 < (2 : ℝ≥0) := Or.inr one_lt_two
  have hrep : ∀ k : ℕ, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ k ũ Ω ∧
      f =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ := fun k ↦
    MemSobolevMultiIndexLoc.exists_contDiffOn_of_lt (m := k + N + 1) hN
      (by
        have : (N : ℝ) / (2 : ℝ≥0) ≤ N := by
          rw [NNReal.coe_ofNat]
          exact half_le_self (Nat.cast_nonneg N)
        push_cast
        linarith)
      (hf _)
  choose v hvc hfv using hrep
  refine ⟨v 0, contDiffOn_infty.2 fun k ↦ ?_, hfv 0⟩
  refine (hvc k).congr fun x hx ↦ ?_
  exact Measure.eqOn_open_of_ae_eq ((hfv 0).symm.trans (hfv k)) Ω.isOpen
    (hvc 0).continuousOn (hvc k).continuousOn hx

end HigherOrderCorollaries

/-!
### The embedding $W^{N,1}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$

This is Remark 13 of [brezis2011functional], Chapter 9.
-/

section LineFTC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The fundamental theorem of calculus along a line, as a bound.** Let $E$ be a real normed
space, let $g : E \to \mathbb{R}$ be $C^1$ with compact support, and let $v \in E$, $v \neq 0$.
For every $x \in E$,
$$|g(x)| \le \int_{\mathbb{R}} |Dg(x + s v) \, v| \, ds.$$

The bound holds because $g$ vanishes far out along the line. -/
theorem ContDiff.enorm_le_lintegral_fderiv_line {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {v : E} (hv : v ≠ 0) (x : E) :
    ‖g x‖ₑ ≤ ∫⁻ s : ℝ, ‖fderiv ℝ g (x + s • v) v‖ₑ := by
  obtain ⟨h', hh'⟩ : ∃ h' : ℝ → ℝ, h' = fun s ↦ fderiv ℝ g (x + s • v) v := ⟨_, rfl⟩
  have hd : ∀ s, HasDerivAt (fun s ↦ g (x + s • v)) (h' s) s := fun s ↦ by
    have h1 : HasDerivAt (fun s : ℝ ↦ x + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add x
    have h2 := (hg.differentiable one_ne_zero (x + s • v)).hasFDerivAt.comp_hasDerivAt s h1
    rw [hh']
    simpa [Function.comp_def] using h2
  have hc : Continuous h' := by
    rw [hh']
    exact ((hg.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  -- the function vanishes far out along the line
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ tsupport g ⊆ closedBall 0 R := by
    obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : E)).1 hgc.isCompact.isBounded
    exact ⟨max R 0, le_max_right _ _, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (R + ‖x‖) / ‖v‖ + 1 := ⟨_, rfl⟩
  have hT0 : 0 < T := by
    rw [hT]
    positivity
  have hzero : g (x + (-T) • v) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR hmem
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : ‖(-T) • v‖ - ‖x‖ ≤ ‖x + (-T) • v‖ := by
      have := norm_sub_norm_le ((-T) • v) (-x)
      rwa [sub_neg_eq_add, norm_neg, add_comm] at this
    rw [norm_smul, norm_neg, Real.norm_of_nonneg hT0.le] at h2
    have h3 : T * ‖v‖ = R + ‖x‖ + ‖v‖ := by
      rw [hT, add_mul, div_mul_cancel₀ _ hv0.ne', one_mul]
    linarith
  -- the fundamental theorem of calculus on `[-T, 0]`
  have hint : IntervalIntegrable h' volume (-T) 0 := hc.intervalIntegrable _ _
  have hftc : g x = ∫ s in (-T)..0, h' s := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s) hint
    rw [this, hzero, sub_zero]
    simp
  rw [hftc, intervalIntegral.integral_of_le (by linarith)]
  calc ‖∫ s in Ioc (-T) 0, h' s‖ₑ ≤ ∫⁻ s in Ioc (-T) 0, ‖h' s‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ s, ‖h' s‖ₑ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ s, ‖fderiv ℝ g (x + s • v) v‖ₑ := by rw [hh']

end LineFTC

section IteratedFTC

variable {N : ℕ}

/-- The standard basis vectors of $\mathbb{R}^N$ indexed by the natural numbers: the $n$-th vector
is $e_n$ for $n < N$ and $0$ for $n \ge N$. The indices start at $0$. -/
def EuclideanSpace.stdVec (N : ℕ) (n : ℕ) : EuclideanSpace ℝ (Fin N) :=
  if h : n < N then EuclideanSpace.single ⟨n, h⟩ 1 else 0

/-- For $n < N$, `EuclideanSpace.stdVec N n` is the basis vector $e_n$. -/
theorem EuclideanSpace.stdVec_of_lt {n : ℕ} (h : n < N) :
    EuclideanSpace.stdVec N n = EuclideanSpace.single ⟨n, h⟩ 1 := by
  simp [EuclideanSpace.stdVec, h]

/-- For $n < N$, `EuclideanSpace.stdVec N n` is not zero. -/
theorem EuclideanSpace.stdVec_ne_zero {n : ℕ} (h : n < N) : EuclideanSpace.stdVec N n ≠ 0 := by
  rw [EuclideanSpace.stdVec_of_lt h]
  intro h0
  have := congrArg (fun v : EuclideanSpace ℝ (Fin N) ↦ v ⟨n, h⟩) h0
  simp at this

/-- The tuple of $j$ directions $(e_{N-j}, \dots, e_{N-1})$ in $\mathbb{R}^N$: its $i$-th entry is
`EuclideanSpace.stdVec N (N - j + i)`. For $j \le N$ these are the last $j$ standard basis
vectors. For $j > N$ the subtraction $N - j$ is truncated to $0$. -/
def EuclideanSpace.stdDirs (N j : ℕ) : Fin j → EuclideanSpace ℝ (Fin N) :=
  fun i ↦ EuclideanSpace.stdVec N (N - j + i)

/-- For $j + 1 \le N$, the tuple `EuclideanSpace.stdDirs N (j + 1)` is $e_{N-1-j}$ followed by the
tuple `EuclideanSpace.stdDirs N j`. -/
theorem EuclideanSpace.stdDirs_succ {j : ℕ} (hj : j + 1 ≤ N) :
    EuclideanSpace.stdDirs N (j + 1)
      = Fin.cons (EuclideanSpace.stdVec N (N - 1 - j)) (EuclideanSpace.stdDirs N j) := by
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp only [EuclideanSpace.stdDirs, Fin.cons_zero, Fin.val_zero, add_zero]
    congr 1
    omega
  · simp only [EuclideanSpace.stdDirs, Fin.cons_succ, Fin.val_succ]
    congr 1
    omega

/-- The tuple `EuclideanSpace.stdDirs N N` is the standard basis $(e_0, \dots, e_{N-1})$ of
$\mathbb{R}^N$ in order. -/
theorem EuclideanSpace.stdDirs_self (i : Fin N) :
    EuclideanSpace.stdDirs N N i = EuclideanSpace.single i 1 := by
  simp only [EuclideanSpace.stdDirs, Nat.sub_self, zero_add]
  rw [EuclideanSpace.stdVec_of_lt i.2]

/-- **The iterated fundamental theorem of calculus, one direction at a time.** Let
$\varphi : \mathbb{R}^N \to \mathbb{R}$ be smooth with compact support, and let
$x \in \mathbb{R}^N$. For every $j \le N$, with $(d_0, \dots, d_{j-1}) = (e_{N-j}, \dots,
e_{N-1})$,
$$|\varphi(x)| \le \int_{\mathbb{R}^j} \Big| D^j \varphi\Big(x + \sum_i t_i d_i\Big)(d_0, \dots,
  d_{j-1}) \Big| \, dt.$$

The proof is by induction on $j$, through the line bound
`ContDiff.enorm_le_lintegral_fderiv_line` and the Fubini step
`MeasureTheory.lintegral_fin_succ_eq`. -/
theorem ContDiff.enorm_le_lintegral_iteratedFDeriv_stdDirs {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (x : EuclideanSpace ℝ (Fin N)) :
    ∀ j ≤ N, ‖φ x‖ₑ ≤ ∫⁻ t : Fin j → ℝ, ‖iteratedFDeriv ℝ j φ
      (x + ∑ i, t i • EuclideanSpace.stdDirs N j i) (EuclideanSpace.stdDirs N j)‖ₑ := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, iteratedFDeriv_zero_apply]
    rw [volume_pi, Measure.pi_of_empty _ (fun _ ↦ 0), lintegral_dirac]
  | succ j ih =>
    intro hj
    refine (ih (by omega)).trans ?_
    -- the pointwise line bound
    have hlt : N - 1 - j < N := by omega
    obtain ⟨v, hv⟩ : ∃ v, v = EuclideanSpace.stdVec N (N - 1 - j) := ⟨_, rfl⟩
    have hv0 : v ≠ 0 := hv ▸ EuclideanSpace.stdVec_ne_zero hlt
    have hg : ContDiff ℝ 1 fun z ↦ iteratedFDeriv ℝ j φ z (EuclideanSpace.stdDirs N j) :=
      (ContinuousMultilinearMap.apply ℝ _ ℝ (EuclideanSpace.stdDirs N j)).contDiff.comp
        (hφ.iteratedFDeriv_right (by simp))
    have hgc : HasCompactSupport ((fun T : EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ ↦
        T (EuclideanSpace.stdDirs N j)) ∘ iteratedFDeriv ℝ j φ) :=
      (hφc.iteratedFDeriv j).comp_left (by simp)
    have hfd : ∀ z, fderiv ℝ (fun z ↦ iteratedFDeriv ℝ j φ z (EuclideanSpace.stdDirs N j)) z v
        = iteratedFDeriv ℝ (j + 1) φ z (EuclideanSpace.stdDirs N (j + 1)) := fun z ↦ by
      rw [EuclideanSpace.stdDirs_succ hj, iteratedFDeriv_succ_apply_left, Fin.cons_zero,
        Fin.tail_cons, ← hv, fderiv_continuousMultilinear_apply_const_apply
          ((hφ.iteratedFDeriv_right (m := 1) (i := j) (by simp)).differentiable one_ne_zero z)]
    have hsum : ∀ (t : Fin j → ℝ) (s : ℝ), x + ∑ i, t i • EuclideanSpace.stdDirs N j i + s • v
        = x + ∑ i, (Fin.cons s t : Fin (j + 1) → ℝ) i • EuclideanSpace.stdDirs N (j + 1) i := by
      intro t s
      rw [EuclideanSpace.stdDirs_succ hj, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero, ← hv,
        add_assoc, add_comm (s • v)]
      simp only [Fin.cons_succ]
    have hpt : ∀ t : Fin j → ℝ, ‖iteratedFDeriv ℝ j φ (x + ∑ i, t i • EuclideanSpace.stdDirs N j i)
        (EuclideanSpace.stdDirs N j)‖ₑ ≤ ∫⁻ s : ℝ, ‖iteratedFDeriv ℝ (j + 1) φ
          (x + ∑ i, (Fin.cons s t : Fin (j + 1) → ℝ) i • EuclideanSpace.stdDirs N (j + 1) i)
          (EuclideanSpace.stdDirs N (j + 1))‖ₑ := fun t ↦ by
      refine (hg.enorm_le_lintegral_fderiv_line hgc hv0 _).trans (le_of_eq ?_)
      refine lintegral_congr fun s ↦ ?_
      rw [hfd, hsum]
    -- integrate in the remaining variables and use Fubini
    have hcont : Continuous fun y : Fin (j + 1) → ℝ ↦ iteratedFDeriv ℝ (j + 1) φ
        (x + ∑ i, y i • EuclideanSpace.stdDirs N (j + 1) i) :=
      (hφ.continuous_iteratedFDeriv (m := j + 1) (by simp)).comp
        (continuous_const.add (continuous_finsetSum _ fun i _ ↦
          (continuous_apply i).smul continuous_const))
    have hcont2 : Continuous fun y : Fin (j + 1) → ℝ ↦ iteratedFDeriv ℝ (j + 1) φ
        (x + ∑ i, y i • EuclideanSpace.stdDirs N (j + 1) i) (EuclideanSpace.stdDirs N (j + 1)) :=
      (ContinuousMultilinearMap.apply ℝ _ ℝ (EuclideanSpace.stdDirs N (j + 1))).continuous.comp
        hcont
    have hmeas : Measurable fun y : Fin (j + 1) → ℝ ↦ ‖iteratedFDeriv ℝ (j + 1) φ
        (x + ∑ i, y i • EuclideanSpace.stdDirs N (j + 1) i) (EuclideanSpace.stdDirs N (j + 1))‖ₑ :=
      (continuous_enorm.comp hcont2).measurable
    calc ∫⁻ t : Fin j → ℝ, ‖iteratedFDeriv ℝ j φ (x + ∑ i, t i • EuclideanSpace.stdDirs N j i)
          (EuclideanSpace.stdDirs N j)‖ₑ
        ≤ ∫⁻ t : Fin j → ℝ, ∫⁻ s : ℝ, ‖iteratedFDeriv ℝ (j + 1) φ
            (x + ∑ i, (Fin.cons s t : Fin (j + 1) → ℝ) i • EuclideanSpace.stdDirs N (j + 1) i)
            (EuclideanSpace.stdDirs N (j + 1))‖ₑ := lintegral_mono hpt
      _ = _ := (MeasureTheory.lintegral_fin_succ_eq hmeas).symm

end IteratedFTC

section Remark13

open SobolevMultiIndex
open scoped BoundedContinuousFunction

variable {N : ℕ}

/-- The product of the norms of the standard basis vectors $e_0, \dots, e_{N-1}$ of $\mathbb{R}^N$
is $1$. -/
theorem EuclideanSpace.prod_norm_stdDirs_self :
    ∏ i : Fin N, ‖EuclideanSpace.stdDirs N N i‖ = 1 := by
  simp [EuclideanSpace.stdDirs_self]

/-- Let $\varphi : \mathbb{R}^N \to \mathbb{R}$ be smooth with compact support. For every
$x \in \mathbb{R}^N$,
$$|\varphi(x)| \le \int_{\mathbb{R}^N} |\partial_1 \cdots \partial_N \varphi(y)| \, dy.$$
This is the bound of Remark 13 of [brezis2011functional], Chapter 9, for smooth functions.

The mixed derivative $\partial_1 \cdots \partial_N \varphi(y)$ is
$D^N \varphi(y)(e_0, \dots, e_{N-1})$. The proof is
`ContDiff.enorm_le_lintegral_iteratedFDeriv_stdDirs` at $j = N$, followed by the change of
variables $t \mapsto x + t$ in $\mathbb{R}^N$. -/
theorem ContDiff.enorm_le_lintegral_iteratedFDeriv_finrank {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (x : EuclideanSpace ℝ (Fin N)) :
    ‖φ x‖ₑ ≤ ∫⁻ y, ‖iteratedFDeriv ℝ N φ y (EuclideanSpace.stdDirs N N)‖ₑ := by
  refine (hφ.enorm_le_lintegral_iteratedFDeriv_stdDirs hφc x N le_rfl).trans (le_of_eq ?_)
  have hsum : ∀ t : Fin N → ℝ, ∑ i, t i • EuclideanSpace.stdDirs N N i = WithLp.toLp 2 t := by
    intro t
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (WithLp.toLp 2 t)]
    simp [EuclideanSpace.stdDirs_self]
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin N) ↦
      ‖iteratedFDeriv ℝ N φ (x + y) (EuclideanSpace.stdDirs N N)‖ₑ :=
    continuous_enorm.comp ((ContinuousMultilinearMap.apply ℝ _ ℝ _).continuous.comp
      ((hφ.continuous_iteratedFDeriv (m := N) (by simp)).comp (continuous_const.add continuous_id)))
  calc ∫⁻ t : Fin N → ℝ, ‖iteratedFDeriv ℝ N φ (x + ∑ i, t i • EuclideanSpace.stdDirs N N i)
        (EuclideanSpace.stdDirs N N)‖ₑ
      = ∫⁻ t : Fin N → ℝ, ‖iteratedFDeriv ℝ N φ (x + WithLp.toLp 2 t)
          (EuclideanSpace.stdDirs N N)‖ₑ := by simp_rw [hsum]
    _ = ∫⁻ y, ‖iteratedFDeriv ℝ N φ (x + y) (EuclideanSpace.stdDirs N N)‖ₑ :=
        (PiLp.volume_preserving_toLp (Fin N)).lintegral_comp hcont.measurable
    _ = ∫⁻ y, ‖iteratedFDeriv ℝ N φ y (EuclideanSpace.stdDirs N N)‖ₑ :=
        lintegral_add_left_eq_self (μ := volume)
          (fun y ↦ ‖iteratedFDeriv ℝ N φ y (EuclideanSpace.stdDirs N N)‖ₑ) x

/-- Let $T$ be a function on $\mathbb{R}^N$ with values in the continuous $N$-linear forms on
$\mathbb{R}^N$. Then
$$\int_{\mathbb{R}^N} |T(y)(e_0, \dots, e_{N-1})| \, dy \le \|T\|_1.$$
-/
theorem lintegral_enorm_apply_stdDirs_le_eLpNorm_one
    (T : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) [×N]→L[ℝ] ℝ) :
    ∫⁻ y, ‖T y (EuclideanSpace.stdDirs N N)‖ₑ ≤ eLpNorm T 1 volume := by
  refine (lintegral_mono fun y ↦ ?_).trans lintegral_enorm_le_eLpNorm_one
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa [EuclideanSpace.prod_norm_stdDirs_self] using (T y).le_opNorm (EuclideanSpace.stdDirs N N)

/-- **The embedding $W^{N,1}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$.** Every
$u \in W^{N,1}(\mathbb{R}^N)$ has a continuous representative $\tilde u$ with
$|\tilde u(x)| \le \|u\|$ for every $x$. This is Remark 13 of [brezis2011functional], Chapter 9.

The proof gives the finer bound $|\tilde u(x)| \le \|\partial_1 \cdots \partial_N u\|_1 \le
\|u\|$. For $\varphi \in C_c^\infty$, $|\varphi(x)| \le \int |\partial_1 \cdots \partial_N
\varphi|$ by `ContDiff.enorm_le_lintegral_iteratedFDeriv_finrank`. So the smooth approximants of
$u$ in $W^{N,1}(\mathbb{R}^N)$ (`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`)
are uniformly Cauchy. Their uniform limit is continuous, equals $u$ almost everywhere, and
satisfies the bound. -/
theorem SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one
    (u : SobolevEuclidean N N 1 ⊤) :
    ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧ fn u =ᵐ[volume] ũ ∧ ∀ x, ‖ũ x‖ ≤ ‖u‖ := by
  -- the tensor weak derivative of order `N` and its mixed component `∂_1 ⋯ ∂_N u`
  have hmem : MemSobolev (fn u) N 1 ⊤ volume := (memSobolevMultiIndex u).memSobolev
  obtain ⟨w, hw, hwp⟩ := hmem.2 N le_rfl
  rw [Measure.restrict_coe_top] at hwp
  obtain ⟨α₁, hα₁⟩ : ∃ α₁ : MultiIndexLE (Fin N) N,
      α₁ = ⟨multiIndexCount (id : Fin N → Fin N), (sum_multiIndexCount _).le⟩ := ⟨_, rfl⟩
  have hperm : (List.ofFn (multiIndexTuple
      ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) α₁.1)).Perm
      (List.ofFn (EuclideanSpace.stdDirs N N)) := by
    rw [hα₁, ← multiIndexDirections_eq_ofFn]
    refine (multiIndexDirections_multiIndexCount_perm _ id).symm.trans (List.Perm.of_eq ?_)
    congr 1
    funext i
    simp [EuclideanSpace.stdDirs_self]
  have hmixed : (fun y ↦ w y (EuclideanSpace.stdDirs N N)) =ᵐ[volume] weakDeriv u α₁ := by
    have h1 : HasWeakIteratedLineDerivOn (EuclideanSpace.stdDirs N N) (fn u)
        (fun y ↦ w y (EuclideanSpace.stdDirs N N)) ⊤ volume :=
      HasWeakIteratedFDerivOn.lineDeriv hw _
    have h2 : HasWeakIteratedLineDerivOn (EuclideanSpace.stdDirs N N) (fn u)
        (weakDeriv u α₁) ⊤ volume :=
      (hasWeakIteratedLineDerivOn u α₁).of_perm hperm
    filter_upwards [h1.ae_eq h2] with x hx
    exact hx (by simp)
  have hmixed_norm : ∫⁻ y, ‖w y (EuclideanSpace.stdDirs N N)‖ₑ ≤ ENNReal.ofReal ‖u‖ := by
    calc ∫⁻ y, ‖w y (EuclideanSpace.stdDirs N N)‖ₑ
        = ∫⁻ y, ‖weakDeriv u α₁ y‖ₑ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hmixed] with y hy
          rw [hy]
      _ = ENNReal.ofReal ‖weakDeriv u α₁‖ := by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_restrict_coe_top,
            eLpNorm_one_eq_lintegral_enorm (by
              simpa only [Measure.restrict_coe_top] using Lp.aestronglyMeasurable (weakDeriv u α₁))]
      _ ≤ ENNReal.ofReal ‖u‖ := ENNReal.ofReal_le_ofReal (norm_weakDeriv_le u α₁)
  have hwmeas : AEMeasurable (fun y ↦ ‖w y (EuclideanSpace.stdDirs N N)‖ₑ) volume :=
    ((ContinuousMultilinearMap.apply ℝ _ ℝ (EuclideanSpace.stdDirs N N)).continuous
      |>.comp_aestronglyMeasurable hwp.aestronglyMeasurable).enorm
  -- the smooth approximants and the two quantities controlling them
  obtain ⟨v, hvs, hvc, hvt⟩ := hmem.exists_seq_hasCompactSupport_tendsto_sobolevNorm le_rfl
    ENNReal.one_ne_top
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ≥0∞,
      D = fun n ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ N (v n) x - w x) 1 volume := ⟨_, rfl⟩
  have hvD : Tendsto D atTop (𝓝 0) := by
    rw [hD]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvt (fun _ ↦ zero_le)
      fun n ↦ ?_
    have hsub : HasWeakIteratedFDerivOn N (v n - fn u)
        (iteratedFDeriv ℝ N (v n) - w) ⊤ volume :=
      ((hvs n).contDiffOn.hasWeakIteratedFDerivOn (by simp)).sub hw
    exact hsub.eLpNorm_le_sobolevNorm_top le_rfl ENNReal.one_ne_top le_rfl
  have hv0 : Tendsto (fun n ↦ eLpNorm (v n - fn u) 1 volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvt (fun _ ↦ zero_le)
      fun n ↦ ?_
    have hloc : LocallyIntegrable (v n - fn u) volume :=
      ((hvs n).continuous.locallyIntegrable).sub
        ((SobolevEuclidean.memLp_fn u).locallyIntegrable le_rfl)
    have h0 := (hasWeakIteratedFDerivOn_zero (μ := volume) (Ω := ⊤)
      (locallyIntegrableOn_univ.2 hloc)).eLpNorm_le_sobolevNorm_top le_rfl ENNReal.one_ne_top
      (Nat.zero_le N)
    refine le_trans ?_ h0
    refine eLpNorm_mono_enorm_ae hloc.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map]
  -- the sup bound for one approximant and for a difference of two
  have hmixed_le : ∀ n, ∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ
      ≤ D n := fun n ↦ by
    rw [hD]
    exact lintegral_enorm_apply_stdDirs_le_eLpNorm_one fun y ↦ iteratedFDeriv ℝ N (v n) y - w y
  have hvmeas : ∀ n, AEMeasurable
      (fun y ↦ ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ) volume := by
    intro n
    have h1 : AEStronglyMeasurable (fun y ↦ iteratedFDeriv ℝ N (v n) y - w y) volume :=
      ((hvs n).continuous_iteratedFDeriv (m := N) (by simp)).aestronglyMeasurable.sub
        hwp.aestronglyMeasurable
    exact ((ContinuousMultilinearMap.apply ℝ _ ℝ (EuclideanSpace.stdDirs N N)).continuous
      |>.comp_aestronglyMeasurable h1).enorm
  have hbound : ∀ n x, ‖v n x‖ₑ ≤ D n + ENNReal.ofReal ‖u‖ := fun n x ↦ by
    refine ((hvs n).enorm_le_lintegral_iteratedFDeriv_finrank (hvc n) x).trans ?_
    calc ∫⁻ y, ‖iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)‖ₑ
        ≤ ∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ
          + ‖w y (EuclideanSpace.stdDirs N N)‖ₑ := by
          refine lintegral_mono fun y ↦ ?_
          rw [sub_apply]
          calc ‖iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)‖ₑ
              = ‖iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)
                  - w y (EuclideanSpace.stdDirs N N) + w y (EuclideanSpace.stdDirs N N)‖ₑ := by
                rw [sub_add_cancel]
            _ ≤ _ := enorm_add_le _ _
      _ = (∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ)
          + ∫⁻ y, ‖w y (EuclideanSpace.stdDirs N N)‖ₑ := lintegral_add_right' _ hwmeas
      _ ≤ D n + ENNReal.ofReal ‖u‖ := add_le_add (hmixed_le n) hmixed_norm
  have hdiff : ∀ n m x, ‖v n x - v m x‖ₑ ≤ D n + D m := fun n m x ↦ by
    have hs : ContDiff ℝ ∞ (v n - v m) := (hvs n).sub (hvs m)
    have hc : HasCompactSupport (v n - v m) := (hvc n).sub (hvc m)
    refine (hs.enorm_le_lintegral_iteratedFDeriv_finrank hc x).trans ?_
    rw [iteratedFDeriv_sub ((hvs n).of_le (by simp)) ((hvs m).of_le (by simp))]
    calc ∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) - iteratedFDeriv ℝ N (v m)) y
          (EuclideanSpace.stdDirs N N)‖ₑ
        ≤ ∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ
          + ‖(iteratedFDeriv ℝ N (v m) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ := by
          refine lintegral_mono fun y ↦ ?_
          simp only [Pi.sub_apply, sub_apply]
          calc ‖iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)
                - iteratedFDeriv ℝ N (v m) y (EuclideanSpace.stdDirs N N)‖ₑ
              = ‖(iteratedFDeriv ℝ N (v n) y (EuclideanSpace.stdDirs N N)
                  - w y (EuclideanSpace.stdDirs N N))
                - (iteratedFDeriv ℝ N (v m) y (EuclideanSpace.stdDirs N N)
                  - w y (EuclideanSpace.stdDirs N N))‖ₑ := by rw [sub_sub_sub_cancel_right]
            _ ≤ _ := enorm_sub_le
      _ = (∫⁻ y, ‖(iteratedFDeriv ℝ N (v n) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ)
          + ∫⁻ y, ‖(iteratedFDeriv ℝ N (v m) y - w y) (EuclideanSpace.stdDirs N N)‖ₑ :=
          lintegral_add_left' (hvmeas n) _
      _ ≤ D n + D m := add_le_add (hmixed_le n) (hmixed_le m)
  -- the approximants as bounded continuous functions, Cauchy in the sup norm
  choose M hM using fun n ↦ (hvc n).exists_bound_of_continuous (hvs n).continuous
  obtain ⟨U, hU⟩ : ∃ U : ℕ → EuclideanSpace ℝ (Fin N) →ᵇ ℝ, ∀ n x, U n x = v n x :=
    ⟨fun n ↦ BoundedContinuousFunction.ofNormedAddCommGroup (v n) (hvs n).continuous (M n) (hM n),
      fun n x ↦ rfl⟩
  have hcauchy : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ0, hδt, hδ⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧ δ ≠ ⊤ ∧ (δ + δ).toReal < ε := by
      refine ⟨ENNReal.ofReal (ε / 4), ENNReal.ofReal_pos.2 (by positivity), ENNReal.ofReal_ne_top,
        ?_⟩
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.toReal_ofReal (by positivity)]
      linarith
    obtain ⟨N₀, hN₀⟩ := (ENNReal.tendsto_nhds_zero.1 hvD δ hδ0).exists_forall_of_atTop
    refine ⟨N₀, fun m hm n hn ↦ ?_⟩
    have hb : dist (U m) (U n) ≤ (δ + δ).toReal := by
      refine (BoundedContinuousFunction.dist_le ENNReal.toReal_nonneg).2 fun x ↦ ?_
      rw [hU, hU, dist_eq_norm, ← toReal_enorm]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hδt, hδt⟩)
        ((hdiff m n x).trans (add_le_add (hN₀ m hm) (hN₀ n hn)))
    exact hb.trans_lt hδ
  -- the uniform limit
  obtain ⟨Ũ, hŨ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hpt : ∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (Ũ x)) := fun x ↦ by
    have := ((continuous_eval_const x).tendsto Ũ).comp hŨ
    simpa only [Function.comp_def, hU] using this
  refine ⟨Ũ, Ũ.continuous, ?_, fun x ↦ ?_⟩
  -- it equals `u` almost everywhere
  · have hmeas : TendstoInMeasure volume v atTop (fn u) :=
      tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hv0
    obtain ⟨ns, hns_mono, hns⟩ := hmeas.exists_seq_tendsto_ae
    filter_upwards [hns] with x hx
    exact tendsto_nhds_unique hx ((hpt x).comp hns_mono.tendsto_atTop)
  -- the sup bound
  · rw [← ENNReal.ofReal_le_ofReal_iff (norm_nonneg _), ofReal_norm]
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    have hlim : Tendsto (fun n ↦ ‖v n x‖ₑ) atTop (𝓝 ‖Ũ x‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hpt x)
    refine le_of_tendsto hlim ?_
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hvD δ (by exact_mod_cast hδ)] with n hn
    calc ‖v n x‖ₑ ≤ D n + ENNReal.ofReal ‖u‖ := hbound n x
      _ ≤ ENNReal.ofReal ‖u‖ + δ := by rw [add_comm]; exact add_le_add le_rfl hn

end Remark13

/-!
### Gagliardo's lemma in its general form

This is Lemma 9.4 of [brezis2011functional].
-/

section Gagliardo

/-- **Gagliardo's lemma for $N = 2$.** For measurable $f_0, f_1 : \mathbb{R} \to [0, \infty]$,
$$\int_{\mathbb{R}^2} f_0(x_1) f_1(x_0) \, dx = \int_{\mathbb{R}} f_0 \int_{\mathbb{R}} f_1.$$
This is the case $N = 2$ of Lemma 9.4 of [brezis2011functional].

Here $x = (x_0, x_1)$, and $f_i$ is applied to $x$ with its $i$-th coordinate omitted,
`x ∘ i.succAbove`, a function on `Fin 1`. -/
theorem MeasureTheory.lintegral_prod_comp_succAbove_two
    (f : Fin 2 → (Fin 1 → ℝ) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x ∘ i.succAbove) = ∏ i, ∫⁻ y, f i y := by
  have hG : Measurable fun x : Fin 2 → ℝ ↦ ∏ i, f i (x ∘ i.succAbove) :=
    Finset.measurable_prod _ fun i _ ↦ (hf i).comp (measurable_comp_succAbove i)
  rw [lintegral_fin_succ_eq' hG, Fin.prod_univ_two]
  have h1 : ∀ s : ℝ, ∫⁻ t : Fin 1 → ℝ, ∏ i, f i (Fin.cons s t ∘ i.succAbove)
      = (∫⁻ t, f 0 t) * f 1 (Fin.cons s Fin.elim0) := by
    intro s
    rw [← lintegral_mul_const _ (hf 0)]
    refine lintegral_congr fun t ↦ ?_
    rw [Fin.prod_univ_two, Fin.comp_zero_succAbove]
    have e0 : Fin.cons s t ∘ Fin.succ = t := by
      ext k
      simp
    have e1 : Fin.cons s t ∘ (1 : Fin 2).succAbove = Fin.cons s Fin.elim0 := by
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.comp_succ_succAbove, Fin.cons_zero]
      congr
      ext k
      exact k.elim0
    rw [e0, e1]
  simp_rw [h1]
  rw [lintegral_const_mul (f := fun s ↦ f 1 (Fin.cons s Fin.elim0)) _ ((hf 1).comp
    (measurable_fin_cons_prod.comp (measurable_id.prodMk measurable_const)))]
  congr 1
  rw [lintegral_fin_succ_eq' (hf 1)]
  refine lintegral_congr fun s ↦ ?_
  rw [lintegral_fin_zero]

/-- **The inductive step of Gagliardo's lemma.** Let $n$ be a natural number, and suppose that
Gagliardo's lemma holds for $n + 2$ functions of $n + 1$ variables: for all measurable
$g_i : \mathbb{R}^{n+1} \to [0, \infty]$, $i < n + 2$,
$$\int_{\mathbb{R}^{n+2}} \prod_i g_i(\tilde x_i) \, dx \le \prod_i
  \|g_i\|_{L^{n+1}(\mathbb{R}^{n+1})},$$
where $\tilde x_i$ is $x$ with its $i$-th coordinate omitted. Then the same inequality holds for
$n + 3$ measurable functions $f_i : \mathbb{R}^{n+2} \to [0, \infty]$, with the norms of
$L^{n+2}(\mathbb{R}^{n+2})$. This is the induction of the proof of Lemma 9.4 of
[brezis2011functional].

Write $N = n + 2$ and $N' = N/(N - 1)$. Fix the first coordinate $s$ by Fubini's theorem
(`MeasureTheory.lintegral_fin_succ_eq'`). For fixed $s$ the factor $f_0$ does not depend on $s$,
and Hölder's inequality with the exponents $N$ and $N'$ separates it from the product of the
other $N$ factors. The induction hypothesis applies to these with the functions
$f_i(s, \cdot)^{N'}$. Then integrate in $s$: each $s \mapsto \|f_i(s, \cdot)\|_{L^N}$ lies in
$L^N(\mathbb{R})$, and the generalized Hölder inequality for $N$ factors
(`ENNReal.lintegral_prod_norm_pow_le`) and Fubini's theorem conclude. -/
theorem MeasureTheory.lintegral_prod_comp_succAbove_le_succ {n : ℕ}
    (ih : ∀ f : Fin (n + 2) → (Fin (n + 1) → ℝ) → ℝ≥0∞, (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x ∘ i.succAbove)
        ≤ ∏ i, (∫⁻ y, f i y ^ ((n : ℝ) + 1)) ^ (1 / ((n : ℝ) + 1)))
    (f : Fin (n + 3) → (Fin (n + 2) → ℝ) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x ∘ i.succAbove)
      ≤ ∏ i, (∫⁻ y, f i y ^ ((n : ℝ) + 2)) ^ (1 / ((n : ℝ) + 2)) := by
  -- the exponents
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (n : ℝ) + 2 := ⟨_, rfl⟩
  have hq1 : 1 < q := by rw [hq]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨q', hq'⟩ : ∃ q' : ℝ, q' = Real.conjExponent q := ⟨_, rfl⟩
  have hqq' : q.HolderConjugate q' := hq' ▸ Real.HolderConjugate.conjExponent hq1
  have hq'0 : 0 < q' := hqq'.symm.pos
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hq2 : q - 1 = (n : ℝ) + 1 := by rw [hq]; ring
  have hq'n : q' * ((n : ℝ) + 1) = q := by
    rw [hq', Real.conjExponent, hq2, div_mul_cancel₀ _ hn1.ne']
  rw [← hq]
  -- measurability
  have hG : Measurable fun x : Fin (n + 3) → ℝ ↦ ∏ i, f i (x ∘ i.succAbove) :=
    Finset.measurable_prod _ fun i _ ↦ (hf i).comp (measurable_comp_succAbove i)
  have hg : ∀ (s : ℝ) (j : Fin (n + 2)), Measurable fun y : Fin (n + 1) → ℝ ↦
      f (Fin.succ j) (Fin.cons s y) := fun s j ↦ (hf _).comp (measurable_fin_cons_const s)
  have hF : ∀ j : Fin (n + 2), Measurable fun s : ℝ ↦
      ∫⁻ y : Fin (n + 1) → ℝ, f (Fin.succ j) (Fin.cons s y) ^ q := fun j ↦
    Measurable.lintegral_prod_right (((hf _).comp measurable_fin_cons_prod).pow_const q)
  -- Step A: Fubini, the first coordinate outermost, and the product split
  rw [lintegral_fin_succ_eq' hG]
  have hsplit : ∀ (s : ℝ) (t : Fin (n + 2) → ℝ), ∏ i, f i (Fin.cons s t ∘ i.succAbove)
      = f 0 t * ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove)) := by
    intro s t
    rw [Fin.prod_univ_succ, Fin.comp_zero_succAbove]
    have e0 : Fin.cons s t ∘ Fin.succ = t := by
      ext k
      simp
    rw [e0]
    congr 1
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Fin.comp_succ_succAbove, Fin.cons_zero, e0]
  simp_rw [hsplit]
  -- Step B: the inner integral, by Hölder and the induction hypothesis
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ≥0∞, A₀ = (∫⁻ t, f 0 t ^ q) ^ (1 / q) := ⟨_, rfl⟩
  have hinner : ∀ s : ℝ, ∫⁻ t : Fin (n + 2) → ℝ,
      f 0 t * ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove))
      ≤ A₀ * ∏ j : Fin (n + 2),
        (∫⁻ y : Fin (n + 1) → ℝ, f (Fin.succ j) (Fin.cons s y) ^ q) ^ (1 / q) := by
    intro s
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hqq' (f := f 0)
      (g := fun t ↦ ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove)))
      (hf 0).aemeasurable
      (Finset.measurable_prod (Finset.univ : Finset (Fin (n + 2))) fun j _ ↦
        (hg s j).comp (measurable_comp_succAbove j)).aemeasurable
    refine hH.trans ?_
    rw [hA₀]
    refine mul_le_mul' le_rfl ?_
    -- the induction hypothesis on the functions `f (succ j) (cons s ·) ^ q'`
    have hIH := ih (fun j y ↦ f (Fin.succ j) (Fin.cons s y) ^ q') fun j ↦ (hg s j).pow_const q'
    have e1 : ∀ t : Fin (n + 2) → ℝ,
        (∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove))) ^ q'
          = ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove)) ^ q' := fun t ↦
      (ENNReal.prod_rpow_of_nonneg hq'0.le).symm
    have e2 : ∫⁻ t : Fin (n + 2) → ℝ,
        (∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove))) ^ q'
          = ∫⁻ t : Fin (n + 2) → ℝ,
            ∏ j : Fin (n + 2), f (Fin.succ j) (Fin.cons s (t ∘ j.succAbove)) ^ q' :=
      lintegral_congr e1
    rw [e2]
    refine (ENNReal.rpow_le_rpow hIH (by positivity)).trans_eq ?_
    rw [← ENNReal.prod_rpow_of_nonneg (by positivity)]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← ENNReal.rpow_mul]
    congr 1
    · refine lintegral_congr fun y ↦ ?_
      rw [← ENNReal.rpow_mul, hq'n]
    · rw [hq', Real.conjExponent, hq2, hq]
      field_simp
  -- Step C: the outer integral, by the generalized Hölder inequality
  refine (lintegral_mono hinner).trans ?_
  rw [lintegral_const_mul _ (Finset.measurable_prod _ fun j _ ↦ (hF j).pow_const _)]
  rw [Fin.prod_univ_succ, ← hA₀]
  refine mul_le_mul' le_rfl ?_
  have hHolder := ENNReal.lintegral_prod_norm_pow_le (μ := volume) Finset.univ
    (f := fun j s ↦ ∫⁻ y : Fin (n + 1) → ℝ, f (Fin.succ j) (Fin.cons s y) ^ q)
    (fun j _ ↦ (hF j).aemeasurable) (p := fun _ ↦ 1 / q) ?_ fun _ _ ↦ by positivity
  · refine hHolder.trans_eq ?_
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [lintegral_fin_succ_eq' ((hf _).pow_const q)]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hq]
    push_cast
    field_simp

/-- **Gagliardo's lemma.** Let $N = n + 2 \ge 2$, and let $f_i : \mathbb{R}^{N-1} \to [0, \infty]$,
$i < N$, be measurable. For $x \in \mathbb{R}^N$ let $\tilde x_i \in \mathbb{R}^{N-1}$ be $x$
with its $i$-th coordinate omitted. Then
$$\int_{\mathbb{R}^N} \prod_i f_i(\tilde x_i) \, dx \le \prod_i
  \|f_i\|_{L^{N-1}(\mathbb{R}^{N-1})}.$$
In particular the product is integrable when every $f_i$ lies in $L^{N-1}(\mathbb{R}^{N-1})$.
This is Lemma 9.4 of [brezis2011functional].

The point $\tilde x_i$ is `x ∘ i.succAbove`. The case $N = 2$ is
`MeasureTheory.lintegral_prod_comp_succAbove_two`, and the induction on $N$ is
`MeasureTheory.lintegral_prod_comp_succAbove_le_succ`. Mathlib's
`MeasureTheory.lintegral_prod_lintegral_pow_le` is the special case $f_i(\tilde x_i) = (\int
f(x_1, \dots, t, \dots, x_N) \, dt)^{1/(N-1)}$ for a single $f$, with $t$ in the $i$-th place,
which is all that Theorem 9.9 needs. -/
theorem MeasureTheory.lintegral_prod_comp_succAbove_le {n : ℕ}
    (f : Fin (n + 2) → (Fin (n + 1) → ℝ) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x ∘ i.succAbove)
      ≤ ∏ i, (∫⁻ y, f i y ^ ((n : ℝ) + 1)) ^ (1 / ((n : ℝ) + 1)) := by
  induction n with
  | zero =>
    rw [lintegral_prod_comp_succAbove_two f hf]
    simp
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [e]
    exact lintegral_prod_comp_succAbove_le_succ ih f hf

end Gagliardo
