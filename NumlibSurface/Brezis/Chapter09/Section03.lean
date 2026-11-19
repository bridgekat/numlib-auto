/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.Sobolev.Compactness
import NumlibSurface.Brezis.Chapter09.Section02

/-!
# Brezis, Section 9.3: Sobolev inequalities

This module formalizes Section 9.3 of [brezis2011functional], the Sobolev embedding theorems in
$\mathbb{R}^N$ with Lebesgue measure. Part A treats $\Omega = \mathbb{R}^N$: the
Sobolev–Gagliardo–Nirenberg inequality $\|u\|_{p^*} \le C \|\nabla u\|_p$ for $1 \le p < N$ and
$1/p^* = 1/p - 1/N$ (Theorem 9.9, with Gagliardo's Lemma 9.4 and the scaling argument of Remark 10),
its consequences for $p \le q \le p^*$ and $p = N$ (Corollaries 9.10 and 9.11), Morrey's theorem for
$p > N$ (Theorem 9.12 and Remarks 11–12), and the embeddings of $W^{m,p}(\mathbb{R}^N)$ (Corollary
9.13 and Remark 13). Part B treats an open set $\Omega$ of class $C^1$ with bounded boundary, or the
half space $\mathbb{R}^N_+$: the same embeddings for $W^{1,p}(\Omega)$ and $W^{m,p}(\Omega)$ through
the extension operator of Section 9.2 (Corollaries 9.14 and 9.15), the Rellich–Kondrachov theorem
for bounded $\Omega$ (Theorem 9.16), and Remarks 14–16.

The proofs specialize the backbone modules `Numlib.Analysis.Sobolev.Embedding` (the whole space),
`Numlib.Analysis.Sobolev.EmbeddingDomain` (the domain, through the extension operator) and
`Numlib.Analysis.Sobolev.Compactness` (Theorem 9.16). Below, $\|u\|$ is the norm of the Lean type of
$W^{1,p}(\Omega)$, $\|u\|_{W^{1,p}} = \|u\|_p + \sum_i \|\partial u / \partial x_i\|_p$ is the norm
of the source (`Brezis.Chapter09.bookNorm`), and $\|\nabla u\|_p$ is the $L^p$ norm of the Euclidean
length of the gradient.

## Main definitions

* Section 9.3, "with continuous injection", `Brezis.Chapter09.IsContinuousInjectionLp`: every
  $u \in W^{m,p}(\Omega)$ lies in $L^q(\Omega)$, and the inclusion $W^{m,p}(\Omega) \to L^q(\Omega)$
  is an injective bounded linear map.
* Section 9.3, "with compact injection", `Brezis.Chapter09.IsCompactInjectionLp`: the inclusion
  $W^{m,p}(\Omega) \to L^q(\Omega)$ is a compact embedding.
* Section 9.3.B, the standing hypothesis, `Brezis.Chapter09.IsClassC1BoundedFrontierOrHalfSpace`:
  $\Omega$ is of class $C^1$ with bounded boundary, or $\Omega = \mathbb{R}^N_+$.
* Theorem 9.16, the injection $W^{1,p}(\Omega) \subset C(\bar\Omega)$,
  `Brezis.Chapter09.toContinuousMapClosure`: for bounded $\Omega$ of class $C^1$ and $p > N$, the
  map that sends $u$ to the restriction to $\bar\Omega$ of its continuous representative.

## Main results

* Lemma 9.4, `Brezis.Chapter09.lemma_9_4`: $\|f_1(\tilde x_1) \cdots f_N(\tilde
  x_N)\|_{L^1(\mathbb{R}^N)} \le \prod_i \|f_i\|_{L^{N-1}(\mathbb{R}^{N-1})}$.
* Theorem 9.9, `Brezis.Chapter09.theorem_9_9`: for $1 \le p < N$, $W^{1,p}(\mathbb{R}^N) \subset
  L^{p^*}(\mathbb{R}^N)$ with $\|u\|_{p^*} \le C \|\nabla u\|_p$.
* Remark 10, `Brezis.Chapter09.remark_9_10`: an inequality $\|u\|_q \le C \|\nabla u\|_p$ on
  $C_c^\infty(\mathbb{R}^N)$ forces $1/q = 1/p - 1/N$.
* Corollary 9.10, `Brezis.Chapter09.corollary_9_10`: for $1 \le p < N$, $W^{1,p}(\mathbb{R}^N)
  \subset L^q(\mathbb{R}^N)$ for $q \in [p, p^*]$.
* Corollary 9.11, `Brezis.Chapter09.corollary_9_11`: for $N \ge 2$, $W^{1,N}(\mathbb{R}^N) \subset
  L^q(\mathbb{R}^N)$ for $q \in [N, \infty)$.
* Theorem 9.12, `Brezis.Chapter09.theorem_9_12`: for $N < p < \infty$, $W^{1,p}(\mathbb{R}^N)
  \subset L^\infty(\mathbb{R}^N)$, and $u$ is Hölder continuous with exponent $1 - N/p$; the parts
  are `Brezis.Chapter09.theorem_9_12_top_le` and `Brezis.Chapter09.theorem_9_12_holder`, and the
  case $p = \infty$ is `Brezis.Chapter09.theorem_9_12_top`.
* Remark 11, `Brezis.Chapter09.remark_9_11`: for $p > N$, $u \in W^{1,p}(\mathbb{R}^N)$ has a unique
  continuous representative.
* Remark 12, `Brezis.Chapter09.remark_9_12`: for $p > N$, the continuous representative tends to $0$
  at infinity.
* Corollary 9.13, `Brezis.Chapter09.corollary_9_13`: the embeddings of $W^{m,p}(\mathbb{R}^N)$ into
  $L^q$, $L^\infty$ and $C^k$; the clauses are `Brezis.Chapter09.corollary_9_13_lt`,
  `Brezis.Chapter09.corollary_9_13_eq`, `Brezis.Chapter09.corollary_9_13_gt` and
  `Brezis.Chapter09.corollary_9_13_holder`.
* Remark 13, `Brezis.Chapter09.remark_9_13`: $W^{N,1}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$,
  with a continuous representative.
* Corollary 9.14, `Brezis.Chapter09.corollary_9_14`: the conclusions of Theorems 9.9 and 9.12 on
  $\Omega$; the cases are `Brezis.Chapter09.corollary_9_14_lt`,
  `Brezis.Chapter09.corollary_9_14_eq`, `Brezis.Chapter09.corollary_9_14_gt` and
  `Brezis.Chapter09.corollary_9_14_holder`.
* Corollary 9.15, `Brezis.Chapter09.corollary_9_15`: the conclusion of Corollary 9.13 on $\Omega$,
  with $C^k(\bar\Omega)$; the parts are `Brezis.Chapter09.corollary_9_15_lp` and
  `Brezis.Chapter09.corollary_9_15_ck`.
* Theorem 9.16 (Rellich–Kondrachov), `Brezis.Chapter09.theorem_9_16`: for bounded $\Omega$ of class
  $C^1$, the compact injections of $W^{1,p}(\Omega)$; the cases are
  `Brezis.Chapter09.theorem_9_16_lt`, `Brezis.Chapter09.theorem_9_16_eq`,
  `Brezis.Chapter09.theorem_9_16_gt` and `Brezis.Chapter09.theorem_9_16_self`.
* Remark 14 (i), `Brezis.Chapter09.remark_9_14_i`: the injection $W^{1,p}(\mathbb{R}^N) \subset
  L^p(\mathbb{R}^N)$ is not compact.
* Remark 15, `Brezis.Chapter09.remark_9_15`: for bounded $\Omega$ of class $C^1$,
  $\|\nabla u\|_p + \|u\|_q$ is a norm on $W^{1,p}(\Omega)$ equivalent to $\|u\|_{W^{1,p}}$; the
  cases are `Brezis.Chapter09.remark_9_15_lt`, `Brezis.Chapter09.remark_9_15_eq` and
  `Brezis.Chapter09.remark_9_15_gt`.
* Remark 16, `Brezis.Chapter09.remark_9_16`: a function of $W^{1,N}$ of a ball that is not bounded.

## Conventions

* The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)` with Lebesgue measure, and
  $\Omega = \mathbb{R}^N$ is the open set `⊤`. In Part B the dimension is written $N = d + 1$, as in
  Section 9.2.
* The exponent $p^* = Np/(N - p)$ is given by its defining equation $1/p^* = 1/p - 1/N$. Finite
  exponents have the type `ℝ≥0`, and the hypothesis $1 \le p$ is the instance
  `[Fact (1 ≤ (p : ℝ≥0∞))]`.
* $\|\nabla u\|_p$ is `eLpNorm (Brezis.Chapter09.gradient u) p`. The norms $\|u\|_{W^{1,p}}$ and
  $\|u\|_{W^{m,p}}$ of the source are `Brezis.Chapter09.bookNorm` and
  `Brezis.Chapter09.bookNormHigher`.
* An estimate that the source states for almost every $x$ and $y$ is stated for a continuous
  representative at every $x$ and $y$, and also in the literal form "for a.e. $x$, for a.e. $y$".

## Implementation notes

* The backbone measures the gradient by the $\ell^p$ norm `SobolevMultiIndex.gradNorm u`
  $= (\sum_i \|\partial_i u\|_p^p)^{1/p}$. The lemmas of the section on the gradient norm compare it
  with the Euclidean norm $\|\nabla u\|_p$ of the source, up to the factor $N$.
* The standing hypothesis of Part B is used only through the extension operator.
  `Brezis.Chapter09.IsClassC1BoundedFrontierOrHalfSpace.isSobolevExtensionDomainAll` turns it into
  the backbone hypothesis `IsSobolevExtensionDomainAll`.

## Deviations from the source

* **Theorem 9.9 and Remark 10** (reading). The theorem states an existential embedding constant.
  Remark 10 uses a finite Sobolev exponent and states the scaling conclusion in reciprocal form.
  See `Brezis.Chapter09.theorem_9_9` and `Brezis.Chapter09.remark_9_10`.
* **Theorem 9.12 and Corollaries 9.13–9.15** (reading). The Hölder estimates use continuous
  representatives, and the higher-order estimates use the norm of the iterated Fréchet derivative.
  See `Brezis.Chapter09.theorem_9_12_holder` and `Brezis.Chapter09.corollary_9_13_holder`.
* **Corollary 9.14** (generalization). The subcritical embedding includes every exponent from
  $p$ to $p^*$. See `Brezis.Chapter09.corollary_9_14_lt`.
* **Corollary 9.14, Theorem 9.16 and Remark 15** (reading). The domain statements use finite
  Sobolev exponents. See `Brezis.Chapter09.corollary_9_14`, `Brezis.Chapter09.theorem_9_16`
  and `Brezis.Chapter09.remark_9_15`.
* **Remarks 13–14** (reading). The library gives the positive $W^{N,1}$ embedding with a
  continuous representative and proves noncompactness on the whole space. See
  `Brezis.Chapter09.remark_9_13` and `Brezis.Chapter09.remark_9_14_i`.
* **Corollary 9.11** (reading). The corollary is stated for $N \ge 2$, which the proof of the source
  uses. The case $N = 1$ is a case of Theorem 8.8. See `Brezis.Chapter09.corollary_9_11`.
* **Corollary 9.13** (reading). The corollary is stated with the hypothesis $N \ge 2$ or $p > 1$,
  which the proof by repeated application of Theorem 9.9, Corollary 9.11 and Theorem 9.12 needs. See
  `Brezis.Chapter09.corollary_9_13`.
* **Corollary 9.13, Sobolev order** (generalization). The statement includes order $m = 0$,
  for which the subcritical embedding is the identity on $L^p$. See
  `Brezis.Chapter09.corollary_9_13`.
* **Corollary 9.14, case $p = N$** (reading). The case is stated for $N \ge 2$, as Corollary 9.11.
  See `Brezis.Chapter09.corollary_9_14_eq`.
* **Corollary 9.15** (reading). The corollary has the hypothesis $N \ge 2$ or $p > 1$, as Corollary
  9.13. See `Brezis.Chapter09.corollary_9_15`.
* **Theorem 9.16, case $p = N$ and last sentence** (reading). The case $p = N$ is stated for
  $N \ge 2$, and the compactness of $W^{1,p}(\Omega) \subset L^p(\Omega)$ for $p \ne 1$ or
  $N \ge 2$. The case $N = p = 1$ is Theorem 8.8. See `Brezis.Chapter09.theorem_9_16_eq` and
  `Brezis.Chapter09.theorem_9_16_self`.
* **Remark 15, case $p = N$** (reading). The case is stated for $N \ge 2$. See
  `Brezis.Chapter09.remark_9_15_eq`.

## Not formalized

* **Footnote 9.** The explicit constant $(N - 1)p/(N - p)$ of Theorem 9.9.
* **Corollary 9.14, case $p = \infty$.** It is Theorem 9.12 for $p = \infty$ on $\mathbb{R}^N$
  (`Brezis.Chapter09.theorem_9_12_top`) and is not restated on $\Omega$.
* **Remark 13, negative clause.** In general $W^{m,p}(\mathbb{R}^N) \not\subset
  L^\infty(\mathbb{R}^N)$ for $p > 1$ and $m = N/p$.
* **Remark 14 (ii).** The injection $W^{1,p}(\Omega) \subset L^{p^*}(\Omega)$ is never compact.
* **Remark 16, Trudinger's inequality.** The source quotes it without proof.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal

namespace Brezis.Chapter09

/-! ### Continuous and compact injections into $L^q(\Omega)$ -/

/-- **Section 9.3** of [brezis2011functional], the phrase "with continuous injection". Let
$m \in \mathbb{N}$, $1 \le p, q \le \infty$ and let $\Omega \subseteq \mathbb{R}^N$ be open.
Then **$W^{m,p}(\Omega) \subset L^q(\Omega)$ with continuous injection** if every function of
$W^{m,p}(\Omega)$ lies in $L^q(\Omega)$ and the inclusion $W^{m,p}(\Omega) \to L^q(\Omega)$,
$u \mapsto u$, is a continuous embedding: an injective bounded linear map.

The inclusion is `SobolevMultiIndex.toLpₗ`, and the continuous embedding is
`IsContinuousEmbedding`. `Brezis.Chapter09.isContinuousInjectionLp_iff` restates the definition
as a norm inequality. -/
def IsContinuousInjectionLp (N m : ℕ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ h : ∀ u : sobolevSpaceHigher N m p Ω,
      MemLp (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    IsContinuousEmbedding (SobolevMultiIndex.toLpₗ ℝ
      (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) m p Ω volume h)

/-- **Section 9.3** of [brezis2011functional], the phrase "with compact injection". Let
$m \in \mathbb{N}$, $1 \le p, q \le \infty$ and let $\Omega \subseteq \mathbb{R}^N$ be open.
Then **$W^{m,p}(\Omega) \subset L^q(\Omega)$ with compact injection** if every function of
$W^{m,p}(\Omega)$ lies in $L^q(\Omega)$ and the inclusion $W^{m,p}(\Omega) \to L^q(\Omega)$ is a
compact embedding: it is a continuous embedding, and every bounded sequence of $W^{m,p}(\Omega)$
has a subsequence that converges in $L^q(\Omega)$.

The compact embedding is `IsCompactEmbedding` of the inclusion `SobolevMultiIndex.toLpₗ`. -/
def IsCompactInjectionLp (N m : ℕ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ h : ∀ u : sobolevSpaceHigher N m p Ω,
      MemLp (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    IsCompactEmbedding (SobolevMultiIndex.toLpₗ ℝ
      (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) m p Ω volume h)

section WholeSpace

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of $\mathbb{R}^N$, as a basis of the module. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

variable {m : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- A reformulation of the definition of a continuous injection. Let $m \in \mathbb{N}$,
$1 \le p, q \le \infty$ and let $\Omega \subseteq \mathbb{R}^N$ be open. Then
$W^{m,p}(\Omega) \subset L^q(\Omega)$ with continuous injection if and only if every
$u \in W^{m,p}(\Omega)$ lies in $L^q(\Omega)$ and there is a constant $C \ge 0$ with
$$\|u\|_{L^q(\Omega)} \le C \|u\| \quad \text{for all } u \in W^{m,p}(\Omega).$$

Here $\|u\|$ is the norm of the Lean type `Brezis.Chapter09.sobolevSpaceHigher`, which is
equivalent to the norm $\|u\|_{W^{m,p}}$ of the source. -/
theorem isContinuousInjectionLp_iff :
    IsContinuousInjectionLp N m p q Ω ↔
      (∀ u : sobolevSpaceHigher N m p Ω,
        MemLp (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher N m p Ω,
        eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))
          ≤ ENNReal.ofReal (C * ‖u‖) := by
  constructor
  · rintro ⟨h, hemb⟩
    obtain ⟨c, hc⟩ := hemb.exists_bound
    refine ⟨h, max c 0, le_max_right _ _, fun u ↦ ?_⟩
    have h1 := hc u
    rw [SobolevMultiIndex.toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp] at h1
    rw [← ENNReal.ofReal_toReal (h u).eLpNorm_ne_top]
    refine ENNReal.ofReal_le_ofReal (h1.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · rintro ⟨h, C, hC0, hC⟩
    refine ⟨h, SobolevMultiIndex.isContinuousEmbedding_toLpₗ h (C := C) fun u ↦ ?_⟩
    rw [SobolevMultiIndex.toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp,
      ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ C * ‖u‖)]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC u)

/-- If $W^{m,p}(\Omega) \subset L^q(\Omega)$ with compact injection, then
$W^{m,p}(\Omega) \subset L^q(\Omega)$ with continuous injection. -/
theorem IsCompactInjectionLp.isContinuousInjectionLp (h : IsCompactInjectionLp N m p q Ω) :
    IsContinuousInjectionLp N m p q Ω :=
  let ⟨h, hc⟩ := h
  ⟨h, hc.toIsContinuousEmbedding⟩

omit [Fact (1 ≤ q)] in
/-- For $1 \le p \le \infty$, $W^{m,p}(\Omega) \subset L^p(\Omega)$ with continuous injection.

The proof uses the bounded map `SobolevMultiIndex.fnL`. -/
theorem isContinuousInjectionLp_self : IsContinuousInjectionLp N m p p Ω :=
  ⟨fun u ↦ SobolevMultiIndex.memLp u, by
    rw [SobolevMultiIndex.toLpₗ_self]
    exact SobolevMultiIndex.isContinuousEmbedding_fnL⟩

/-! ### The gradient norm and the partial derivatives -/

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- Let $u \in W^{1,p}(\Omega)$ and $1 \le i \le N$. Then $\|\partial u / \partial
x_i\|_{L^p(\Omega)} \le \|\nabla u\|_{L^p(\Omega)}$, because a component of a vector is bounded
by its Euclidean norm. -/
theorem eLpNorm_partialDeriv_le (u : sobolevSpace N p Ω) (i : Fin N) :
    eLpNorm (partialDeriv u i) p (volume.restrict (Ω : Set 𝔼))
      ≤ eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) :=
  eLpNorm_mono_ae (Lp.aestronglyMeasurable _)
    (Eventually.of_forall fun x ↦ PiLp.norm_apply_le (gradient u x) i)

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- Let $u \in W^{1,p}(\Omega)$ and $1 \le i \le N$. The norm of $\partial u / \partial x_i$ in
$L^p(\Omega)$, as an element of $[0, \infty]$, is $\|\partial u / \partial x_i\|_{L^p(\Omega)}$
computed by `eLpNorm`. -/
theorem ofReal_norm_partialDeriv (u : sobolevSpace N p Ω) (i : Fin N) :
    ENNReal.ofReal ‖partialDeriv u i‖
      = eLpNorm (partialDeriv u i) p (volume.restrict (Ω : Set 𝔼)) := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- Let $u \in W^{1,p}(\Omega)$. Then
$$\sum_{i=1}^N \Big\|\frac{\partial u}{\partial x_i}\Big\|_{L^p(\Omega)} \le N \|\nabla
  u\|_{L^p(\Omega)}.$$
-/
theorem sum_ofReal_norm_partialDeriv_le (u : sobolevSpace N p Ω) :
    ∑ i, ENNReal.ofReal ‖partialDeriv u i‖
      ≤ N * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  calc ∑ i, ENNReal.ofReal ‖partialDeriv u i‖
      ≤ ∑ _i : Fin N, eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) :=
        Finset.sum_le_sum fun i _ ↦ by
          rw [ofReal_norm_partialDeriv]
          exact eLpNorm_partialDeriv_le u i
    _ = N * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [Fact (1 ≤ q)] in
/-- Let $1 \le p \le \infty$ and $u \in W^{1,p}(\Omega)$. Then
$$\|\nabla u\|_{L^p(\Omega)} \le \sum_{i=1}^N \Big\|\frac{\partial u}{\partial
  x_i}\Big\|_{L^p(\Omega)},$$
because the Euclidean norm of a vector is at most the sum of the absolute values of its
components. -/
theorem eLpNorm_gradient_le_sum (u : sobolevSpace N p Ω) :
    eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))
      ≤ ∑ i, ENNReal.ofReal ‖partialDeriv u i‖ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  calc eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))
      ≤ eLpNorm (fun x ↦ ∑ i, ‖partialDeriv u i x‖) p (volume.restrict (Ω : Set 𝔼)) :=
        eLpNorm_mono_ae (aestronglyMeasurable_gradient u) (Eventually.of_forall fun x ↦ by
          rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
          exact PiLp.norm_le_sum_norm (gradient u x))
    _ = eLpNorm (∑ i, fun x ↦ ‖partialDeriv u i x‖) p (volume.restrict (Ω : Set 𝔼)) := by
        congr 1
        funext x
        simp only [Finset.sum_apply]
    _ ≤ ∑ i, eLpNorm (fun x ↦ ‖partialDeriv u i x‖) p (volume.restrict (Ω : Set 𝔼)) :=
        eLpNorm_sum_le_of_norm hp
    _ = ∑ i, ENNReal.ofReal ‖partialDeriv u i‖ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [eLpNorm_norm _ (Lp.aestronglyMeasurable _), ofReal_norm_partialDeriv]

omit [Fact (1 ≤ q)] in
/-- Let $1 \le p \le \infty$ and $u \in W^{1,p}(\Omega)$. The $\ell^p$ gradient norm $(\sum_i
\|\partial u / \partial x_i\|_p^p)^{1/p}$ of the backbone satisfies
$$\Big(\sum_{i=1}^N \Big\|\frac{\partial u}{\partial x_i}\Big\|_p^p\Big)^{1/p} \le N \|\nabla
  u\|_{L^p(\Omega)}.$$

The $\ell^p$ gradient norm is `SobolevMultiIndex.gradNorm`. -/
theorem gradNorm_le_eLpNorm_gradient (u : sobolevSpace N p Ω) :
    SobolevMultiIndex.gradNorm u
      ≤ N * (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal := by
  have h1 : SobolevMultiIndex.gradNorm u ≤ ∑ i, ‖partialDeriv u i‖ :=
    PiLp.norm_le_sum_norm (SobolevMultiIndex.grad u)
  refine h1.trans ?_
  have h2 := sum_ofReal_norm_partialDeriv_le u
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _] at h2
  have hfin : (N : ℝ≥0∞) * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (memLp_gradient u).eLpNorm_ne_top
  have := ENNReal.toReal_mono hfin h2
  rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_natCast] at this

omit [Fact (1 ≤ q)] in
/-- Let $1 \le p \le \infty$ and $u \in W^{1,p}(\Omega)$. Then $\|\nabla u\|_{L^p(\Omega)}$ is at
most $N$ times the $\ell^p$ gradient norm `SobolevMultiIndex.gradNorm u` $= (\sum_i \|\partial u
/ \partial x_i\|_p^p)^{1/p}$. -/
theorem toReal_eLpNorm_gradient_le_gradNorm (u : sobolevSpace N p Ω) :
    (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
      ≤ N * SobolevMultiIndex.gradNorm u := by
  have h2 := eLpNorm_gradient_le_sum u
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _] at h2
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at this
  refine this.trans ?_
  calc ∑ i, ‖partialDeriv u i‖ ≤ ∑ _i : Fin N, SobolevMultiIndex.gradNorm u :=
        Finset.sum_le_sum fun i _ ↦ SobolevMultiIndex.norm_weakDeriv_single_le_gradNorm u i
    _ = N * SobolevMultiIndex.gradNorm u := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]


/-! ### Lemma 9.4: Gagliardo's product lemma -/

section Gagliardo

/-- **Lemma 9.4** of [brezis2011functional] (Gagliardo). Let $N \ge 2$ and
$f_1, \dots, f_N \in L^{N-1}(\mathbb{R}^{N-1})$. For $x \in \mathbb{R}^N$ and $1 \le i \le N$
let $\tilde x_i = (x_1, \dots, x_{i-1}, x_{i+1}, \dots, x_N) \in \mathbb{R}^{N-1}$ be $x$ with
the coordinate $x_i$ left out, and let $f(x) = f_1(\tilde x_1) f_2(\tilde x_2) \cdots f_N(\tilde
x_N)$. Then $f \in L^1(\mathbb{R}^N)$ and
$$\|f\|_{L^1(\mathbb{R}^N)} \le \prod_{i=1}^N \|f_i\|_{L^{N-1}(\mathbb{R}^{N-1})}.$$

Here $N = n + 2$, the space $\mathbb{R}^{N-1}$ is `Fin (n + 1) → ℝ` with the product measure,
and $\tilde x_i$ is `x ∘ Fin.succAbove i`. The proof applies the backbone's
`MeasureTheory.lintegral_prod_comp_succAbove_le` to the functions $|f_i|$. That lemma follows
the induction on $N$ of the source, with Hölder's inequality in the last coordinate at each
step. -/
theorem lemma_9_4 {n : ℕ} (f : Fin (n + 2) → Lp ℝ (n + 1) (volume : Measure (Fin (n + 1) → ℝ))) :
    Integrable (fun x : Fin (n + 2) → ℝ ↦ ∏ i, f i (x ∘ i.succAbove)) volume ∧
      eLpNorm (fun x : Fin (n + 2) → ℝ ↦ ∏ i, f i (x ∘ i.succAbove)) 1 volume
        ≤ ∏ i, eLpNorm (f i) (n + 1) volume := by
  have hmeas : Measurable fun x : Fin (n + 2) → ℝ ↦ ∏ i, f i (x ∘ i.succAbove) :=
    Finset.measurable_prod _ fun i _ ↦
      (Lp.stronglyMeasurable (f i)).measurable.comp (measurable_comp_succAbove i)
  have h1 : eLpNorm (fun x : Fin (n + 2) → ℝ ↦ ∏ i, f i (x ∘ i.succAbove)) 1 volume
      = ∫⁻ x, ∏ i, ‖f i (x ∘ i.succAbove)‖ₑ := by
    rw [eLpNorm_one_eq_lintegral_enorm hmeas.aestronglyMeasurable]
    refine lintegral_congr fun x ↦ ?_
    simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.ofNNReal_finsetProd]
  have h2 : ∀ i, eLpNorm (f i) (n + 1) volume
      = (∫⁻ y, ‖f i y‖ₑ ^ ((n : ℝ) + 1)) ^ (1 / ((n : ℝ) + 1)) := fun i ↦ by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) (by simp)
      (Lp.aestronglyMeasurable (f i))]
    simp [ENNReal.toReal_add]
  have hle : eLpNorm (fun x : Fin (n + 2) → ℝ ↦ ∏ i, f i (x ∘ i.succAbove)) 1 volume
      ≤ ∏ i, eLpNorm (f i) (n + 1) volume := by
    rw [h1]
    simp_rw [h2]
    exact MeasureTheory.lintegral_prod_comp_succAbove_le (fun i y ↦ ‖f i y‖ₑ)
      fun i ↦ (Lp.stronglyMeasurable (f i)).measurable.enorm
  refine ⟨memLp_one_iff_integrable.1 ?_, hle⟩
  exact hle.trans_lt (ENNReal.prod_lt_top fun i _ ↦ Lp.eLpNorm_lt_top (f i))

end Gagliardo

/-! ### Theorem 9.9: the Sobolev–Gagliardo–Nirenberg inequality -/

section GNS

variable {p p' q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- **Theorem 9.9** of [brezis2011functional] (Sobolev, Gagliardo, Nirenberg). Let $1 \le p < N$ and
let $p^* \ge 1$ be given by $1/p^* = 1/p - 1/N$. Then $W^{1,p}(\mathbb{R}^N) \subset
L^{p^*}(\mathbb{R}^N)$ with continuous injection, and there is a constant $C$ such that
$$\|u\|_{L^{p^*}(\mathbb{R}^N)} \le C \|\nabla u\|_{L^p(\mathbb{R}^N)} \quad \text{for all } u
  \in W^{1,p}(\mathbb{R}^N).$$

The proof specializes `SobolevEuclidean.isContinuousEmbedding_toLp_of_eq` and
`SobolevEuclidean.eLpNorm_fn_le_of_eq`. These follow from Mathlib's inequality for compactly
supported $C^1$ functions, by density and Fatou's lemma. The constant is $N$ times
`SobolevEuclidean.gnsConst`, the constant of the Mathlib inequality; the explicit constant
$(N - 1)p/(N - p)$ of footnote 9 is not given.

**Reading.** Footnote 9 specifies a constant. The statement here uses an existential bound. -/
theorem theorem_9_9 [Fact (1 ≤ (p' : ℝ≥0∞))] (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) :
    IsContinuousInjectionLp N 1 p p' ⊤ ∧ ∃ C : ℝ≥0, ∀ u : sobolevSpace N p ⊤,
      eLpNorm (SobolevMultiIndex.fn u) p' volume ≤ C * eLpNorm (gradient u) p volume := by
  refine ⟨⟨fun u ↦ by
      simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_of_eq hpN hp' u,
    SobolevEuclidean.isContinuousEmbedding_toLp_of_eq hpN hp'⟩, SobolevEuclidean.gnsConst N p * N,
    fun u ↦ ?_⟩
  refine (SobolevEuclidean.eLpNorm_fn_le_of_eq hpN hp' u).trans ?_
  have h := sum_ofReal_norm_partialDeriv_le u
  rw [eLpNorm_restrict_coe_top] at h
  push_cast
  rw [mul_assoc]
  exact mul_le_mul' le_rfl h

/-- **Corollary 9.10** of [brezis2011functional]. Let $1 \le p < N$ and $1/p^* = 1/p - 1/N$. Then
$W^{1,p}(\mathbb{R}^N) \subset L^q(\mathbb{R}^N)$ with continuous injection for every
$q \in [p, p^*]$.

The proof specializes `SobolevEuclidean.isContinuousEmbedding_toLp_of_le_of_le`. It uses the
interpolation inequality $\|u\|_q \le \|u\|_p^\alpha \|u\|_{p^*}^{1-\alpha} \le \|u\|_p +
\|u\|_{p^*}$ (Remark 2 of Chapter 4 and Young's inequality) and Theorem 9.9. -/
theorem corollary_9_10 [Fact (1 ≤ (q : ℝ≥0∞))] (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (hpq : p ≤ q) (hqp' : q ≤ p') : IsContinuousInjectionLp N 1 p q ⊤ :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_le_of_le hpN hp' hpq hqp'⟩

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- **Corollary 9.11** of [brezis2011functional] (the limiting case $p = N$). Let $N \ge 2$. Then
$W^{1,N}(\mathbb{R}^N) \subset L^q(\mathbb{R}^N)$ with continuous injection for every
$q \in [N, +\infty)$.

**Reading.** The source states the corollary for every $N$. Its proof uses the exponent
$N' = N/(N - 1)$, so it needs $N \ge 2$, and the statement here assumes $N \ge 2$. For $N = 1$
the statement is a case of Theorem 8.8.

By footnote 11 of the source the constant of the injection depends on $q$ and $N$. The proof
specializes `SobolevEuclidean.isContinuousEmbedding_toLp_of_eq_finrank`, which follows the
iteration with $|u|^{m-1} u$ of the source, (20)–(23). -/
theorem corollary_9_11 [Fact (1 ≤ (N : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) : IsContinuousInjectionLp N 1 N q ⊤ :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_eq_finrank hN hq⟩

end GNS

/-! ### Theorem 9.12: Morrey's theorem -/

section Morrey

variable {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- **Theorem 9.12** of [brezis2011functional] (Morrey), the injection and the inequality (24). Let
$N < p < \infty$. Then $W^{1,p}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$ with continuous
injection, and there is a constant $C$ with
$$\|u\|_{L^\infty(\mathbb{R}^N)} \le C \|u\|_{W^{1,p}} \quad \text{for all } u \in
  W^{1,p}(\mathbb{R}^N).$$

The proof specializes `SobolevEuclidean.eLpNorm_fn_top_le_of_lt`, which uses Morrey's estimate
on balls with the constant `MeasureTheory.morreySupConst`. -/
theorem theorem_9_12_top_le (hp : (N : ℝ≥0) < p) :
    IsContinuousInjectionLp N 1 p ⊤ ⊤ ∧ ∃ C : ℝ, ∀ u : sobolevSpace N p ⊤,
      eLpNorm (SobolevMultiIndex.fn u) ⊤ volume ≤ ENNReal.ofReal (C * bookNorm u) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞,
    K = morreySupConst (volume : Measure 𝔼) p * (N + 1) := ⟨_, rfl⟩
  have hKt : K ≠ ⊤ := hK ▸ ENNReal.mul_ne_top (morreySupConst_ne_top _ _) (by simp)
  have hbound : ∀ u : sobolevSpace N p ⊤,
      eLpNorm (SobolevMultiIndex.fn u) ⊤ volume ≤ ENNReal.ofReal (K.toReal * ‖u‖) := fun u ↦ by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hKt, hK]
    exact SobolevEuclidean.eLpNorm_fn_top_le_of_lt hp u
  refine ⟨isContinuousInjectionLp_iff.2 ⟨fun u ↦ by
      simpa [Measure.restrict_coe_top] using SobolevEuclidean.memLp_fn_top_of_lt hp u,
      K.toReal, ENNReal.toReal_nonneg, fun u ↦ by
        simpa [Measure.restrict_coe_top] using hbound u⟩, K.toReal, fun u ↦ ?_⟩
  exact (hbound u).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (bookNorm_equiv u).1 ENNReal.toReal_nonneg))

/-- **Theorem 9.12** of [brezis2011functional] (Morrey), the inequality (25). Let $N < p < \infty$
and $\alpha = 1 - N/p$. There is a constant $C \ge 0$ such that every
$u \in W^{1,p}(\mathbb{R}^N)$ has a continuous representative $\tilde u$ with
$$|\tilde u(x) - \tilde u(y)| \le C |x - y|^\alpha \|\nabla u\|_{L^p(\mathbb{R}^N)} \quad
  \text{for all } x, y \in \mathbb{R}^N,$$
and hence $|u(x) - u(y)| \le C |x - y|^\alpha \|\nabla u\|_p$ for a.e. $x$ and a.e. $y$ in
$\mathbb{R}^N$.

The proof specializes `SobolevEuclidean.exists_continuous_ae_eq_of_lt`, which averages over
balls, with the constant `MeasureTheory.morreyConst`.

**Reading.** The statement gives a pointwise estimate for a continuous representative,
 together with the estimate for almost every $x$ and almost every $y$ for the original class. -/
theorem theorem_9_12_holder (hp : (N : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∀ u : sobolevSpace N p ⊤, ∃ ũ : 𝔼 → ℝ, Continuous ũ ∧
      SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
      (∀ x y, ‖ũ x - ũ y‖ₑ ≤ C * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
        * eLpNorm (gradient u) p volume) ∧
      ∀ᵐ x, ∀ᵐ y, ‖SobolevMultiIndex.fn u x - SobolevMultiIndex.fn u y‖ₑ
        ≤ C * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ))) * eLpNorm (gradient u) p volume := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = morreyConst (volume : Measure 𝔼) p * N := ⟨_, rfl⟩
  have hKt : K ≠ ⊤ := hK ▸ ENNReal.mul_ne_top (morreyConst_ne_top _ _) (by simp)
  refine ⟨K.toNNReal, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, hhold, -, -⟩ := SobolevEuclidean.exists_continuous_ae_eq_of_lt hp u
  have hsum := sum_ofReal_norm_partialDeriv_le u
  rw [eLpNorm_restrict_coe_top] at hsum
  have hbound : ∀ x y, ‖ũ x - ũ y‖ₑ ≤ K.toNNReal * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
      * eLpNorm (gradient u) p volume := fun x y ↦ by
    refine (hhold x y).trans ?_
    rw [ENNReal.coe_toNNReal hKt, hK]
    calc morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
          * ∑ i, ENNReal.ofReal ‖SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)‖
        ≤ morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
          * (N * eLpNorm (gradient u) p volume) := mul_le_mul' le_rfl hsum
      _ = _ := by ring
  refine ⟨ũ, hc, hae, hbound, ?_⟩
  filter_upwards [hae] with x hx
  filter_upwards [hae] with y hy
  rw [hx, hy]
  exact hbound x y

/-- **Theorem 9.12** of [brezis2011functional] (Morrey). Let $N < p < \infty$ and
$\alpha = 1 - N/p$. Then $W^{1,p}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$ with continuous
injection. There is a constant $C$ with $\|u\|_\infty \le C \|u\|_{W^{1,p}}$ for all
$u \in W^{1,p}(\mathbb{R}^N)$ (inequality (24)), and a constant $C' \ge 0$ such that for all
$u \in W^{1,p}(\mathbb{R}^N)$
$$|u(x) - u(y)| \le C' |x - y|^\alpha \|\nabla u\|_p \quad \text{for a.e. } x, y \in
  \mathbb{R}^N$$
(inequality (25)).

The source writes one constant $C$ that depends only on $p$ and $N$. The two parts are
`Brezis.Chapter09.theorem_9_12_top_le` and `Brezis.Chapter09.theorem_9_12_holder`, and the case
$p = \infty$ is `Brezis.Chapter09.theorem_9_12_top`.

**Reading.** The finite-exponent case states (25) for almost every $x$ and almost every $y$.
 The estimate on a common conull set follows from the continuous representative in
 `Brezis.Chapter09.theorem_9_12_holder`. -/
theorem theorem_9_12 (hp : (N : ℝ≥0) < p) :
    IsContinuousInjectionLp N 1 p ⊤ ⊤ ∧
    (∃ C : ℝ, ∀ u : sobolevSpace N p ⊤,
      eLpNorm (SobolevMultiIndex.fn u) ⊤ volume ≤ ENNReal.ofReal (C * bookNorm u)) ∧
    ∃ C : ℝ≥0, ∀ u : sobolevSpace N p ⊤, ∀ᵐ x, ∀ᵐ y,
      ‖SobolevMultiIndex.fn u x - SobolevMultiIndex.fn u y‖ₑ
        ≤ C * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ))) * eLpNorm (gradient u) p volume := by
  obtain ⟨h1, h2⟩ := theorem_9_12_top_le hp
  obtain ⟨C, hC⟩ := theorem_9_12_holder hp
  exact ⟨h1, h2, C, fun u ↦ (hC u).choose_spec.2.2.2⟩

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- **Theorem 9.12** of [brezis2011functional], the case $p = \infty$. The space
$W^{1,\infty}(\mathbb{R}^N)$ is contained in $L^\infty(\mathbb{R}^N)$ with continuous injection,
and every $u \in W^{1,\infty}(\mathbb{R}^N)$ has a representative $\tilde u$ with
$$|\tilde u(x) - \tilde u(y)| \le \|\nabla u\|_\infty |x - y| \quad \text{for all } x, y \in
  \mathbb{R}^N.$$

This is the inequality (25) with $\alpha = 1$. The second part is Remark 7
(`Brezis.Chapter09.remark_9_7_convex`) for the convex set $\mathbb{R}^N$.

**Reading.** The endpoint $p = \infty$ is stated as a global Lipschitz estimate for a
 representative, with the gradient bound as the Lipschitz constant. -/
theorem theorem_9_12_top :
    IsContinuousInjectionLp N 1 ⊤ ⊤ ⊤ ∧ ∀ u : sobolevSpace N ⊤ ⊤, ∃ ũ : 𝔼 → ℝ,
      SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
      ∀ x y, |ũ x - ũ y| ≤ (eLpNorm (gradient u) ⊤ volume).toReal * ‖x - y‖ := by
  refine ⟨isContinuousInjectionLp_self, fun u ↦ ?_⟩
  obtain ⟨ũ, hae, hlip⟩ := remark_9_7_convex (Ω := ⊤) (convex_univ) u
  refine ⟨ũ, eventuallyEq_restrict_coe_top_iff.1 hae, fun x y ↦ ?_⟩
  have := hlip x trivial y trivial
  rwa [eLpNorm_restrict_coe_top] at this

/-- **Remark 11** of Chapter 9 of [brezis2011functional]. Let $N < p < \infty$ and
$u \in W^{1,p}(\mathbb{R}^N)$. There is a unique continuous function
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ with $u = \tilde u$ a.e. on $\mathbb{R}^N$.

Uniqueness holds because two continuous functions that agree almost everywhere agree everywhere.
The source then writes $u$ for $\tilde u$. The backbone bundles the representative as
`SobolevEuclidean.contRep`. -/
theorem remark_9_11 (hp : (N : ℝ≥0) < p) (u : sobolevSpace N p ⊤) :
    ∃! ũ : 𝔼 → ℝ, Continuous ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ := by
  refine ⟨SobolevEuclidean.contRep hp u, ⟨(SobolevEuclidean.contRep hp u).continuous,
    SobolevEuclidean.fn_ae_eq_contRep hp u⟩, fun g ⟨hgc, hg⟩ ↦ ?_⟩
  exact Measure.eq_of_ae_eq (μ := volume) (hg.symm.trans (SobolevEuclidean.fn_ae_eq_contRep hp u))
    hgc (SobolevEuclidean.contRep hp u).continuous

/-- **Remark 12** of Chapter 9 of [brezis2011functional]. Let $N < p < \infty$ and
$u \in W^{1,p}(\mathbb{R}^N)$. The continuous representative $\tilde u$ of $u$ satisfies
$\lim_{|x| \to \infty} \tilde u(x) = 0$.

The limit is taken along the filter `Filter.cocompact`. The function $\tilde u$ is the uniform
limit of $C_c^1$ approximations, by (24). The statement is the last part of
`SobolevEuclidean.exists_continuous_ae_eq_of_lt`. -/
theorem remark_9_12 (hp : (N : ℝ≥0) < p) (u : sobolevSpace N p ⊤) :
    ∃ ũ : 𝔼 → ℝ, Continuous ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
      Tendsto ũ (cocompact 𝔼) (𝓝 0) :=
  ⟨SobolevEuclidean.contRep hp u, (SobolevEuclidean.contRep hp u).continuous,
    SobolevEuclidean.fn_ae_eq_contRep hp u, SobolevEuclidean.tendsto_contRep_cocompact hp u⟩

end Morrey

/-! ### Corollary 9.13: the spaces $W^{m,p}(\mathbb{R}^N)$ -/

section HigherOrder

variable {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- An exponent computation for Corollary 9.13. Let $p > 0$ and $m \in \mathbb{N}$. If
$1/p - m/N < 0$, then $N/p < m$. -/
theorem div_lt_of_inv_sub_div_neg {m : ℕ} (hp : (0 : ℝ) < p)
    (hm : (p : ℝ)⁻¹ - m / N < 0) : (N : ℝ) / p < m := by
  have hN : (0 : ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg N)
    rw [this, div_zero, sub_zero] at hm
    exact absurd hm (not_lt.2 (inv_pos.2 hp).le)
  rw [div_lt_iff₀ hp]
  have := (sub_neg.1 hm)
  rwa [inv_lt_iff_one_lt_mul₀ hp, div_mul_eq_mul_div, one_lt_div hN] at this

/-- **Corollary 9.13** of [brezis2011functional], first clause. Let $m \in \mathbb{N}$,
$1 \le p < \infty$, and assume $N \ge 2$ or $p > 1$. If $1/p - m/N > 0$ and $1/q = 1/p - m/N$,
then $W^{m,p}(\mathbb{R}^N) \subset L^q(\mathbb{R}^N)$ with continuous injection.

**Reading.** The source has no hypothesis on $N$ and $p$. Its proof is the repeated application
of Theorem 9.9 and Corollary 9.11, and Corollary 9.11 needs $N \ge 2$; the chain of first-order
embeddings stops at $W^{1,1}(\mathbb{R})$. The statement here assumes $N \ge 2$ or $p > 1$.

**Generalization.** The source assumes $m \ge 1$. The declaration includes $m = 0$, when
$q = p$ and the embedding is the identity on $L^p$.

The proof specializes
`SobolevEuclidean.isContinuousEmbedding_toLp_of_order`, by induction on $m$. -/
theorem corollary_9_13_lt [Fact (1 ≤ (q : ℝ≥0∞))] {m : ℕ} (hN : 2 ≤ N ∨ 1 < p)
    (hpos : 0 < (p : ℝ)⁻¹ - m / N) (hq : (q : ℝ)⁻¹ = p⁻¹ - m / N) :
    IsContinuousInjectionLp N m p q ⊤ := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hq0 : (0 : ℝ) < q := by
    rw [← inv_pos, hq]
    exact hpos
  have hpq : p ≤ q := by
    rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hq0 hp0, hq]
    exact sub_le_self _ (by positivity)
  exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order hN hpq hq.ge⟩

/-- **Corollary 9.13** of [brezis2011functional], second clause. Let $m \in \mathbb{N}$,
$1 \le p < \infty$, and assume $N \ge 2$ or $p > 1$. If $1/p - m/N = 0$, then
$W^{m,p}(\mathbb{R}^N) \subset L^q(\mathbb{R}^N)$ with continuous injection for every
$q \in [p, +\infty)$.

**Reading.** The hypothesis $N \ge 2$ or $p > 1$ is added, as in
`Brezis.Chapter09.corollary_9_13_lt`.

The proof specializes `SobolevEuclidean.isContinuousEmbedding_toLp_of_order`, by repeated
application of Theorem 9.9 and Corollary 9.11. -/
theorem corollary_9_13_eq [Fact (1 ≤ (q : ℝ≥0∞))] {m : ℕ} (hN : 2 ≤ N ∨ 1 < p)
    (hm : (p : ℝ)⁻¹ - m / N = 0) (hpq : p ≤ q) : IsContinuousInjectionLp N m p q ⊤ :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order hN hpq (hm ▸ by positivity)⟩

/-- **Corollary 9.13** of [brezis2011functional], third clause. Let $m \in \mathbb{N}$,
$1 \le p < \infty$, and assume $N \ge 2$ or $p > 1$. If $1/p - m/N < 0$, then
$W^{m,p}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$ with continuous injection.

**Reading.** The hypothesis $N \ge 2$ or $p > 1$ is added, as in
`Brezis.Chapter09.corollary_9_13_lt`.

The proof specializes `SobolevEuclidean.isContinuousEmbedding_toLp_top_of_order`, by repeated
application of Theorem 9.9 and Theorem 9.12. -/
theorem corollary_9_13_gt {m : ℕ} (hN : 2 ≤ N ∨ 1 < p) (hm : (p : ℝ)⁻¹ - m / N < 0) :
    IsContinuousInjectionLp N m p ⊤ ⊤ := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_top_of_order hN
    (div_lt_of_inv_sub_div_neg hp0 hm)⟩

/-- **Corollary 9.13** of [brezis2011functional], the $C^k$ clause (footnotes 12–14). Let
$m \in \mathbb{N}$, $1 \le p < \infty$, and assume $N \ge 2$ or $p > 1$. Assume that
$m - N/p > 0$ is not an integer, and let $k = [m - N/p]$ be its integer part and
$\theta = m - N/p - k \in (0, 1)$. There is a constant $C \ge 0$ such that every
$u \in W^{m,p}(\mathbb{R}^N)$ has a representative $\tilde u$ of class $C^k$ with
$$\|D^j \tilde u(x)\| \le C \|u\|_{W^{m,p}} \quad \text{for all } j \le k \text{ and } x \in
  \mathbb{R}^N,$$
$$\|D^k \tilde u(x) - D^k \tilde u(y)\| \le C \|u\|_{W^{m,p}} |x - y|^\theta \quad \text{for all
  } x, y \in \mathbb{R}^N.$$
In particular $W^{m,p}(\mathbb{R}^N) \subset C^k(\mathbb{R}^N)$, up to the choice of a
representative.

**Reading.** The hypothesis $N \ge 2$ or $p > 1$ is added, as in
`Brezis.Chapter09.corollary_9_13_lt`.

The source bounds the partial derivatives $D^\alpha \tilde u$ for $|\alpha| \le k$. Here
$D^j \tilde u$ is the full $j$-th derivative `iteratedFDeriv ℝ j ũ`, which bounds every
$D^\alpha \tilde u$ with $|\alpha| = j$. The estimates hold at every point, and hence almost
everywhere. The proof specializes `SobolevEuclidean.exists_contDiff_ae_eq_of_order`.

**Reading.** The derivative bounds use the operator norm of the iterated Fréchet derivative
 and hold at every point for a $C^k$ representative. The source bounds the coordinate derivatives
 almost everywhere. -/
theorem corollary_9_13_holder {m : ℕ} (hN : 2 ≤ N ∨ 1 < p) (hm : 0 < (m : ℝ) - N / p)
    (hint : ∀ j : ℕ, (m : ℝ) - N / p ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher N m p ⊤, ∃ ũ : 𝔼 → ℝ,
      ContDiff ℝ ⌊(m : ℝ) - N / p⌋₊ ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
      (∀ j ≤ ⌊(m : ℝ) - N / p⌋₊, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * bookNormHigher u) ∧
      ∀ x y, ‖iteratedFDeriv ℝ ⌊(m : ℝ) - N / p⌋₊ ũ x - iteratedFDeriv ℝ ⌊(m : ℝ) - N / p⌋₊ ũ y‖
        ≤ C * bookNormHigher u * ‖x - y‖ ^ ((m : ℝ) - N / p - ⌊(m : ℝ) - N / p⌋₊) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊(m : ℝ) - N / p⌋₊ := ⟨_, rfl⟩
  have hθ0 : 0 < (m : ℝ) - N / p - k := by
    rw [hk]
    exact lt_of_le_of_ne (sub_nonneg.2 (Nat.floor_le hm.le)) fun h ↦ hint _ (sub_eq_zero.1 h.symm)
  have hθ1 : (m : ℝ) - N / p - k < 1 := by
    rw [hk, sub_lt_iff_lt_add, add_comm]
    exact Nat.lt_floor_add_one _
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_contDiff_ae_eq_of_order (N := N) (m := m) (k := k)
    hN hθ0 hθ1
  rw [← hk]
  refine ⟨C, hC0, fun u ↦ ?_⟩
  obtain ⟨ũ, hũ, hae, hb, hh⟩ := hC u
  have hnorm : C * ‖u‖ ≤ C * bookNormHigher u :=
    mul_le_mul_of_nonneg_left (bookNormHigher_equiv u).1 hC0
  refine ⟨ũ, hũ, hae, fun j hj x ↦ (hb j hj x).trans hnorm, fun x y ↦ (hh x y).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (norm_nonneg _) _)

/-- **Corollary 9.13** of [brezis2011functional]. Let $m \in \mathbb{N}$ and $1 \le p < \infty$, and
assume $N \ge 2$ or $p > 1$. Then, with continuous injections,
$$W^{m,p}(\mathbb{R}^N) \subset L^q(\mathbb{R}^N), \quad \frac{1}{q} = \frac{1}{p} -
  \frac{m}{N}, \quad \text{if } \frac{1}{p} - \frac{m}{N} > 0,$$
$$W^{m,p}(\mathbb{R}^N) \subset L^q(\mathbb{R}^N) \text{ for all } q \in [p, +\infty), \quad
  \text{if } \frac{1}{p} - \frac{m}{N} = 0,$$
$$W^{m,p}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N), \quad \text{if } \frac{1}{p} -
  \frac{m}{N} < 0.$$
Moreover, if $m - N/p > 0$ is not an integer, let $k = [m - N/p]$ and $\theta = m - N/p - k$.
There is $C \ge 0$ such that every $u \in W^{m,p}(\mathbb{R}^N)$ has a $C^k$ representative
whose derivatives of order $j \le k$ are bounded by $C \|u\|_{W^{m,p}}$ and whose derivative of
order $k$ is Hölder continuous with exponent $\theta$ and constant $C \|u\|_{W^{m,p}}$. In
particular $W^{m,p}(\mathbb{R}^N) \subset C^k(\mathbb{R}^N)$.

**Reading.** The hypothesis $N \ge 2$ or $p > 1$ is added; see
`Brezis.Chapter09.corollary_9_13_lt`.

**Generalization.** The source assumes $m \ge 1$. The declaration includes $m = 0$, when the
applicable embedding is the identity on $L^p$.

The case $m = N$, $p = 1$ is Remark 13, `Brezis.Chapter09.remark_9_13`. -/
theorem corollary_9_13 {m : ℕ} (hN : 2 ≤ N ∨ 1 < p) :
    (∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], 0 < (p : ℝ)⁻¹ - m / N →
      (q : ℝ)⁻¹ = p⁻¹ - m / N → IsContinuousInjectionLp N m p q ⊤) ∧
    ((p : ℝ)⁻¹ - m / N = 0 → ∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLp N m p q ⊤) ∧
    ((p : ℝ)⁻¹ - m / N < 0 → IsContinuousInjectionLp N m p ⊤ ⊤) ∧
    (0 < (m : ℝ) - N / p → (∀ j : ℕ, (m : ℝ) - N / p ≠ j) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher N m p ⊤, ∃ ũ : 𝔼 → ℝ,
        ContDiff ℝ ⌊(m : ℝ) - N / p⌋₊ ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧
        (∀ j ≤ ⌊(m : ℝ) - N / p⌋₊, ∀ x, ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * bookNormHigher u) ∧
        ∀ x y, ‖iteratedFDeriv ℝ ⌊(m : ℝ) - N / p⌋₊ ũ x
            - iteratedFDeriv ℝ ⌊(m : ℝ) - N / p⌋₊ ũ y‖
          ≤ C * bookNormHigher u * ‖x - y‖ ^ ((m : ℝ) - N / p - ⌊(m : ℝ) - N / p⌋₊)) :=
  ⟨fun _ _ hpos hq ↦ corollary_9_13_lt hN hpos hq, fun hm _ _ hpq ↦ corollary_9_13_eq hN hm hpq,
    corollary_9_13_gt hN, corollary_9_13_holder hN⟩

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- **Remark 13** of Chapter 9 of [brezis2011functional]. The case $p = 1$, $m = N$ is special:
$W^{N,1}(\mathbb{R}^N) \subset L^\infty(\mathbb{R}^N)$ with continuous injection, and every
$u \in W^{N,1}(\mathbb{R}^N)$ has a continuous representative $\tilde u$ with
$$|\tilde u(x)| \le \|u\|_{W^{N,1}} \quad \text{for all } x \in \mathbb{R}^N.$$

The proof specializes `SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one`. For
$u \in C_c^\infty(\mathbb{R}^N)$ one has $u(x) = \int_{-\infty}^{x_1} \cdots
\int_{-\infty}^{x_N} \partial^N u / \partial x_1 \cdots \partial x_N$, so $\|u\|_\infty \le
\|\partial_1 \cdots \partial_N u\|_1 \le \|u\|_{W^{N,1}}$, and the general case follows by
density. The negative clause of the remark, that in general $W^{m,p}(\mathbb{R}^N) \not\subset
L^\infty(\mathbb{R}^N)$ for $p > 1$ and $m = N/p$, is not formalized.

**Reading.** The positive embedding is stated with a continuous representative and constant
 one. The source also describes the failure of the critical embedding with $p>1$. -/
theorem remark_9_13 :
    IsContinuousInjectionLp N N 1 ⊤ ⊤ ∧ ∀ u : sobolevSpaceHigher N N 1 ⊤, ∃ ũ : 𝔼 → ℝ,
      Continuous ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume] ũ ∧ ∀ x, |ũ x| ≤ bookNormHigher u := by
  have hbound : ∀ u : sobolevSpaceHigher N N 1 ⊤,
      eLpNorm (SobolevMultiIndex.fn u) ⊤ volume ≤ ENNReal.ofReal (1 * ‖u‖) := fun u ↦ by
    obtain ⟨ũ, hc, hae, hb⟩ := SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one u
    rw [eLpNorm_congr_ae hae, one_mul]
    refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal ‖u‖) hc.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb x)
  have hmem : ∀ u : sobolevSpaceHigher N N 1 ⊤, MemLp (SobolevMultiIndex.fn u) ⊤ volume :=
    fun u ↦ memLp_iff.2 ((hbound u).trans_lt ENNReal.ofReal_lt_top)
  refine ⟨isContinuousInjectionLp_iff.2 ⟨fun u ↦ ?_, 1, zero_le_one, fun u ↦ ?_⟩, fun u ↦ ?_⟩
  · simpa [Measure.restrict_coe_top] using hmem u
  · simpa [Measure.restrict_coe_top] using hbound u
  · obtain ⟨ũ, hc, hae, hb⟩ := SobolevEuclidean.exists_continuous_ae_eq_of_order_finrank_one u
    exact ⟨ũ, hc, hae, fun x ↦ (Real.norm_eq_abs _ ▸ hb x).trans (bookNormHigher_equiv u).1⟩

end HigherOrder

/-! ### The gradient norms in the equivalence of Remark 15 -/

section EquivNorm

omit [Fact (1 ≤ q)] in
/-- A comparison of two equivalences of norms, used for Remark 15. Let $1 \le p \le \infty$,
$q \in [0, \infty]$ and $\Omega \subseteq \mathbb{R}^N$ open. Assume that there are constants
$C, C' \ge 0$ with
$$\|u\| \le C \big(g(u) + \|u\|_{L^q(\Omega)}\big), \qquad g(u) + \|u\|_{L^q(\Omega)} \le C'
  \|u\|$$
for all $u \in W^{1,p}(\Omega)$, where $g(u) = (\sum_i \|\partial u / \partial x_i\|_p^p)^{1/p}$
is the $\ell^p$ gradient norm. Then there are constants $C_1, C_2$ with
$$\|u\|_{W^{1,p}} \le C_1 \big(\|\nabla u\|_{L^p(\Omega)} + \|u\|_{L^q(\Omega)}\big), \qquad
  \|\nabla u\|_{L^p(\Omega)} + \|u\|_{L^q(\Omega)} \le C_2 \|u\|_{W^{1,p}}$$
for all $u \in W^{1,p}(\Omega)$.

The function $g$ is `SobolevMultiIndex.gradNorm`. The proof uses
$\|u\| \le \|u\|_{W^{1,p}} \le (N + 1) \|u\|$ and $g(u) \le N \|\nabla u\|_p \le N^2 g(u)$. -/
theorem bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add
    (h₁ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpace N p Ω, ‖u‖ ≤ C * (SobolevMultiIndex.gradNorm u
      + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal))
    (h₂ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpace N p Ω, SobolevMultiIndex.gradNorm u
      + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal ≤ C * ‖u‖) :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace N p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u := by
  obtain ⟨C, hC0, hC⟩ := h₁
  obtain ⟨C', hC'0, hC'⟩ := h₂
  refine ⟨(N + 1) * C * (N + 1), (N + 1) * C', fun u ↦ ⟨?_, ?_⟩⟩
  · have hg := gradNorm_le_eLpNorm_gradient u
    have hq0 : 0 ≤ (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal :=
      ENNReal.toReal_nonneg
    have hg0 : 0 ≤ (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal :=
      ENNReal.toReal_nonneg
    calc bookNorm u ≤ (N + 1) * ‖u‖ := (bookNorm_equiv u).2
      _ ≤ (N + 1) * (C * (SobolevMultiIndex.gradNorm u
          + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal)) :=
          mul_le_mul_of_nonneg_left (hC u) (by positivity)
      _ ≤ (N + 1) * (C * ((N + 1) * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
          + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal))) := by
          gcongr
          nlinarith
      _ = _ := by ring
  · have hg := toReal_eLpNorm_gradient_le_gradNorm u
    have hgn := SobolevMultiIndex.gradNorm_nonneg u
    have hq0 : 0 ≤ (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal :=
      ENNReal.toReal_nonneg
    calc (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
          + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
        ≤ (N + 1) * (SobolevMultiIndex.gradNorm u
          + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) := by
          nlinarith
      _ ≤ (N + 1) * (C' * ‖u‖) := mul_le_mul_of_nonneg_left (hC' u) (by positivity)
      _ ≤ (N + 1) * (C' * bookNorm u) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (bookNorm_equiv u).1 hC'0)
            (by positivity)
      _ = _ := by ring

end EquivNorm
end WholeSpace




/-! ### Remark 10: the scaling argument -/

section Scaling

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- Scaling of the $L^q$ norm. Let $F$ be a normed group, $u : \mathbb{R}^N \to F$ almost everywhere
strongly measurable, $t > 0$ and $q \in [0, \infty]$. Then
$$\|u(t\,\cdot)\|_{L^q(\mathbb{R}^N)} = t^{-N/q} \|u\|_{L^q(\mathbb{R}^N)},$$
where $N/q$ is read as $0$ for $q = \infty$ (and for $q = 0$). The proof uses $d(tx) = t^N dx$.

**Generalization.** The norm change under scaling applies to a.e. strongly measurable
 normed-group-valued functions and includes extended exponents. -/
theorem eLpNorm_comp_smul_eq {F : Type*} [NormedAddCommGroup F] {u : 𝔼 → F}
    (hu : AEStronglyMeasurable u volume) {t : ℝ} (ht : 0 < t) (q : ℝ≥0∞) :
    eLpNorm (fun x ↦ u (t • x)) q volume
      = ENNReal.ofReal (t ^ (-(N : ℝ) * (q⁻¹).toReal)) * eLpNorm u q volume := by
  have hmap : Measure.map (t • ·) (volume : Measure 𝔼)
      = ENNReal.ofReal |(t ^ N)⁻¹| • volume := by
    rw [Measure.map_addHaar_smul volume ht.ne', finrank_euclideanSpace_fin]
  have h1 : eLpNorm (fun x ↦ u (t • x)) q volume = eLpNorm u q (Measure.map (t • ·) volume) := by
    refine (eLpNorm_map_measure ?_ (measurable_const_smul t).aemeasurable).symm
    rw [hmap]
    exact hu.smul_measure _
  have hc0 : ENNReal.ofReal |(t ^ N)⁻¹| ≠ 0 := by
    rw [abs_of_pos (by positivity)]
    exact ENNReal.ofReal_pos.2 (by positivity) |>.ne'
  rw [h1, hmap, eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul, one_div,
    abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) ENNReal.toReal_nonneg]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_mul ht.le]

/-- Let $u : \mathbb{R}^N \to \mathbb{R}$ be of class $C^1$ and $p \in [0, \infty]$. The $L^p$ norm
of the gradient vector $\nabla u = (\partial_1 u, \dots, \partial_N u)$ equals the $L^p$ norm of
the differential $x \mapsto Du(x)$, because the operator norm of $Du(x)$ is the Euclidean norm
of $\nabla u(x)$. -/
theorem eLpNorm_gradientVec_eq {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ (WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) : 𝔼)) p
      volume = eLpNorm (fderiv ℝ u) p volume := by
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  refine eLpNorm_congr_norm_ae ?_ hd.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  · exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ hd.clm_apply
      continuous_const)).aestronglyMeasurable
  · exact (norm_eq_norm_toLp_apply_single (fderiv ℝ u x)).symm

/-- **Remark 10** of Chapter 9 of [brezis2011functional] (the scaling argument). Let
$1 \le p < \infty$ and $1 \le q \le \infty$. Assume that there is a constant $C < \infty$ with
$$\|u\|_{L^q(\mathbb{R}^N)} \le C \|\nabla u\|_{L^p(\mathbb{R}^N)} \quad \text{for all } u \in
  C_c^\infty(\mathbb{R}^N).$$
Then $1/q = 1/p - 1/N$, that is, $q = p^*$. Here $1/q$ is read as $0$ for $q = \infty$.

The source's argument applies the inequality to $u_\lambda(x) = u(\lambda x)$. This gives
$\|u\|_q \le C \lambda^{1 + N/q - N/p} \|\nabla u\|_p$ for all $\lambda > 0$, which forces
$1 + N/q - N/p = 0$ for a function $u$ that does not vanish identically. The constant $C$ is an
element of `ℝ≥0∞` different from `⊤`, and $\nabla u$ is the vector of the partial derivatives
`fderiv ℝ u x (EuclideanSpace.single i 1)`.

**Reading.** The exponent $p$ is finite, as in the subcritical setting. The conclusion is
 written as an identity for reciprocal exponents, with reciprocal of infinity equal to zero. -/
theorem remark_9_10 {p : ℝ≥0} (hp : 1 ≤ p) {q : ℝ≥0∞} (hq : 1 ≤ q) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ u : 𝔼 → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm u q volume ≤ C * eLpNorm
        (fun x ↦ (WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) : 𝔼)) p volume) :
    (q⁻¹).toReal = (p : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp)
  have hp0' : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  -- a nonzero bump
  set u₀ : ContDiffBump (0 : 𝔼) := ⟨1, 2, one_pos, one_lt_two⟩ with hu₀
  have hu₀s : ContDiff ℝ ∞ u₀ := u₀.contDiff
  have hu₀c : HasCompactSupport u₀ := u₀.hasCompactSupport
  have hu₀0 : u₀ 0 = 1 := u₀.one_of_mem_closedBall (by simp [hu₀])
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = eLpNorm (u₀ : 𝔼 → ℝ) q volume := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = eLpNorm (fderiv ℝ (u₀ : 𝔼 → ℝ)) p volume := ⟨_, rfl⟩
  have hAt : A ≠ ⊤ := hA ▸ (u₀.continuous.memLp_of_hasCompactSupport hu₀c).eLpNorm_ne_top
  have hBt : B ≠ ⊤ := hB ▸ ((hu₀s.continuous_fderiv (by simp)).memLp_of_hasCompactSupport
    (hu₀c.fderiv (𝕜 := ℝ))).eLpNorm_ne_top
  have hA0 : 0 < A.toReal := by
    refine ENNReal.toReal_pos (fun h0 ↦ ?_) hAt
    rw [hA, eLpNorm_eq_zero_iff (zero_lt_one.trans_le hq).ne'] at h0
    have := (u₀.continuous.ae_eq_iff_eq (μ := volume) continuous_const).1 h0
    have h00 : (u₀ : 𝔼 → ℝ) 0 = 0 := congrFun this 0
    rw [hu₀0] at h00
    exact one_ne_zero h00
  -- the scaled inequality `A ≤ D t^e`, `e = 1 + N/q − N/p`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (q⁻¹).toReal := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 + N * s - N * (p : ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C.toReal * B.toReal := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ by positivity
  have key : ∀ t : ℝ, 0 < t → A.toReal ≤ D * t ^ e := by
    intro t ht
    have hsm : ContDiff ℝ ∞ fun x : 𝔼 ↦ u₀ (t • x) :=
      hu₀s.comp (contDiff_const_smul t)
    have hcs : HasCompactSupport fun x : 𝔼 ↦ u₀ (t • x) := hu₀c.comp_smul ht.ne'
    have h1 := h _ hsm hcs
    rw [eLpNorm_gradientVec_eq (hsm.of_le (by simp))] at h1
    have hfd : fderiv ℝ (fun x : 𝔼 ↦ u₀ (t • x))
        = t • fun x ↦ fderiv ℝ (u₀ : 𝔼 → ℝ) (t • x) := by
      funext x
      exact fderiv_comp_smul t
    rw [hfd, eLpNorm_const_smul, eLpNorm_comp_smul_eq u₀.continuous.aestronglyMeasurable ht,
      eLpNorm_comp_smul_eq (hu₀s.continuous_fderiv (by simp)).aestronglyMeasurable ht, ← hA, ← hB,
      Real.enorm_eq_ofReal ht.le] at h1
    have hfin : C * (ENNReal.ofReal t * (ENNReal.ofReal (t ^ (-(N : ℝ) * (p⁻¹ : ℝ≥0∞).toReal))
        * B)) ≠ ⊤ :=
      ENNReal.mul_ne_top hC (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt))
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _), ENNReal.toReal_ofReal ht.le,
      ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _), ← hs, ← ENNReal.coe_inv hp0',
      ENNReal.coe_toReal, NNReal.coe_inv] at h2
    -- multiply by `t^{N s}`
    have hts : 0 < t ^ ((N : ℝ) * s) := Real.rpow_pos_of_pos ht _
    have h3 : t ^ (-(N : ℝ) * s) * t ^ ((N : ℝ) * s) = 1 := by
      rw [← Real.rpow_add ht, neg_mul, neg_add_cancel, Real.rpow_zero]
    have h4 : t * t ^ (-(N : ℝ) * (p : ℝ)⁻¹) * t ^ ((N : ℝ) * s) = t ^ e := by
      rw [he, show (1 : ℝ) + N * s - N * (p : ℝ)⁻¹ = 1 + (-(N : ℝ) * (p : ℝ)⁻¹) + N * s by ring,
        Real.rpow_add ht, Real.rpow_add ht, Real.rpow_one]
    calc A.toReal = t ^ (-(N : ℝ) * s) * A.toReal * t ^ ((N : ℝ) * s) := by
          rw [mul_comm _ A.toReal, mul_assoc, h3, mul_one]
      _ ≤ C.toReal * (t * (t ^ (-(N : ℝ) * (p : ℝ)⁻¹) * B.toReal)) * t ^ ((N : ℝ) * s) :=
          mul_le_mul_of_nonneg_right h2 hts.le
      _ = D * (t * t ^ (-(N : ℝ) * (p : ℝ)⁻¹) * t ^ ((N : ℝ) * s)) := by rw [hD]; ring
      _ = D * t ^ e := by rw [h4]
  -- the exponent must vanish
  have he0 : e = 0 := by
    by_contra hne
    rcases hD0.eq_or_lt with hD0' | hDpos
    · have := key 1 one_pos
      rw [← hD0', zero_mul] at this
      exact absurd this (not_le.2 hA0)
    · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (A.toReal / (2 * D)) ^ e⁻¹ := ⟨_, rfl⟩
      have htpos : 0 < t := ht ▸ Real.rpow_pos_of_pos (by positivity) _
      have hte : t ^ e = A.toReal / (2 * D) := ht ▸ Real.rpow_inv_rpow (by positivity) hne
      have h5 := key t htpos
      rw [hte] at h5
      have h6 : D * (A.toReal / (2 * D)) = A.toReal / 2 := by
        field_simp
      rw [h6] at h5
      linarith
  -- and `1 + N/q − N/p = 0` is `1/q = 1/p − 1/N`
  rw [← hs]
  rw [he0] at he
  have hN : (N : ℝ) ≠ 0 := by
    rintro hN0
    rw [hN0] at he
    linarith
  have h6 : (N : ℝ) * (s + (N : ℝ)⁻¹) = N * (p : ℝ)⁻¹ := by
    rw [mul_add, mul_inv_cancel₀ hN]
    linarith
  have := mul_left_cancel₀ hN h6
  linarith

end Scaling
/-!
### Remark 14 (i): the injection $W^{1,p}(\mathbb{R}^N) \subset L^p(\mathbb{R}^N)$ is not compact
-/

section NonCompact

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The translates of a $C^1$ function with compact support. Let $1 \le p \le \infty$, let
$\varphi : \mathbb{R}^N \to \mathbb{R}$ be of class $C^1$ with compact support, and let
$c \in \mathbb{R}^N$. There is $v \in W^{1,p}(\mathbb{R}^N)$ with $v = \varphi(\cdot - c)$ a.e.
and
$$\|v\|_{W^{1,p}} = \|\varphi\|_p + \sum_{i=1}^N \Big\|\frac{\partial \varphi}{\partial
  x_i}\Big\|_p.$$
The norm does not depend on $c$ because Lebesgue measure is translation invariant. -/
theorem exists_translate_mem_sobolevSpace {φ : 𝔼 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (c : 𝔼) :
    ∃ v : sobolevSpace N p ⊤, SobolevMultiIndex.fn v =ᵐ[volume] (fun x ↦ φ (x - c)) ∧
      bookNorm v = (eLpNorm φ p volume).toReal
        + ∑ i, (eLpNorm (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) p volume).toReal := by
  have hmp : MeasurePreserving (fun x : 𝔼 ↦ x - c) volume volume := measurePreserving_sub_right _ c
  have hφc' : HasCompactSupport fun x ↦ φ (x - c) := hφc.comp_homeomorph (Homeomorph.subRight c)
  have hφ' : ContDiff ℝ 1 fun x ↦ φ (x - c) := hφ.comp (contDiff_id.sub contDiff_const)
  have hd : ∀ i, HasCompactSupport fun x ↦ fderiv ℝ φ (x - c) (EuclideanSpace.single i 1) := by
    intro i
    have h1 : HasCompactSupport fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : 𝔼 →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) rfl
    exact h1.comp_homeomorph (Homeomorph.subRight c)
  have hdc : ∀ i, Continuous fun x ↦ fderiv ℝ φ (x - c) (EuclideanSpace.single i 1) := fun i ↦
    ((hφ.continuous_fderiv one_ne_zero).comp (continuous_id.sub continuous_const)).clm_apply
      continuous_const
  obtain ⟨v, hv, hvd⟩ := remark_9_2 (Ω := ⊤) (p := p) hφ'.contDiffOn
    (by simpa [Measure.restrict_coe_top] using hφ'.continuous.memLp_of_hasCompactSupport hφc')
    fun i ↦ by
      simp only [fderiv_comp_sub]
      simpa [Measure.restrict_coe_top] using (hdc i).memLp_of_hasCompactSupport (hd i)
  refine ⟨v, eventuallyEq_restrict_coe_top_iff.1 hv, ?_⟩
  have h0 : eLpNorm (fun x ↦ φ (x - c)) p volume = eLpNorm φ p volume :=
    eLpNorm_comp_measurePreserving hφ.continuous.aestronglyMeasurable hmp
  rw [bookNorm, Lp.norm_def, SobolevMultiIndex.weakDeriv_zero, eLpNorm_restrict_coe_top,
    eLpNorm_congr_ae (eventuallyEq_restrict_coe_top_iff.1 hv), h0]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Lp.norm_def, eLpNorm_restrict_coe_top, eLpNorm_congr_ae (eventuallyEq_restrict_coe_top_iff.1
    (hvd i))]
  simp only [fderiv_comp_sub]
  congr 1
  exact eLpNorm_comp_measurePreserving (g := fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable hmp

/-- **Remark 14 (i)** of Chapter 9 of [brezis2011functional]. If $\Omega$ is not bounded, the
injection $W^{1,p}(\Omega) \subset L^p(\Omega)$ is in general not compact. Here: for $N \ge 1$
and $1 \le p \le \infty$, $W^{1,p}(\mathbb{R}^N) \subset L^p(\mathbb{R}^N)$ is not a compact
injection.

The proof takes the translates $u_n(x) = \varphi(x - 5n e_1)$ of a function
$\varphi \in C_c^\infty(\mathbb{R}^N)$ that is not zero. They are bounded in
$W^{1,p}(\mathbb{R}^N)$, and their supports are disjoint, so they are pairwise at $L^p$ distance
at least $\|\varphi\|_p$, and no subsequence converges in $L^p(\mathbb{R}^N)$. This is the
argument of Remark 12 of Chapter 4 (Exercise 4.33) in $N$ dimensions. Remark 14 (ii), that the
injection into $L^{p^*}$ is never compact, is not formalized.

**Reading.** The library gives the whole space of positive dimension as the counterexample to
 compactness on unbounded domains. -/
theorem remark_9_14_i (hN : 0 < N) : ¬ IsCompactInjectionLp N 1 p p ⊤ := by
  rintro ⟨h, hc⟩
  -- the bump and its translates
  set φ : ContDiffBump (0 : 𝔼) := ⟨1, 2, one_pos, one_lt_two⟩ with hφ
  have hφs : ContDiff ℝ 1 φ := φ.contDiff
  have hφc : HasCompactSupport φ := φ.hasCompactSupport
  have hφ0 : φ 0 = 1 := φ.one_of_mem_closedBall (by simp [hφ])
  have hφp : 0 < eLpNorm (φ : 𝔼 → ℝ) p volume := by
    refine pos_iff_ne_zero.2 fun h0 ↦ ?_
    rw [eLpNorm_eq_zero_iff (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'] at h0
    have := (φ.continuous.ae_eq_iff_eq (μ := volume) continuous_const).1 h0
    have h00 : (φ : 𝔼 → ℝ) 0 = 0 := congrFun this 0
    rw [hφ0] at h00
    exact one_ne_zero h00
  have hφt : eLpNorm (φ : 𝔼 → ℝ) p volume ≠ ⊤ :=
    (φ.continuous.memLp_of_hasCompactSupport hφc).eLpNorm_ne_top
  obtain ⟨e, he⟩ : ∃ e : 𝔼, ‖e‖ = 1 := ⟨EuclideanSpace.single ⟨0, hN⟩ 1, by simp⟩
  set c : ℕ → 𝔼 := fun n ↦ (5 * n : ℝ) • e with hcdef
  have hcd : ∀ a b : ℕ, a ≠ b → 5 ≤ dist (c a) (c b) := by
    intro a b hab
    rw [dist_eq_norm, hcdef]
    simp only [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs, ← mul_sub, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    have : (1 : ℝ) ≤ |(a : ℝ) - b| := by
      rcases lt_or_gt_of_ne hab with h | h
      · have hab' : (a : ℝ) < b := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_pos (sub_pos.2 hab')]
        have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
        linarith
      · have hab' : (b : ℝ) < a := by exact_mod_cast h
        rw [abs_of_pos (sub_pos.2 hab')]
        have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
        linarith
    linarith
  choose v hv hvn using fun n ↦ exists_translate_mem_sobolevSpace (p := p) hφs hφc (c n)
  -- the translates are bounded in `W^{1,p}`
  have hbdd : ∃ M : ℝ, ∀ n, ‖v n‖ ≤ M :=
    ⟨_, fun n ↦ (bookNorm_equiv (v n)).1.trans (hvn n).le⟩
  obtain ⟨ψ, w, hψ, hw⟩ := hc.exists_subseq_tendsto v hbdd
  -- and pairwise separated in `L^p`
  have hsep : ∀ a b : ℕ, a ≠ b → eLpNorm (φ : 𝔼 → ℝ) p volume
      ≤ eLpNorm (SobolevMultiIndex.fn (v a) - SobolevMultiIndex.fn (v b)) p volume := by
    intro a b hab
    have hzero : ∀ x ∈ closedBall (c a) 2, φ (x - c b) = 0 := fun x hx ↦ by
      refine φ.zero_of_le_dist ?_
      rw [dist_zero_right, ← dist_eq_norm]
      have h1 := hcd a b hab
      have h2 := dist_triangle (c a) x (c b)
      rw [mem_closedBall, dist_comm] at hx
      simp only [hφ]
      linarith
    have hsupp : Function.support (fun x ↦ φ (x - c a)) ⊆ closedBall (c a) 2 := fun x hx ↦ by
      rw [mem_closedBall]
      by_contra hlt
      refine hx (φ.zero_of_le_dist ?_)
      rw [dist_zero_right, ← dist_eq_norm]
      simp only [hφ]
      exact (not_le.1 hlt).le
    have hmp : MeasurePreserving (fun x : 𝔼 ↦ x - c a) volume volume :=
      measurePreserving_sub_right _ (c a)
    have hae : SobolevMultiIndex.fn (v a) - SobolevMultiIndex.fn (v b)
        =ᵐ[volume] fun x ↦ φ (x - c a) - φ (x - c b) := by
      filter_upwards [hv a, hv b] with x hxa hxb
      simp [hxa, hxb]
    calc eLpNorm (φ : 𝔼 → ℝ) p volume
        = eLpNorm (fun x ↦ φ (x - c a)) p volume :=
          (eLpNorm_comp_measurePreserving (p := p) φ.continuous.aestronglyMeasurable hmp).symm
      _ = eLpNorm (fun x ↦ φ (x - c a)) p (volume.restrict (closedBall (c a) 2)) :=
          (eLpNorm_restrict_eq_of_support_subset
            (φ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
            hsupp).symm
      _ = eLpNorm (fun x ↦ φ (x - c a) - φ (x - c b)) p (volume.restrict (closedBall (c a) 2)) := by
          refine eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_closedBall fun x hx ↦ ?_)
          simp only [hzero x hx, sub_zero]
      _ ≤ eLpNorm (fun x ↦ φ (x - c a) - φ (x - c b)) p volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = _ := (eLpNorm_congr_ae hae).symm
  -- a convergent subsequence would be Cauchy, against the separation
  have hcs := hw.cauchySeq
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.1 hcs (eLpNorm (φ : 𝔼 → ℝ) p volume).toReal
    (ENNReal.toReal_pos hφp.ne' hφt)
  have h1 := hM (M + 1) (Nat.le_succ M)
  have hne : ψ (M + 1) ≠ ψ M := hψ.injective.ne (Nat.succ_ne_self M)
  have h2 := hsep _ _ hne
  rw [Lp.dist_def] at h1
  have hcoe : ⇑(SobolevMultiIndex.toLpₗ ℝ
        (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) 1 p ⊤ volume h
        (v (ψ (M + 1))))
      - ⇑(SobolevMultiIndex.toLpₗ ℝ
        (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) 1 p ⊤ volume h (v (ψ M)))
      =ᵐ[volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)]
        SobolevMultiIndex.fn (v (ψ (M + 1))) - SobolevMultiIndex.fn (v (ψ M)) := by
    filter_upwards [SobolevMultiIndex.toLpₗ_coeFn h (v (ψ (M + 1))),
      SobolevMultiIndex.toLpₗ_coeFn h (v (ψ M))] with x hxa hxb
    simp [hxa, hxb]
  rw [eLpNorm_congr_ae hcoe, eLpNorm_restrict_coe_top] at h1
  have hfin : eLpNorm (SobolevMultiIndex.fn (v (ψ (M + 1))) - SobolevMultiIndex.fn (v (ψ M))) p
      volume ≠ ⊤ :=
    ((SobolevEuclidean.memLp_fn (v (ψ (M + 1)))).sub
      (SobolevEuclidean.memLp_fn (v (ψ M)))).eLpNorm_ne_top
  exact absurd (ENNReal.toReal_mono hfin h2) (not_le.2 h1)

end NonCompact
/-! ### B. The case $\Omega \subset \mathbb{R}^N$ -/

section Domain

variable {d : ℕ}

/-- The space $\mathbb{R}^N$, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- **Section 9.3.B** of [brezis2011functional], the standing hypothesis. An open set
$\Omega \subseteq \mathbb{R}^N$ **satisfies the standing hypothesis** if $\Omega$ is of class
$C^1$ and its boundary $\Gamma$ is bounded, or if $\Omega = \mathbb{R}^N_+ = \{x : x_N > 0\}$.

The source writes "we suppose here that $\Omega$ is an open set of class $C^1$ with $\Gamma$
bounded, or else that $\Omega = \mathbb{R}^N_+$". In both cases Theorem 9.7 gives an extension
operator $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ for every $p$
(`Brezis.Chapter09.IsClassC1BoundedFrontierOrHalfSpace.isSobolevExtensionDomainAll`), and the
proofs of Corollaries 9.14 and 9.15 use only this operator. -/
def IsClassC1BoundedFrontierOrHalfSpace (Ω : Opens 𝔼) : Prop :=
  (IsClassC1 (Ω : Set 𝔼) ∧ Bornology.IsBounded (frontier (Ω : Set 𝔼))) ∨
    Ω = EuclideanSpace.upperHalfSpaceOpens d

/-- A bounded open set of class $C^1$ satisfies the standing hypothesis of Section 9.3.B. -/
theorem isClassC1BoundedFrontierOrHalfSpace_of_isBounded {Ω : Opens 𝔼}
    (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    IsClassC1BoundedFrontierOrHalfSpace Ω :=
  Or.inl ⟨hΩ, hb.closure.subset frontier_subset_closure⟩

/-- The half space $\mathbb{R}^N_+$ satisfies the standing hypothesis of Section 9.3.B. -/
theorem isClassC1BoundedFrontierOrHalfSpace_upperHalfSpace :
    IsClassC1BoundedFrontierOrHalfSpace (EuclideanSpace.upperHalfSpaceOpens d) :=
  Or.inr rfl

/-- If $\Omega$ satisfies the standing hypothesis of Section 9.3.B, then for every
$1 \le q \le \infty$ there is an extension operator $W^{1,q}(\Omega) \to W^{1,q}(\mathbb{R}^N)$.

The conclusion is `IsSobolevExtensionDomainAll`. For $\Omega$ of class $C^1$ with bounded
boundary it is Theorem 9.7 (`IsSobolevExtensionDomainAll.of_isContDiffChartDomain`), and for the
half space it is Lemma 9.2 (`IsSobolevExtensionDomain.upperHalfSpace`).

**Reading.** The extension property supplies an operator with a bound for each exponent.
 The source specifies a constant depending only on the domain. -/
theorem IsClassC1BoundedFrontierOrHalfSpace.isSobolevExtensionDomainAll {Ω : Opens 𝔼}
    (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω) : IsSobolevExtensionDomainAll (d + 1) Ω := by
  rcases hΩ with ⟨h1, h2⟩ | rfl
  · exact IsSobolevExtensionDomainAll.of_isContDiffChartDomain h1 h2
  · intro q _
    exact IsSobolevExtensionDomain.upperHalfSpace

/-- If $\Omega$ satisfies the standing hypothesis of Section 9.3.B and $1 \le p \le \infty$, then
there is an extension operator $W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$
(`IsSobolevExtensionDomain`). -/
theorem IsClassC1BoundedFrontierOrHalfSpace.isSobolevExtensionDomain {Ω : Opens 𝔼}
    (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsSobolevExtensionDomain (d + 1) p Ω :=
  hΩ.isSobolevExtensionDomainAll p

/-! ### Corollary 9.14 -/

variable {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Corollary 9.14** of [brezis2011functional], the case $p < N$. Let $\Omega$ satisfy the
standing hypothesis of Section 9.3.B, let $1 \le p < N$ and $1/p^* = 1/p - 1/N$. Then
$W^{1,p}(\Omega) \subset L^q(\Omega)$ with continuous injection for every $q \in [p, p^*]$.

The source states the injection into $L^{p^*}(\Omega)$; the other exponents follow as in
Corollary 9.10. The proof composes the extension operator of Theorem 9.7 with Theorem 9.9, and
specializes `SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_lt`.

**Generalization.** The subcritical injection covers all $q$ between $p$ and $p^*$ by
 interpolation. The source displays the endpoint $p^*$. -/
theorem corollary_9_14_lt [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    {p' : ℝ≥0} (hpN : p < ((d + 1 : ℕ) : ℝ≥0)) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹)
    (hpq : p ≤ q) (hqp' : q ≤ p') : IsContinuousInjectionLp (d + 1) 1 p q Ω :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_lt
    (hΩ.isSobolevExtensionDomain p) hpN hp' hpq hqp'⟩

/-- **Corollary 9.14** of [brezis2011functional], the case $p = N$. Let $\Omega$ satisfy the
standing hypothesis of Section 9.3.B and let $N \ge 2$. Then
$W^{1,N}(\Omega) \subset L^q(\Omega)$ with continuous injection for every $q \in [N, +\infty)$.

**Reading.** The case is stated for $N \ge 2$, because it rests on Corollary 9.11, whose proof
needs $N \ge 2$. For $N = 1$ the statement is a case of Theorem 8.8.

Here $N = d + 1$, and $N \ge 2$ is `1 ≤ d`. The proof composes the extension operator with
Corollary 9.11, and specializes
`SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_eq`. -/
theorem corollary_9_14_eq [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hd : 1 ≤ d) (hp : p = ((d + 1 : ℕ) : ℝ≥0)) (hq : p ≤ q) :
    IsContinuousInjectionLp (d + 1) 1 p q Ω := by
  subst hp
  have : Fact (1 ≤ ((d + 1 : ℕ) : ℝ≥0∞)) := ‹_›
  exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_eq
    (hΩ.isSobolevExtensionDomain _) (by omega) hq⟩

/-- **Corollary 9.14** of [brezis2011functional], the case $p > N$, the injection. Let $\Omega$
satisfy the standing hypothesis of Section 9.3.B and let $N < p < \infty$. Then
$W^{1,p}(\Omega) \subset L^\infty(\Omega)$ with continuous injection.

The proof composes the extension operator with Theorem 9.12, and specializes
`SobolevEuclidean.isContinuousEmbedding_toLp_top_of_hasSobolevExtension_of_lt`.

**Reading.** This version assumes finite $p$. The endpoint $p=\infty$ embeds into itself. -/
theorem corollary_9_14_gt (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) : IsContinuousInjectionLp (d + 1) 1 p ⊤ Ω :=
  ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_top_of_hasSobolevExtension_of_lt
    (hΩ.isSobolevExtensionDomain p) hp⟩

/-- **Corollary 9.14** of [brezis2011functional], the case $p > N$, the Hölder estimate and
footnote 15. Let $\Omega$ satisfy the standing hypothesis of Section 9.3.B, let $N < p < \infty$
and $\alpha = 1 - N/p$. There is a constant $C \ge 0$ such that every $u \in W^{1,p}(\Omega)$
has a representative $\tilde u$ that is continuous on $\bar\Omega$ and satisfies
$$|\tilde u(x) - \tilde u(y)| \le C \|u\|_{W^{1,p}} |x - y|^\alpha \quad \text{for all } x, y
  \in \bar\Omega,$$
and hence $|u(x) - u(y)| \le C \|u\|_{W^{1,p}} |x - y|^\alpha$ for a.e. $x$ and a.e. $y$ in
$\Omega$. In particular $W^{1,p}(\Omega) \subset C(\bar\Omega)$, up to the choice of a
representative (footnote 15).

The function $\tilde u$ is defined on $\mathbb{R}^N$ and equals $u$ a.e. on $\Omega$. The proof
specializes `SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq`. Its representative
is Morrey's representative of $Pu$, and is in fact continuous and Hölder continuous on all of
$\mathbb{R}^N$.

**Reading.** For finite $p>N$ the estimate holds at all points of the closure for a
 continuous representative, and is also stated almost everywhere for the original class. -/
theorem corollary_9_14_holder (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpace (d + 1) p Ω, ∃ ũ : 𝔼 → ℝ,
      ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
        |ũ x - ũ y| ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p)) ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
        |SobolevMultiIndex.fn u x - SobolevMultiIndex.fn u y|
          ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p) := by
  obtain ⟨C, hC⟩ := SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq
    (hΩ.isSobolevExtensionDomain p) hp
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hα : ((1 - ((d + 1 : ℕ) : ℝ≥0) / p : ℝ≥0) : ℝ) = 1 - ((d + 1 : ℕ) : ℝ) / p := by
    rw [NNReal.coe_sub ((div_le_one (by exact_mod_cast hp0)).2 hp.le)]
    simp
  refine ⟨C, C.coe_nonneg, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, hh, -⟩ := hC u
  have hbound : ∀ x y, |ũ x - ũ y| ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p) := by
    intro x y
    have h1 := hh.dist_le x y
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, hα] at h1
    refine h1.trans ?_
    gcongr
    exact (bookNorm_equiv u).1
  refine ⟨ũ, hc.continuousOn, hae, fun x _ y _ ↦ hbound x y, ?_⟩
  filter_upwards [hae] with x hx
  filter_upwards [hae] with y hy
  rw [hx, hy]
  exact hbound x y

/-- **Corollary 9.14** of [brezis2011functional]. Let $\Omega$ satisfy the standing hypothesis of
Section 9.3.B and let $1 \le p < \infty$. Then, with continuous injections,
$$W^{1,p}(\Omega) \subset L^q(\Omega) \text{ for all } q \in [p, p^*], \ \frac{1}{p^*} =
  \frac{1}{p} - \frac{1}{N}, \quad \text{if } p < N,$$
$$W^{1,p}(\Omega) \subset L^q(\Omega) \text{ for all } q \in [p, +\infty), \quad \text{if } p =
  N \text{ and } N \ge 2,$$
$$W^{1,p}(\Omega) \subset L^\infty(\Omega), \quad \text{if } p > N.$$
Moreover, if $p > N$ and $\alpha = 1 - N/p$, there is $C \ge 0$ such that every
$u \in W^{1,p}(\Omega)$ has a representative $\tilde u$ continuous on $\bar\Omega$ with $|\tilde
u(x) - \tilde u(y)| \le C \|u\|_{W^{1,p}} |x - y|^\alpha$ for all $x, y \in \bar\Omega$, and
hence $|u(x) - u(y)| \le C \|u\|_{W^{1,p}} |x - y|^\alpha$ for a.e. $x, y \in \Omega$. In
particular $W^{1,p}(\Omega) \subset C(\bar\Omega)$.

**Reading.** The case $p = N$ is stated for $N \ge 2$; see `Brezis.Chapter09.corollary_9_14_eq`.

The source allows $1 \le p \le \infty$. The case $p = \infty$ is Theorem 9.12 on $\mathbb{R}^N$
(`Brezis.Chapter09.theorem_9_12_top`) and is not restated on $\Omega$.

**Reading.** The bundled statement uses finite $p$ and includes intermediate exponents in
 the subcritical case. The critical case requires $N \ge 2$. -/
theorem corollary_9_14 (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω) :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < ((d + 1 : ℕ) : ℝ≥0) →
      (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ → p ≤ q → q ≤ p' →
        IsContinuousInjectionLp (d + 1) 1 p q Ω) ∧
    (1 ≤ d → p = ((d + 1 : ℕ) : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLp (d + 1) 1 p q Ω) ∧
    (((d + 1 : ℕ) : ℝ≥0) < p → IsContinuousInjectionLp (d + 1) 1 p ⊤ Ω) ∧
    (((d + 1 : ℕ) : ℝ≥0) < p → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpace (d + 1) p Ω, ∃ ũ : 𝔼 → ℝ,
      ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
        |ũ x - ũ y| ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p)) ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
        |SobolevMultiIndex.fn u x - SobolevMultiIndex.fn u y|
          ≤ C * bookNorm u * ‖x - y‖ ^ (1 - ((d + 1 : ℕ) : ℝ) / p)) :=
  ⟨fun _ _ _ hpN hp' hpq hqp' ↦ corollary_9_14_lt hΩ hpN hp' hpq hqp',
    fun hd hp _ _ hq ↦ corollary_9_14_eq hΩ hd hp hq, corollary_9_14_gt hΩ,
    corollary_9_14_holder hΩ⟩

/-! ### Corollary 9.15 -/

/-- **Corollary 9.15** of [brezis2011functional], the $L^q$ clauses. Let $\Omega$ satisfy the
standing hypothesis of Section 9.3.B, let $m \in \mathbb{N}$ and $1 \le p < \infty$, and assume
$N \ge 2$ or $p > 1$. Then, with continuous injections, $W^{m,p}(\Omega) \subset L^q(\Omega)$
with $1/q = 1/p - m/N$ if $1/p - m/N > 0$; $W^{m,p}(\Omega) \subset L^q(\Omega)$ for all
$q \in [p, +\infty)$ if $1/p - m/N = 0$; and $W^{m,p}(\Omega) \subset L^\infty(\Omega)$ if
$1/p - m/N < 0$.

**Reading.** The hypothesis $N \ge 2$ or $p > 1$ is added, as in
`Brezis.Chapter09.corollary_9_13_lt`.

The proof is "by repeated application of Corollary 9.14" and uses no extension operator on
$W^{m,p}(\Omega)$ (footnote 17). It specializes
`SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension` and
`SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension`.

**Generalization.** The subcritical clause includes zero order, when the injection is the
 identity for $q=p$. -/
theorem corollary_9_15_lp {m : ℕ} (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hN : 2 ≤ d + 1 ∨ 1 < p) :
    (∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], 0 < (p : ℝ)⁻¹ - m / (d + 1 : ℕ) →
      (q : ℝ)⁻¹ = p⁻¹ - m / (d + 1 : ℕ) → IsContinuousInjectionLp (d + 1) m p q Ω) ∧
    ((p : ℝ)⁻¹ - m / (d + 1 : ℕ) = 0 → ∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLp (d + 1) m p q Ω) ∧
    ((p : ℝ)⁻¹ - m / (d + 1 : ℕ) < 0 → IsContinuousInjectionLp (d + 1) m p ⊤ Ω) := by
  have hall := hΩ.isSobolevExtensionDomainAll
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  refine ⟨fun q _ hpos hq ↦ ?_, fun hm q _ hpq ↦ ?_, fun hm ↦ ?_⟩
  · have hq0 : (0 : ℝ) < q := by
      rw [← inv_pos, hq]
      exact hpos
    have hpq : p ≤ q := by
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hq0 hp0, hq]
      exact sub_le_self _ (by positivity)
    exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension hall hN
      hpq hq.ge⟩
  · exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension hall hN
      hpq (hm ▸ by positivity)⟩
  · obtain ⟨C, θ, hC0, -, -, -, hC⟩ :=
      SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension hall hN
        (div_lt_of_inv_sub_div_neg hp0 hm)
    refine isContinuousInjectionLp_iff.2 ⟨fun u ↦ ?_, C, hC0, fun u ↦ ?_⟩
    · exact SobolevEuclidean.memLp_fn_top_of_order_of_hasSobolevExtension hall hN
        (div_lt_of_inv_sub_div_neg hp0 hm) u
    · obtain ⟨ũ, hc, hae, hb, -⟩ := hC u
      rw [eLpNorm_congr_ae hae]
      refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal (C * ‖u‖))
        hc.aestronglyMeasurable.restrict (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hb x)

/-- **Corollary 9.15** of [brezis2011functional], the $C^k(\bar\Omega)$ clause (footnote 16). Let
$\Omega$ satisfy the standing hypothesis of Section 9.3.B, let $m \in \mathbb{N}$ and
$1 \le p < \infty$, and assume $N \ge 2$ or $p > 1$. Assume that $m - N/p > 0$ is not an
integer, and let $k = [m - N/p]$ and $\theta = m - N/p - k$. There is $C \ge 0$ such that every
$u \in W^{m,p}(\Omega)$ has a representative $\tilde u \in C^k(\bar\Omega)$ with
$$\|D^j \tilde u(x)\| \le C \|u\|_{W^{m,p}} \quad \text{for all } j \le k \text{ and } x \in
  \Omega,$$
$$\|D^k \tilde u(x) - D^k \tilde u(y)\| \le C \|u\|_{W^{m,p}} |x - y|^\theta \quad \text{for all
  } x, y \in \Omega.$$
Here $C^k(\bar\Omega)$ is the space of footnote 16, the functions $u \in C^k(\Omega)$ such that
$D^\alpha u$ has a continuous extension to $\bar\Omega$ for every $|\alpha| \le k$.

**Reading.** The hypothesis $N \ge 2$ or $p > 1$ is added, as in
`Brezis.Chapter09.corollary_9_13_lt`.

The space $C^k(\bar\Omega)$ is `ContDiffOnClosure ℝ k · Ω` of the module
`Numlib.Analysis.Calculus.ContDiffOnClosure`, and the derivative of order $j$ is
`iteratedFDeriv ℝ j ũ`. The proof specializes
`SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order`.

**Reading.** The statement uses continuous boundary extensions of the iterated Fréchet
 derivatives and pointwise estimates on the open set. -/
theorem corollary_9_15_ck {m : ℕ} (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hN : 2 ≤ d + 1 ∨ 1 < p) (hm : 0 < (m : ℝ) - (d + 1 : ℕ) / p)
    (hint : ∀ j : ℕ, (m : ℝ) - (d + 1 : ℕ) / p ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher (d + 1) m p Ω, ∃ ũ : 𝔼 → ℝ,
      ContDiffOnClosure ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ Ω ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      (∀ j ≤ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊, ∀ x ∈ (Ω : Set 𝔼),
        ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * bookNormHigher u) ∧
      ∀ x ∈ (Ω : Set 𝔼), ∀ y ∈ (Ω : Set 𝔼),
        ‖iteratedFDeriv ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ x
            - iteratedFDeriv ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ y‖
          ≤ C * bookNormHigher u
            * ‖x - y‖ ^ ((m : ℝ) - (d + 1 : ℕ) / p - ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ := ⟨_, rfl⟩
  have hθ0 : 0 < (m : ℝ) - (d + 1 : ℕ) / p - k := by
    rw [hk]
    exact lt_of_le_of_ne (sub_nonneg.2 (Nat.floor_le hm.le)) fun h ↦ hint _ (sub_eq_zero.1 h.symm)
  have hθ1 : (m : ℝ) - (d + 1 : ℕ) / p - k < 1 := by
    rw [hk, sub_lt_iff_lt_add']
    exact Nat.lt_floor_add_one _
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order
    (N := d + 1) (m := m) (k := k) hΩ.isSobolevExtensionDomainAll hN hθ0 hθ1
  rw [← hk]
  refine ⟨C, hC0, fun u ↦ ?_⟩
  obtain ⟨ũ, -, hũ, hae, hG, G, hGc, hGeq, hGh⟩ := hC u
  have hnorm : C * ‖u‖ ≤ C * bookNormHigher u :=
    mul_le_mul_of_nonneg_left (bookNormHigher_equiv u).1 hC0
  refine ⟨ũ, ⟨hũ, fun j hj ↦ ?_⟩, hae, fun j hj x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · obtain ⟨G', hG'c, hG'eq, -⟩ := hG j (by exact_mod_cast hj)
    exact ⟨G', hG'c.continuousOn, hG'eq.symm⟩
  · obtain ⟨G', -, hG'eq, hG'b⟩ := hG j hj
    rw [hG'eq hx]
    exact (hG'b x).trans hnorm
  · rw [hGeq hx, hGeq hy]
    exact (hGh x y).trans (mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (norm_nonneg _) _))


/-- **Corollary 9.15** of [brezis2011functional]. Let $\Omega$ be of class $C^1$ with $\Gamma$
bounded, or $\Omega = \mathbb{R}^N_+$, let $m \in \mathbb{N}$ and $1 \le p < \infty$, and assume
$N \ge 2$ or $p > 1$. Then the conclusion of Corollary 9.13 holds with $\mathbb{R}^N$ replaced
by $\Omega$: the three $L^q$ clauses of `Brezis.Chapter09.corollary_9_15_lp` hold, and if
$m - N/p > 0$ is not an integer, then $W^{m,p}(\Omega) \subset C^k(\bar\Omega)$ with
$k = [m - N/p]$, with the bounds of `Brezis.Chapter09.corollary_9_15_ck`.

**Reading.** The hypothesis $N \ge 2$ or $p > 1$ is added, as in
`Brezis.Chapter09.corollary_9_13_lt`.

**Generalization.** The subcritical clause includes zero order, when the injection is the
 identity for $q=p$. -/
theorem corollary_9_15 {m : ℕ} (hΩ : IsClassC1BoundedFrontierOrHalfSpace Ω)
    (hN : 2 ≤ d + 1 ∨ 1 < p) :
    ((∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], 0 < (p : ℝ)⁻¹ - m / (d + 1 : ℕ) →
      (q : ℝ)⁻¹ = p⁻¹ - m / (d + 1 : ℕ) → IsContinuousInjectionLp (d + 1) m p q Ω) ∧
    ((p : ℝ)⁻¹ - m / (d + 1 : ℕ) = 0 → ∀ q : ℝ≥0, ∀ [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLp (d + 1) m p q Ω) ∧
    ((p : ℝ)⁻¹ - m / (d + 1 : ℕ) < 0 → IsContinuousInjectionLp (d + 1) m p ⊤ Ω)) ∧
    (0 < (m : ℝ) - (d + 1 : ℕ) / p → (∀ j : ℕ, (m : ℝ) - (d + 1 : ℕ) / p ≠ j) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevSpaceHigher (d + 1) m p Ω, ∃ ũ : 𝔼 → ℝ,
        ContDiffOnClosure ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ Ω ∧
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
        (∀ j ≤ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊, ∀ x ∈ (Ω : Set 𝔼),
          ‖iteratedFDeriv ℝ j ũ x‖ ≤ C * bookNormHigher u) ∧
        ∀ x ∈ (Ω : Set 𝔼), ∀ y ∈ (Ω : Set 𝔼),
          ‖iteratedFDeriv ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ x
              - iteratedFDeriv ℝ ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊ ũ y‖
            ≤ C * bookNormHigher u
              * ‖x - y‖ ^ ((m : ℝ) - (d + 1 : ℕ) / p - ⌊(m : ℝ) - (d + 1 : ℕ) / p⌋₊)) :=
  ⟨corollary_9_15_lp hΩ hN, corollary_9_15_ck hΩ hN⟩
/-! ### Theorem 9.16: the Rellich–Kondrachov theorem -/

/-- **Theorem 9.16** of [brezis2011functional], the injection
$W^{1,p}(\Omega) \subset C(\bar\Omega)$. Let $\Omega$ be a bounded open set of class $C^1$ and
$N < p < \infty$. The **injection $W^{1,p}(\Omega) \subset C(\bar\Omega)$** is the bounded
linear map that sends $u$ to the restriction to the compact set $\bar\Omega$ of the continuous
representative of $u$ (Corollary 9.14, `Brezis.Chapter09.corollary_9_14_holder`).

The map is the backbone's `SobolevEuclidean.toContinuousMapL` for the set `closure Ω`. -/
noncomputable def toContinuousMapClosure (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hp : ((d + 1 : ℕ) : ℝ≥0) < p) :
    sobolevSpace (d + 1) p Ω →L[ℝ] C(closure (Ω : Set 𝔼), ℝ) :=
  haveI : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  SobolevEuclidean.toContinuousMapL
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure))
    hp (closure (Ω : Set 𝔼))

/-- Let $\Omega$ be a bounded open set of class $C^1$, $N < p < \infty$ and $u \in W^{1,p}(\Omega)$.
There is a continuous function $\tilde u$ on $\mathbb{R}^N$ with $u = \tilde u$ a.e. on $\Omega$
whose restriction to $\bar\Omega$ is the image of $u$ under
`Brezis.Chapter09.toContinuousMapClosure`.

**Reading.** The representative on the closure is realized as the restriction of a continuous
 function on all of $\mathbb{R}^N$. -/
theorem exists_continuous_ae_eq_toContinuousMapClosure (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hp : ((d + 1 : ℕ) : ℝ≥0) < p)
    (u : sobolevSpace (d + 1) p Ω) :
    ∃ ũ : 𝔼 → ℝ, Continuous ũ ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      ∀ x : closure (Ω : Set 𝔼), toContinuousMapClosure hΩ hb hp u x = ũ x := by
  have : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  refine ⟨_, (SobolevEuclidean.contRep hp _).continuous,
    SobolevEuclidean.fn_ae_eq_toContinuousMapL (IsSobolevExtensionDomain.of_isContDiffChartDomain
      hΩ (hb.closure.subset frontier_subset_closure)) hp u, fun x ↦ rfl⟩

/-- **Theorem 9.16** of [brezis2011functional] (Rellich–Kondrachov), the case $p < N$. Let $\Omega$
be a bounded open set of class $C^1$, $1 \le p < N$ and $1/p^* = 1/p - 1/N$. Then
$W^{1,p}(\Omega) \subset L^q(\Omega)$ with compact injection for every $q \in [1, p^*)$.

The proof applies Theorem 4.26 (Kolmogorov–M. Riesz–Fréchet) to the image of the unit ball under
the extension operator, with the translation estimate of Proposition 9.3 and the interpolation
inequality. It specializes `SobolevEuclidean.isCompactEmbedding_toLp_of_lt`. -/
theorem theorem_9_16_lt [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {p' : ℝ≥0} (hpN : p < ((d + 1 : ℕ) : ℝ≥0))
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹) (hqp' : q < p') :
    IsCompactInjectionLp (d + 1) 1 p q Ω :=
  ⟨_, SobolevEuclidean.isCompactEmbedding_toLp_of_lt hΩ hb hpN hp' hqp'⟩

/-- **Theorem 9.16** of [brezis2011functional] (Rellich–Kondrachov), the case $p = N$. Let $\Omega$
be a bounded open set of class $C^1$ and $N \ge 2$. Then $W^{1,N}(\Omega) \subset L^q(\Omega)$
with compact injection for every $q \in [N, +\infty)$.

**Reading.** The case is stated for $N \ge 2$, as Corollary 9.14 for $p = N$. For $N = 1$ the
statement is a case of Theorem 8.8.

The source says that the case $p = N$ reduces to the case $p < N$:
$W^{1,N}(\Omega) \subset W^{1,r}(\Omega)$ for some $r < N$ with $r^* > q$. The proof specializes
`SobolevEuclidean.isCompactEmbedding_toLp_of_eq`. -/
theorem theorem_9_16_eq [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hd : 1 ≤ d) (hp : p = ((d + 1 : ℕ) : ℝ≥0))
    (hq : p ≤ q) : IsCompactInjectionLp (d + 1) 1 p q Ω := by
  obtain ⟨h, -⟩ := corollary_9_14_eq (isClassC1BoundedFrontierOrHalfSpace_of_isBounded hΩ hb) hd
    hp hq
  subst hp
  exact ⟨h, SobolevEuclidean.isCompactEmbedding_toLp_of_eq hΩ hb hd h⟩

/-- **Theorem 9.16** of [brezis2011functional] (Rellich–Kondrachov), the case $p > N$. Let $\Omega$
be a bounded open set of class $C^1$ and $N < p < \infty$. Then the injection
$W^{1,p}(\Omega) \subset C(\bar\Omega)$, $u \mapsto \tilde u|_{\bar\Omega}$, is compact.

The injection is `Brezis.Chapter09.toContinuousMapClosure`. By Corollary 9.14 the image of the
unit ball is bounded and uniformly Hölder continuous in $C(\bar\Omega)$, so the Ascoli–Arzelà
theorem applies. The proof specializes
`SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt`.

**Reading.** This version of the compact embedding is stated for finite $p>N$. The source
 does not state that upper restriction. -/
theorem theorem_9_16_gt (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) :
    haveI : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
    IsCompactEmbedding (toContinuousMapClosure hΩ hb hp).toLinearMap := by
  have : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  exact SobolevEuclidean.isCompactEmbedding_toContinuousMapL_of_gt hΩ hb hp subset_closure

/-- **Theorem 9.16** of [brezis2011functional], last sentence. Let $\Omega$ be a bounded open set of
class $C^1$ and $1 \le p < \infty$, and assume $p \ne 1$ or $N \ge 2$. Then
$W^{1,p}(\Omega) \subset L^p(\Omega)$ with compact injection.

**Reading.** The source states this "for all $p$ (and all $N$)". The case $N = p = 1$, an
interval, is a case of Theorem 8.8 and is left out here.

The proof combines the three cases $p < N$, $p = N$ with $N \ge 2$, and $p > N$ through
$C(\bar\Omega)$. It specializes `SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one`. -/
theorem theorem_9_16_self (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hd : p ≠ 1 ∨ 1 ≤ d) : IsCompactInjectionLp (d + 1) 1 p p Ω :=
  ⟨_, SobolevEuclidean.isCompactEmbedding_toLp_self_of_ne_one hΩ hb hd⟩

/-- **Theorem 9.16** of [brezis2011functional] (Rellich–Kondrachov). Let $\Omega$ be a bounded open
set of class $C^1$ and $1 \le p < \infty$. Then the following injections are compact:
$$W^{1,p}(\Omega) \subset L^q(\Omega) \text{ for all } q \in [1, p^*), \ \frac{1}{p^*} =
  \frac{1}{p} - \frac{1}{N}, \quad \text{if } p < N,$$
$$W^{1,p}(\Omega) \subset L^q(\Omega) \text{ for all } q \in [p, +\infty), \quad \text{if } p =
  N \text{ and } N \ge 2,$$
$$W^{1,p}(\Omega) \subset C(\bar\Omega), \quad \text{if } p > N.$$
In particular $W^{1,p}(\Omega) \subset L^p(\Omega)$ with compact injection if $p \ne 1$ or
$N \ge 2$.

**Reading.** The case $p = N$ assumes $N \ge 2$, and the last sentence leaves out $N = p = 1$;
see `Brezis.Chapter09.theorem_9_16_eq` and `Brezis.Chapter09.theorem_9_16_self`.

The injection into $C(\bar\Omega)$ is `Brezis.Chapter09.toContinuousMapClosure`.

**Reading.** The bundled compact embeddings use finite $p$. This leaves out $p=\infty$ as well
 as the $p=N=1$ case of the final self-embedding assertion. -/
theorem theorem_9_16 (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < ((d + 1 : ℕ) : ℝ≥0) →
      (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ → q < p' → IsCompactInjectionLp (d + 1) 1 p q Ω) ∧
    (1 ≤ d → p = ((d + 1 : ℕ) : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsCompactInjectionLp (d + 1) 1 p q Ω) ∧
    (∀ hp : ((d + 1 : ℕ) : ℝ≥0) < p,
      haveI : CompactSpace (closure (Ω : Set 𝔼)) :=
        isCompact_iff_compactSpace.1 hb.isCompact_closure
      IsCompactEmbedding (toContinuousMapClosure hΩ hb hp).toLinearMap) ∧
    (p ≠ 1 ∨ 1 ≤ d → IsCompactInjectionLp (d + 1) 1 p p Ω) :=
  ⟨fun _ _ _ hpN hp' hqp' ↦ theorem_9_16_lt hΩ hb hpN hp' hqp',
    fun hd hp _ _ hq ↦ theorem_9_16_eq hΩ hb hd hp hq, theorem_9_16_gt hΩ hb,
    theorem_9_16_self hΩ hb⟩

/-! ### Remark 15: equivalent norms -/

/-- **Remark 15** of Chapter 9 of [brezis2011functional], the case $p < N$. Let $\Omega$ be a
bounded open set of class $C^1$, $1 \le p < N$, $1/p^* = 1/p - 1/N$ and $1 \le q \le p^*$. There
are constants $C_1, C_2$ with
$$\|u\|_{W^{1,p}} \le C_1 \big(\|\nabla u\|_{L^p(\Omega)} + \|u\|_{L^q(\Omega)}\big), \qquad
  \|\nabla u\|_{L^p(\Omega)} + \|u\|_{L^q(\Omega)} \le C_2 \|u\|_{W^{1,p}}$$
for all $u \in W^{1,p}(\Omega)$. Thus the norm $\|\nabla u\|_p + \|u\|_q$ is equivalent to the
norm of $W^{1,p}(\Omega)$.

The proof specializes `SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_lt`, which
uses Corollary 9.14, the interpolation inequality and an absorption argument. It passes to the
norms of the source through
`Brezis.Chapter09.bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add`. -/
theorem remark_9_15_lt (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {p' : ℝ≥0} (hpN : p < ((d + 1 : ℕ) : ℝ≥0)) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hqp' : q ≤ p') :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace (d + 1) p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u :=
  let ⟨h₁, h₂⟩ := SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_lt
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure))
    hb hpN hp' hq hqp'
  bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add h₁ h₂

/-- **Remark 15** of Chapter 9 of [brezis2011functional], the case $p = N$. Let $\Omega$ be a
bounded open set of class $C^1$, $N \ge 2$, and $1 \le q < \infty$. There are constants
$C_1, C_2$ with
$$\|u\|_{W^{1,N}} \le C_1 \big(\|\nabla u\|_{L^N(\Omega)} + \|u\|_{L^q(\Omega)}\big), \qquad
  \|\nabla u\|_{L^N(\Omega)} + \|u\|_{L^q(\Omega)} \le C_2 \|u\|_{W^{1,N}}$$
for all $u \in W^{1,N}(\Omega)$.

**Reading.** The case is stated for $N \ge 2$, as Corollary 9.14 for $p = N$.

The proof specializes
`SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_eq_finrank`. -/
theorem remark_9_15_eq (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hd : 1 ≤ d) (hp : p = ((d + 1 : ℕ) : ℝ≥0)) {q : ℝ≥0} (hq : 1 ≤ q) :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace (d + 1) p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u := by
  subst hp
  have : Fact (1 ≤ ((d + 1 : ℕ) : ℝ≥0∞)) := ‹_›
  obtain ⟨h₁, h₂⟩ := SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_eq_finrank
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure))
    hb (by omega) hq
  exact bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add h₁ h₂

/-- **Remark 15** of Chapter 9 of [brezis2011functional], the case $p > N$. Let $\Omega$ be a
bounded open set of class $C^1$, $N < p < \infty$, and $1 \le q \le \infty$. There are constants
$C_1, C_2$ with
$$\|u\|_{W^{1,p}} \le C_1 \big(\|\nabla u\|_{L^p(\Omega)} + \|u\|_{L^q(\Omega)}\big), \qquad
  \|\nabla u\|_{L^p(\Omega)} + \|u\|_{L^q(\Omega)} \le C_2 \|u\|_{W^{1,p}}$$
for all $u \in W^{1,p}(\Omega)$.

The proof specializes `SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_gt`.

**Reading.** The range $p>N$ is restricted to finite Sobolev exponents, while $q=\infty$
 is included. -/
theorem remark_9_15_gt (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hp : ((d + 1 : ℕ) : ℝ≥0) < p) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace (d + 1) p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u :=
  let ⟨h₁, h₂⟩ := SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_gt
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ
      (hb.closure.subset frontier_subset_closure))
    hb hp hq
  bookNorm_equiv_gradient_add_of_norm_equiv_gradNorm_add h₁ h₂

/-- **Remark 15** of Chapter 9 of [brezis2011functional]. Let $\Omega$ be a bounded open set of
class $C^1$ and $1 \le p < \infty$. The norm $\|\nabla u\|_{L^p(\Omega)} + \|u\|_{L^q(\Omega)}$
is equivalent to the norm $\|u\|_{W^{1,p}}$ on $W^{1,p}(\Omega)$, that is, there are constants
$C_1, C_2$ with
$$\|u\|_{W^{1,p}} \le C_1 \big(\|\nabla u\|_p + \|u\|_q\big), \qquad \|\nabla u\|_p + \|u\|_q
  \le C_2 \|u\|_{W^{1,p}},$$
so long as $1 \le q \le p^*$ if $1 \le p < N$; $1 \le q < \infty$ if $p = N$ and $N \ge 2$; and
$1 \le q \le \infty$ if $p > N$.

**Reading.** The case $p = N$ assumes $N \ge 2$; see `Brezis.Chapter09.remark_9_15_eq`.

**Reading.** The library handles finite Sobolev exponents. The critical clause has $N \ge 2$. -/
theorem remark_9_15 (hΩ : IsClassC1 (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hcase : (∃ p' : ℝ≥0, p < ((d + 1 : ℕ) : ℝ≥0) ∧ (p' : ℝ)⁻¹ = p⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ ∧
        q ≤ p') ∨
      (1 ≤ d ∧ p = ((d + 1 : ℕ) : ℝ≥0) ∧ q ≠ ⊤) ∨ ((d + 1 : ℕ) : ℝ≥0) < p) :
    ∃ C₁ C₂ : ℝ, ∀ u : sobolevSpace (d + 1) p Ω,
      bookNorm u ≤ C₁ * ((eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal) ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        + (eLpNorm (SobolevMultiIndex.fn u) q (volume.restrict (Ω : Set 𝔼))).toReal
          ≤ C₂ * bookNorm u := by
  rcases hcase with ⟨p', hpN, hp', hqp'⟩ | ⟨hd, hp, hqt⟩ | hp
  · exact remark_9_15_lt hΩ hb hpN hp' hq hqp'
  · lift q to ℝ≥0 using hqt
    exact remark_9_15_eq hΩ hb hd hp (by exact_mod_cast hq)
  · exact remark_9_15_gt hΩ hb hp hq

end Domain

/-! ### Remark 16: the limiting case $p = N$ -/

section LimitingCase

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **Remark 16** of Chapter 9 of [brezis2011functional] (the limiting case $p = N$). Let $N \ge 2$
and $0 < \alpha < 1 - 1/N$, let $\Omega = \{x \in \mathbb{R}^N : |x| < 1/2\}$, and let
$u(x) = (\log 1/|x|)^\alpha$. Then $u \in W^{1,N}(\Omega)$, but $u \notin L^\infty(\Omega)$.
Thus a function of $W^{1,N}(\Omega)$ need not be bounded.

For $N = 1$ there is no admissible $\alpha$. The proof uses the backbone's
`memSobolevMultiIndex_logRpow` and `eLpNorm_logRpow_top`. The weak gradient is
$-\alpha (\log 1/|x|)^{\alpha - 1} x / |x|^2$ away from the origin. The formula also gives the
weak gradient on the ball, and the radial integral
$\int_0^{1/2} (\log 1/r)^{(\alpha - 1)N} r^{-1} \, dr$ is finite because $\alpha < 1 - 1/N$.
Trudinger's inequality, which the source quotes without
proof, is not restated.

**Reading.** The logarithmic example is stated as a failure of essential boundedness. The
 dimension restriction $N\ge 2$ follows from the stated range for $\alpha$. -/
theorem remark_9_16 (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α) (hα1 : α < 1 - 1 / N) :
    (∃ u : sobolevSpace N N ⟨ball 0 (1 / 2), isOpen_ball⟩,
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (ball (0 : 𝔼) (1 / 2))]
        fun x ↦ Real.log (1 / ‖x‖) ^ α) ∧
    ¬ MemLp (fun x : 𝔼 ↦ Real.log (1 / ‖x‖) ^ α) ⊤ (volume.restrict (ball (0 : 𝔼) (1 / 2))) := by
  have : Fact (1 ≤ (N : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ N)⟩
  refine ⟨(exists_fn_ae_eq_iff _).2 (memSobolevMultiIndex_logRpow hN hα hα1), fun h ↦ ?_⟩
  exact h.eLpNorm_ne_top (eLpNorm_logRpow_top (by omega) hα)

end LimitingCase

end Brezis.Chapter09
