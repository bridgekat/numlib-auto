/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, beside the whole-space
inequalities of `Numlib/Analysis/Sobolev/Embedding.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Holder
import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.InnerProductSpace.NormPow
import Numlib.Analysis.Sobolev.Chart
import Numlib.Analysis.Sobolev.Embedding
import Numlib.Analysis.Sobolev.Zero

/-!
# Sobolev embeddings on a domain with an extension operator

Let $\Omega \subseteq \mathbb{R}^N$ be open. This module proves the Sobolev embeddings of
$W^{1,p}(\Omega)$ and $W^{m,p}(\Omega)$ on a domain that has an extension operator: a bounded linear
map $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ with $Pu = u$ almost everywhere on $\Omega$. The
presentation follows [brezis2011functional], §9.3.B: Corollary 9.14 with footnote 15, Corollary 9.15
with footnotes 16 and 17, and Remarks 15, 16 and 20. For $1 \le p < N$ and $1/p^* = 1/p - 1/N$, the
space $W^{1,p}(\Omega)$ embeds continuously in $L^q(\Omega)$ for $p \le q \le p^*$. For
$p = N \ge 2$ it embeds in $L^q(\Omega)$ for $N \le q < \infty$. For $N < p < \infty$ every
$u \in W^{1,p}(\Omega)$ has a representative that is continuous on $\bar\Omega$, bounded by
$C \|u\|$ and Hölder continuous of exponent $1 - N/p$ with constant $C \|u\|$. Repeated application
gives $W^{m,p}(\Omega) \subset L^q(\Omega)$ for $p \le q < \infty$ with $1/p - m/N \le 1/q$,
$W^{m,p}(\Omega) \subset L^\infty(\Omega)$ for $m > N/p$, and
$W^{m,p}(\Omega) \subset C^k(\bar\Omega)$ for $k + N/p < m$.

Each result is the whole-space theorem of `Numlib.Analysis.Sobolev.Embedding` applied to $Pu$ and
restricted to $\Omega$. The hypothesis on $\Omega$ is therefore the existence of an extension
operator, `HasSobolevExtensionOn` on a subspace $S \subseteq W^{1,p}(\Omega)$ and
`IsSobolevExtensionDomain` for $S = W^{1,p}(\Omega)$. An open set of class $C^1$ with bounded
boundary and the half space are extension domains. For an arbitrary open set,
$S = W_0^{1,p}(\Omega)$ has the extension by zero, so the embeddings hold on $W_0^{1,p}(\Omega)$
(Remark 20). The module also proves that $\|\nabla u\|_p + \|u\|_q$ is an equivalent norm on
$W^{1,p}(\Omega)$ for a bounded extension domain (Remark 15), and that $u(x) = (\log(1/|x|))^\alpha$
lies in $W^{1,N}(B(0, 1/2))$ but not in $L^\infty$ (Remark 16).

## Main definitions

* `SobolevMultiIndex.toLpₗOn`: the inclusion of a subspace $S \subseteq W^{k,p}(\Omega)$ into
  $L^q(\Omega)$, for a subspace whose elements lie in $L^q(\Omega)$.
* `SobolevMultiIndexZero.toLowerExponentL`: the inclusion $W_0^{k,p}(\Omega) \to W_0^{k,r}(\Omega)$
  for $r \le p$ and $|\Omega| < \infty$.
* `HasSobolevExtensionOn.toContinuousMapOnL`, `SobolevEuclidean.toContinuousMapL`: for
  $N < p < \infty$, the bounded linear map $u \mapsto \tilde u|_K$ into $C(K)$, where $\tilde u$ is
  the continuous representative and $K \supseteq \Omega$ is compact, typically $K = \bar\Omega$.
* `IsSobolevExtensionDomainAll`: $\Omega$ is an extension domain for every exponent, the hypothesis
  of Corollary 9.15.
* `logRpow`: the function $u(x) = (\log(1/|x|))^\alpha$ of Remark 16.

## Main results

* `HasSobolevExtensionOn.exists_forall_eLpNorm_fn_le`: an $L^q$ bound on $W^{1,p}(\mathbb{R}^N)$
  gives an $L^q(\Omega)$ bound on a subspace with an extension operator.
* `HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_le_of_le`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_lt`: Corollary 9.14 for
  $p < N$, $W^{1,p}(\Omega) \hookrightarrow L^q(\Omega)$ for $p \le q \le p^*$.
* `HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_eq_finrank`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_eq`: Corollary 9.14 for
  $p = N \ge 2$, $W^{1,N}(\Omega) \hookrightarrow L^q(\Omega)$ for $N \le q < \infty$.
* `HasSobolevExtensionOn.exists_forall_continuous_holderWith_ae_eq`,
  `SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_top_of_hasSobolevExtension_of_lt`: Corollary 9.14 for
  $N < p < \infty$, a continuous, bounded and Hölder continuous representative, and $W^{1,p}(\Omega)
  \hookrightarrow L^\infty(\Omega)$.
* `SobolevEuclidean.isContinuousEmbedding_toContinuousMapL`: $W^{1,p}(\Omega) \hookrightarrow C(K)$
  for $N < p < \infty$ and a compact $K \supseteq \Omega$.
* `SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension`,
  `SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension`: Corollary 9.15,
  $W^{m,p}(\Omega) \hookrightarrow L^q(\Omega)$ for $p \le q < \infty$ with $1/p - m/N \le 1/q$.
* `SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension`,
  `SobolevEuclidean.memLp_fn_top_of_order_of_hasSobolevExtension`: Corollary 9.15,
  $W^{m,p}(\Omega) \subset L^\infty(\Omega)$ for $m > N/p$, with a continuous Hölder representative.
* `SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order`,
  `SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order`,
  `SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_lt`: Corollary 9.15,
  $W^{m,p}(\Omega) \subset C^k(\bar\Omega)$ for $k + N/p < m$, with bounded derivatives and a Hölder
  continuous derivative of order $k$.
* `SobolevEuclidean.exists_continuousLinearMap_lower_of_order`:
  $W^{m+1+j,p}(\Omega) \to W^{j+1,r}(\Omega)$ is a bounded linear map for $p \le r < \infty$ with
  $1/p - m/N \le 1/r$.
* `isContDiffDomain_ball`, `isContDiffChartDomain_ball`: an open ball of $\mathbb{R}^{d+1}$ is a
  domain of class $C^\infty$.
* `SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_lt`,
  `SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_eq_finrank`,
  `SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_gt`: Remark 15,
  $\|\nabla u\|_p + \|u\|_q$ is equivalent to the norm of $W^{1,p}(\Omega)$ on a bounded extension
  domain, for the $q$ of Corollary 9.14.
* `SobolevEuclideanZero.isContinuousEmbedding_toLp`,
  `SobolevEuclideanZero.exists_forall_continuous_holderWith_ae_eq`: Remark 20, the embeddings of
  Corollary 9.14 on $W_0^{1,p}(\Omega)$ for an arbitrary open set $\Omega$.
* `ContDiffOnClosure.memSobolevMultiIndex_of_isBounded_of_le`: on a bounded open set, a function of
  class $C^n(\bar\Omega)$ lies in $W^{m,p}(\Omega)$ for $m \le n$.
* `memSobolevMultiIndex_logRpow`, `eLpNorm_logRpow_top`: Remark 16, for $N \ge 2$ and
  $0 < \alpha < 1 - 1/N$ the function $(\log(1/|x|))^\alpha$ lies in $W^{1,N}(B(0, 1/2))$ and is not
  essentially bounded.

## Proof outline

For a subspace $S$ with an extension operator $P$, an inequality
$\|v\|_{L^q(\mathbb{R}^N)} \le K \|v\|$ on $W^{1,p}(\mathbb{R}^N)$ gives $\|u\|_{L^q(\Omega)} \le
\|Pu\|_{L^q(\mathbb{R}^N)} \le K \|P\| \|u\|$, and the continuous representative of $Pu$ is one of
$u$ on $\Omega$. Corollary 9.15 follows by induction on $m$: an $L^q$ bound on $W^{m,p}(\Omega)$
makes $W^{m+1,p}(\Omega) \subseteq W^{1,q}(\Omega)$, and Corollary 9.14 applies at the exponent $q$.
The $C^k(\bar\Omega)$ clause follows by a second induction on $k$, applied to the partial
derivatives. Remark 15 combines Hölder's inequality on a set of finite measure, the interpolation
inequality between $L^q$ and $L^r$, and an absorption argument. In Remark 16 the classical gradient
of $u$ off the origin is its weak gradient on the ball, by a removable-singularity lemma, and
$|\nabla u|^N$ is integrable by a computation in polar coordinates.

## Notation

* $W^{k,p}(\Omega)$ is `SobolevEuclidean N k p Ω`, with the norm $\|u\| = (\sum_{|\alpha| \le k}
  \|\partial^\alpha u\|_{L^p(\Omega)}^p)^{1/p}$. The general space `SobolevMultiIndex F b k p Ω μ`
  uses a basis $b$ of $E$ and a measure $\mu$.
* $W_0^{k,p}(\Omega)$ is `SobolevEuclideanZero N k p Ω`, the closure of the test functions in
  $W^{k,p}(\Omega)$.
* An element $u$ of $W^{k,p}(\Omega)$ and its function `SobolevMultiIndex.fn u` are both written
  $u$.
* $\|\nabla u\|_p = (\sum_i \|\partial_i u\|_p^p)^{1/p}$ is `SobolevMultiIndex.gradNorm u`.
* $p^*$ is the Sobolev exponent, $1/p^* = 1/p - 1/N$.
* $V \hookrightarrow W$ is a continuous embedding `IsContinuousEmbedding`: an injective linear map
  $\iota$ with $\|\iota v\| \le c \|v\|$.
* $\bar\Omega$ is the closure of $\Omega$, and $|\Omega|$ its Lebesgue measure.

## Implementation notes

* The standing hypothesis of [brezis2011functional] §9.3.B, that $\Omega$ is of class $C^1$ with
  bounded boundary or is the half space, is replaced by the existence of an extension operator. The
  instances are `IsSobolevExtensionDomain.of_isContDiffChartDomain` (Theorem 9.7),
  `IsSobolevExtensionDomain.upperHalfSpace` (the half space) and
  `SobolevEuclideanZero.hasSobolevExtensionOn` (the extension by zero on $W_0^{1,p}(\Omega)$).
  Theorem 9.7 enters this module only through
  `IsSobolevExtensionDomainAll.of_isContDiffChartDomain`.
* The constants depend on the extension operator, and so they are existential.
* An exponent `p : ℝ≥0` with `[Fact (1 ≤ (p : ℝ≥0∞))]` is a finite exponent $1 \le p < \infty$. An
  exponent in `ℝ≥0∞` can also be infinite. The exponent $p^*$ is a variable `p'` with the hypothesis
  `(p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹`.
* Each $L^q$ clause is stated three times: as a bound $\|u\|_{L^q(\Omega)} \le C \|u\|$, as a
  membership $u \in L^q(\Omega)$, and as a continuous embedding along `SobolevMultiIndex.toLpₗ` (for
  $W^{k,p}(\Omega)$) or `SobolevMultiIndex.toLpₗOn` (for a subspace).
* The continuous representative is continuous on all of $\mathbb{R}^N$, which is stronger than
  continuity on $\bar\Omega$. A function lies in $C^k(\bar\Omega)$ when it is of class $C^k$ on
  $\Omega$ and each derivative of order at most $k$ agrees on $\Omega$ with a function that is
  continuous on $\bar\Omega$, as in `ContDiffOnClosure` (footnote 16). The $C^k(\bar\Omega)$ results
  of this module give extensions of the derivatives that are continuous on all of $\mathbb{R}^N$,
  which is stronger.
* The statements that cover all three cases of Corollary 9.14 at once assume $N \ge 2$ or $p > 1$.
  They exclude the case $N = 1 = p$, as Corollary 9.13 does.
* The function of Remark 16 is defined on all of $\mathbb{R}^N$ by $(-\log |x|)^\alpha$. Lean's
  conventions $\log 0 = 0$ and $0^\alpha = 0$ for $\alpha \neq 0$ give it the value $0$ at the
  origin.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

noncomputable section

/-! ### The inclusion of a subspace of $W^{k,p}(\Omega)$ into $L^q(\Omega)$ -/

section Inclusion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p q : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

variable (F b k p Ω μ) in
/-- Let $S$ be a subspace of $W^{k,p}(\Omega)$ whose elements all lie in $L^q(\Omega)$. The
**inclusion of $S$ into $L^q(\Omega)$** is the linear map $S \to L^q(\Omega)$ that sends $u$ to
the class of its function.

This is `SobolevMultiIndex.toLpₗ` for a subspace. It is the form in which the embeddings hold on
$W_0^{1,p}(\Omega)$, as in Remark 20 of [brezis2011functional]. -/
def toLpₗOn (S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ))
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E))) :
    S →ₗ[ℝ] Lp F q (μ.restrict (Ω : Set E)) where
  toFun u := (h u).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (fn_add _ _)
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (fn_smul c _)

/-- The inclusion $S \to L^q(\Omega)$ of `SobolevMultiIndex.toLpₗOn` sends $u$ to a class whose
representatives agree with $u$ almost everywhere on $\Omega$. -/
theorem toLpₗOn_coeFn {S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E)))
    (u : S) :
    toLpₗOn F b k p Ω μ S h u =ᵐ[μ.restrict (Ω : Set E)] fn (u : SobolevMultiIndex F b k p Ω μ) :=
  MemLp.coeFn_toLp (h u)

/-- The norm of the image of $u \in S$ under `SobolevMultiIndex.toLpₗOn` is $\|u\|_{L^q(\Omega)}$.
-/
theorem norm_toLpₗOn {S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E)))
    (u : S) :
    ‖toLpₗOn F b k p Ω μ S h u‖
      = (eLpNorm (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E))).toReal :=
  Lp.norm_toLp _ (h u)

/-- Let $E$ be finite-dimensional and $F$ complete. The inclusion `SobolevMultiIndex.toLpₗOn` of a
subspace $S \subseteq W^{k,p}(\Omega)$ into $L^q(\Omega)$ is injective. -/
theorem toLpₗOn_injective [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    {S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E))) :
    Function.Injective (toLpₗOn F b k p Ω μ S h) := fun u v huv ↦
  Subtype.ext <| ext_of_fn_ae_eq <| (toLpₗOn_coeFn h u).symm.trans <|
    (Lp.ext_iff.1 huv).trans (toLpₗOn_coeFn h v)

/-- Let $E$ be finite-dimensional, $F$ complete and $p, q \ge 1$. Let $S$ be a subspace of
$W^{k,p}(\Omega)$ whose elements lie in $L^q(\Omega)$. If there is $C$ with
$\|u\|_{L^q(\Omega)} \le C \|u\|$ for all $u \in S$, then the inclusion
`SobolevMultiIndex.toLpₗOn` is a continuous embedding $S \hookrightarrow L^q(\Omega)$. -/
theorem isContinuousEmbedding_toLpₗOn [Fact (1 ≤ p)] [Fact (1 ≤ q)] [FiniteDimensional ℝ E]
    [BorelSpace E] [CompleteSpace F] {S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E)))
    {C : ℝ} (hC : ∀ u : S, eLpNorm (fn (u : SobolevMultiIndex F b k p Ω μ)) q
      (μ.restrict (Ω : Set E)) ≤ ENNReal.ofReal (C * ‖u‖)) :
    IsContinuousEmbedding (toLpₗOn F b k p Ω μ S h) :=
  ⟨toLpₗOn_injective h, max C 0, fun u ↦ by
    rw [norm_toLpₗOn]
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC u)).trans ?_
    rw [ENNReal.toReal_ofReal']
    exact (max_le_max_right 0 (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))).trans
      (max_eq_left (by positivity)).le⟩

/-- Let $E$ be finite-dimensional, $F$ complete and $p, q \ge 1$. If every $u \in W^{k,p}(\Omega)$
lies in $L^q(\Omega)$ and there is $C$ with $\|u\|_{L^q(\Omega)} \le C \|u\|$ for all $u$, then
the inclusion `SobolevMultiIndex.toLpₗ` is a continuous embedding
$W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$.

This is the form of `SobolevMultiIndex.isContinuousEmbedding_toLpₗ` with the bound stated by
`MeasureTheory.eLpNorm`. -/
theorem isContinuousEmbedding_toLpₗ_of_eLpNorm_le [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    (h : ∀ u : SobolevMultiIndex F b k p Ω μ, MemLp (fn u) q (μ.restrict (Ω : Set E)))
    {C : ℝ} (hC : ∀ u : SobolevMultiIndex F b k p Ω μ,
      eLpNorm (fn u) q (μ.restrict (Ω : Set E)) ≤ ENNReal.ofReal (C * ‖u‖)) :
    IsContinuousEmbedding (toLpₗ F b k p Ω μ h) :=
  isContinuousEmbedding_toLpₗ h (C := max C 0) fun u ↦ by
    rw [toLpₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC u)).trans ?_
    rw [ENNReal.toReal_ofReal']
    exact (max_le_max_right 0 (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))).trans
      (max_eq_left (by positivity)).le

end SobolevMultiIndex

end Inclusion

/-!
### The inclusion of a subspace into $L^p(\Omega)$, and $W_0^{k,p}(\Omega) \to W_0^{k,r}(\Omega)$
-/

section ZeroInclusion

open SobolevMultiIndex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p q r : ℝ≥0∞} [Fact (1 ≤ p)]
  [Fact (1 ≤ q)] [Fact (1 ≤ r)] {Ω : Opens E} {μ : Measure E}

/-- For a subspace $S \subseteq W^{k,p}(\Omega)$, the inclusion `SobolevMultiIndex.toLpₗOn` of $S$
into $L^p(\Omega)$ is the restriction of `SobolevMultiIndex.fnL` to $S$. -/
theorem SobolevMultiIndex.toLpₗOn_self (S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)) :
    toLpₗOn F b k p Ω μ S (fun u ↦ memLp (u : SobolevMultiIndex F b k p Ω μ))
      = ((fnL F b k p Ω μ).comp S.subtypeL).toLinearMap :=
  LinearMap.ext fun u ↦ Lp.ext ((toLpₗOn_coeFn _ u).trans (Eventually.of_forall fun _ ↦ rfl))

/-- The inclusion `SobolevMultiIndex.toLpₗOn` of $W_0^{k,p}(\Omega)$ into $L^p(\Omega)$ is
`SobolevMultiIndexZero.fnL`. -/
theorem SobolevMultiIndexZero.toLpₗOn_eq_fnL :
    toLpₗOn F b k p Ω μ (SobolevMultiIndexZero F b k p Ω μ)
        (fun u ↦ memLp (u : SobolevMultiIndex F b k p Ω μ))
      = (SobolevMultiIndexZero.fnL F b k p Ω μ).toLinearMap :=
  SobolevMultiIndex.toLpₗOn_self _

/-- Let $p, q, r \ge 1$, and let $S \subseteq W^{k,p}(\Omega)$ and $S' \subseteq W^{k,r}(\Omega)$ be
subspaces whose elements lie in $L^q(\Omega)$. Let $T : S \to S'$ be a bounded linear map that
is a continuous embedding and satisfies $Tu = u$ almost everywhere on $\Omega$. If the inclusion
$S' \to L^q(\Omega)$ is a compact embedding, then the inclusion $S \to L^q(\Omega)$ is a compact
embedding.

The inclusion of $S$ is the inclusion of $S'$ composed with $T$. The operators are variables, so
that the statement applies directly to maps such as $W_0^{1,N}(\Omega) \to W_0^{1,r}(\Omega)$. -/
theorem SobolevMultiIndex.isCompactEmbedding_toLpₗOn_of_comp
    {S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    {S' : Submodule ℝ (SobolevMultiIndex F b k r Ω μ)} (T : S →L[ℝ] S')
    (hT : IsContinuousEmbedding T.toLinearMap)
    (hfn : ∀ u : S, fn ((T u : S') : SobolevMultiIndex F b k r Ω μ)
      =ᵐ[μ.restrict (Ω : Set E)] fn (u : SobolevMultiIndex F b k p Ω μ))
    {h' : ∀ v : S', MemLp (fn (v : SobolevMultiIndex F b k r Ω μ)) q (μ.restrict (Ω : Set E))}
    (hc : IsCompactEmbedding (toLpₗOn F b k r Ω μ S' h'))
    (h : ∀ u : S, MemLp (fn (u : SobolevMultiIndex F b k p Ω μ)) q (μ.restrict (Ω : Set E))) :
    IsCompactEmbedding (toLpₗOn F b k p Ω μ S h) := by
  have := hT.comp_isCompactEmbedding hc
  convert this using 1
  refine LinearMap.ext fun u ↦ Lp.ext ((toLpₗOn_coeFn h u).trans ?_)
  exact ((toLpₗOn_coeFn h' (T u)).trans (hfn u)).symm

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

/-- Let $E$ be finite-dimensional, $F$ complete and $p \ge 1$. For every subspace
$S \subseteq W^{k,p}(\Omega)$, the inclusion `SobolevMultiIndex.toLpₗOn` of $S$ into
$L^p(\Omega)$ is a continuous embedding: it is injective and of norm at most $1$. -/
theorem SobolevMultiIndex.isContinuousEmbedding_toLpₗOn_self
    (S : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)) :
    IsContinuousEmbedding (toLpₗOn F b k p Ω μ S
      fun u ↦ memLp (u : SobolevMultiIndex F b k p Ω μ)) := by
  rw [toLpₗOn_self]
  exact ⟨fun _ _ huv ↦ Subtype.ext (fnL_injective huv), _,
    ((fnL F b k p Ω μ).comp S.subtypeL).le_opNorm⟩

/-- Let $E$ be finite-dimensional, $F$ complete, $|\Omega| < \infty$ and $1 \le r \le p$. The
inclusion `SobolevMultiIndex.toLowerExponentL` of $W^{k,p}(\Omega)$ into $W^{k,r}(\Omega)$ maps
$W_0^{k,p}(\Omega)$ into $W_0^{k,r}(\Omega)$.

The inclusion maps test functions to test functions and is continuous, so it maps the closure of
the test functions into the closure. -/
theorem SobolevMultiIndexZero.toLowerExponentL_mem (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p)
    {u : SobolevMultiIndex F b k p Ω μ} (hu : u ∈ SobolevMultiIndexZero F b k p Ω μ) :
    toLowerExponentL F b k p r μ hΩ hrp u ∈ SobolevMultiIndexZero F b k r Ω μ := by
  have h : SobolevMultiIndexZero F b k p Ω μ ≤ (SobolevMultiIndexZero F b k r Ω μ).comap
      (toLowerExponentL F b k p r μ hΩ hrp : SobolevMultiIndex F b k p Ω μ →ₗ[ℝ] _) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · intro v hv
      obtain ⟨φ, hφ⟩ := mem_testFunctions.1 hv
      exact SobolevMultiIndexZero.testFunctions_le
        (mem_testFunctions.2 ⟨φ, (fn_toLowerExponentL hΩ hrp v).trans hφ⟩)
    · exact SobolevMultiIndexZero.isClosed.preimage (toLowerExponentL F b k p r μ hΩ hrp).continuous
  exact h hu

variable (F b k p r μ) in
/-- Let $E$ be finite-dimensional, $F$ complete, $|\Omega| < \infty$ and $1 \le r \le p$. The
**inclusion $W_0^{k,p}(\Omega) \to W_0^{k,r}(\Omega)$** is the bounded linear map that
`SobolevMultiIndex.toLowerExponentL` induces on the closures of the test functions. -/
def SobolevMultiIndexZero.toLowerExponentL (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) :
    SobolevMultiIndexZero F b k p Ω μ →L[ℝ] SobolevMultiIndexZero F b k r Ω μ :=
  ((SobolevMultiIndex.toLowerExponentL F b k p r μ hΩ hrp).comp
    (SobolevMultiIndexZero F b k p Ω μ).subtypeL).codRestrict _
      fun u ↦ SobolevMultiIndexZero.toLowerExponentL_mem hΩ hrp u.2

/-- As an element of $W^{k,r}(\Omega)$, the image of $u$ under
`SobolevMultiIndexZero.toLowerExponentL` is the image of $u$ under
`SobolevMultiIndex.toLowerExponentL`. -/
@[simp]
theorem SobolevMultiIndexZero.coe_toLowerExponentL (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p)
    (u : SobolevMultiIndexZero F b k p Ω μ) :
    (SobolevMultiIndexZero.toLowerExponentL F b k p r μ hΩ hrp u : SobolevMultiIndex F b k r Ω μ)
      = SobolevMultiIndex.toLowerExponentL F b k p r μ hΩ hrp u :=
  rfl

/-- The image of $u$ under `SobolevMultiIndexZero.toLowerExponentL` agrees with $u$ almost
everywhere on $\Omega$. -/
theorem SobolevMultiIndexZero.fn_toLowerExponentL (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p)
    (u : SobolevMultiIndexZero F b k p Ω μ) :
    fn ((SobolevMultiIndexZero.toLowerExponentL F b k p r μ hΩ hrp u : _) :
        SobolevMultiIndex F b k r Ω μ)
      =ᵐ[μ.restrict (Ω : Set E)] fn (u : SobolevMultiIndex F b k p Ω μ) := by
  rw [SobolevMultiIndexZero.coe_toLowerExponentL]
  exact SobolevMultiIndex.fn_toLowerExponentL hΩ hrp _

/-- Let $E$ be finite-dimensional, $F$ complete, $|\Omega| < \infty$ and $1 \le r \le p$. The
inclusion $W_0^{k,p}(\Omega) \hookrightarrow W_0^{k,r}(\Omega)$ of
`SobolevMultiIndexZero.toLowerExponentL` is a continuous embedding. -/
theorem SobolevMultiIndexZero.isContinuousEmbedding_toLowerExponentL (hΩ : μ Ω ≠ ⊤) (hrp : r ≤ p) :
    IsContinuousEmbedding (SobolevMultiIndexZero.toLowerExponentL F b k p r μ hΩ hrp).toLinearMap :=
  ⟨fun _ _ huv ↦ Subtype.ext (toLowerExponentL_injective hΩ hrp (congrArg Subtype.val huv)), _,
    (SobolevMultiIndexZero.toLowerExponentL F b k p r μ hΩ hrp).le_opNorm⟩

end ZeroInclusion

/-! ### Corollary 9.14: the embeddings on an extension domain -/

section Transfer

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- Let $1 \le p \le \infty$, and let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension
operator. Then there are a bounded linear map $P : S \to W^{1,p}(\mathbb{R}^N)$ and $C \ge 0$
such that, for every $u \in S$, $Pu = u$ almost everywhere on $\Omega$ and $\|Pu\| \le C \|u\|$. -/
theorem HasSobolevExtensionOn.exists_forall_norm_le (hS : HasSobolevExtensionOn S) :
    ∃ (P : S →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ), 0 ≤ C ∧ ∀ u : S,
      fn (P u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fn (u : SobolevEuclidean N 1 p Ω) ∧ ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨P, hP⟩ := hS
  exact ⟨P, ‖P‖, norm_nonneg _, fun u ↦ ⟨hP u, P.le_opNorm u⟩⟩

/-- The **transfer principle** of §9.3.B of [brezis2011functional]. Let $1 \le p \le \infty$, and
let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator. Suppose that
$\|v\|_{L^q(\mathbb{R}^N)} \le K \|v\|$ for every $v \in W^{1,p}(\mathbb{R}^N)$. Then there is
$C \ge 0$ with $$\|u\|_{L^q(\Omega)} \le C \|u\| \qquad \text{for all } u \in S.$$

For an extension operator $P$ with $\|Pu\| \le C_P \|u\|$, the function $u$ agrees with $Pu$ on
$\Omega$, so $C = \max\{K, 0\} \, C_P$ works. -/
theorem HasSobolevExtensionOn.exists_forall_eLpNorm_fn_le (hS : HasSobolevExtensionOn S)
    {q : ℝ≥0∞} {K : ℝ} (hK : ∀ v : SobolevEuclidean N 1 p ⊤,
      eLpNorm (fn v) q volume ≤ ENNReal.ofReal (K * ‖v‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖) := by
  obtain ⟨P, C, hC0, hP⟩ := hS.exists_forall_norm_le
  refine ⟨max K 0 * C, by positivity, fun u ↦ ?_⟩
  rw [← eLpNorm_congr_ae (hP u).1]
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ((hK (P u)).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  calc K * ‖P u‖ ≤ max K 0 * ‖P u‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max K 0 * (C * ‖u‖) := mul_le_mul_of_nonneg_left (hP u).2 (le_max_right _ _)
    _ = max K 0 * C * ‖u‖ := by ring

end Transfer

section Domain

open SobolevMultiIndex
open scoped BoundedContinuousFunction

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-! ### Corollary 9.14, the case $p < N$ -/

/-- Let $1 \le p < N$, let $1/p^* = 1/p - 1/N$, and let $p \le q \le p^*$. Let $S$ be a subspace of
$W^{1,p}(\Omega)$ with an extension operator. Then there is $C \ge 0$ with
$\|u\|_{L^q(\Omega)} \le C \|u\|$ for all $u \in S$. This is Corollary 9.14 of
[brezis2011functional] for $p < N$, on a subspace. -/
theorem HasSobolevExtensionOn.exists_forall_eLpNorm_fn_le_of_le_of_le
    (hS : HasSobolevExtensionOn S) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖) :=
  hS.exists_forall_eLpNorm_fn_le fun v ↦
    SobolevEuclidean.eLpNorm_fn_le_norm_of_le_of_le hpN hp' hpq hqp' v

/-- Let $1 \le p < N$, let $1/p^* = 1/p - 1/N$, and let $p \le q \le p^*$. If $S$ is a subspace of
$W^{1,p}(\Omega)$ with an extension operator, then every $u \in S$ lies in $L^q(\Omega)$. -/
theorem HasSobolevExtensionOn.memLp_fn_of_le_of_le (hS : HasSobolevExtensionOn S) {p' : ℝ≥0}
    (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') (u : S) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_le_of_le hpN hp' hpq hqp'
  exact memLp_iff.2 ((hC u).trans_lt ENNReal.ofReal_lt_top)

/-- Let $1 \le p < N$, let $1/p^* = 1/p - 1/N$, and let $p \le q \le p^*$. If $S$ is a subspace of
$W^{1,p}(\Omega)$ with an extension operator, then $S \hookrightarrow L^q(\Omega)$. This is
Corollary 9.14 of [brezis2011functional] for $p < N$, in the form of Remark 20.

The embedding is the inclusion `SobolevMultiIndex.toLpₗOn`. -/
theorem HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_le_of_le [Fact (1 ≤ (q : ℝ≥0∞))]
    (hS : HasSobolevExtensionOn S) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      (hS.memLp_fn_of_le_of_le hpN hp' hpq hqp')) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_le_of_le hpN hp' hpq hqp'
  exact isContinuousEmbedding_toLpₗOn _ hC

/-- Let $\Omega$ be an extension domain for $W^{1,p}$, let $1 \le p < N$, let $1/p^* = 1/p - 1/N$,
and let $p \le q \le p^*$. Then every $u \in W^{1,p}(\Omega)$ lies in $L^q(\Omega)$. -/
theorem SobolevEuclidean.memLp_fn_of_isSobolevExtensionDomain_of_le_of_le
    (hΩ : IsSobolevExtensionDomain N p Ω) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p')
    (u : SobolevEuclidean N 1 p Ω) :
    MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hΩ.memLp_fn_of_le_of_le hpN hp' hpq hqp' ⟨u, Submodule.mem_top⟩

/-- Let $\Omega$ be an extension domain for $W^{1,p}$, for example an open set of class $C^1$ with
bounded boundary, or the half space. Let $1 \le p < N$, let $1/p^* = 1/p - 1/N$, and let
$p \le q \le p^*$. Then $$W^{1,p}(\Omega) \hookrightarrow L^q(\Omega).$$ This is Corollary 9.14
of [brezis2011functional], first case, with the range of $q$ of Corollary 9.10.

The embedding is the inclusion `SobolevMultiIndex.toLpₗ`. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_lt
    [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N p Ω) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclidean.memLp_fn_of_isSobolevExtensionDomain_of_le_of_le hΩ hpN hp' hpq hqp')) := by
  obtain ⟨C, -, hC⟩ := hΩ.exists_forall_eLpNorm_fn_le_of_le_of_le hpN hp' hpq hqp'
  exact isContinuousEmbedding_toLpₗ_of_eLpNorm_le _ fun u ↦ by
    simpa using hC ⟨u, Submodule.mem_top⟩

/-! ### Corollary 9.14, the case $p = N$ -/

/-- Let $N \ge 2$ and $N \le q < \infty$, and let $S$ be a subspace of $W^{1,N}(\Omega)$ with an
extension operator. Then there is $C \ge 0$ with $\|u\|_{L^q(\Omega)} \le C \|u\|$ for all
$u \in S$. This is Corollary 9.14 of [brezis2011functional] for $p = N$, on a subspace. -/
theorem HasSobolevExtensionOn.exists_forall_eLpNorm_fn_le_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    {S : Submodule ℝ (SobolevEuclidean N 1 N Ω)} (hS : HasSobolevExtensionOn S) (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, eLpNorm (fn (u : SobolevEuclidean N 1 N Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖) := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  refine hS.exists_forall_eLpNorm_fn_le (K := K.toReal) fun v ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
  exact hKu v

/-- Let $N \ge 2$ and $N \le q < \infty$. If $S$ is a subspace of $W^{1,N}(\Omega)$ with an
extension operator, then every $u \in S$ lies in $L^q(\Omega)$. -/
theorem HasSobolevExtensionOn.memLp_fn_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    {S : Submodule ℝ (SobolevEuclidean N 1 N Ω)} (hS : HasSobolevExtensionOn S) (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) (u : S) :
    MemLp (fn (u : SobolevEuclidean N 1 N Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  exact memLp_iff.2 ((hC u).trans_lt ENNReal.ofReal_lt_top)

/-- Let $N \ge 2$ and $N \le q < \infty$. If $S$ is a subspace of $W^{1,N}(\Omega)$ with an
extension operator, then $S \hookrightarrow L^q(\Omega)$. This is Corollary 9.14 of
[brezis2011functional] for $p = N$, in the form of Remark 20.

The embedding is the inclusion `SobolevMultiIndex.toLpₗOn`. -/
theorem HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_eq_finrank [Fact (1 ≤ (N : ℝ≥0∞))]
    [Fact (1 ≤ (q : ℝ≥0∞))] {S : Submodule ℝ (SobolevEuclidean N 1 N Ω)}
    (hS : HasSobolevExtensionOn S) (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 N Ω volume S
      (hS.memLp_fn_of_eq_finrank hN hq)) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  exact isContinuousEmbedding_toLpₗOn _ hC

/-- Let $\Omega$ be an extension domain for $W^{1,N}$, with $N \ge 2$, and let $N \le q < \infty$.
Then every $u \in W^{1,N}(\Omega)$ lies in $L^q(\Omega)$. -/
theorem SobolevEuclidean.memLp_fn_of_isSobolevExtensionDomain_of_eq_finrank
    [Fact (1 ≤ (N : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N N Ω) (hN : 2 ≤ N)
    (hq : (N : ℝ≥0) ≤ q) (u : SobolevEuclidean N 1 N Ω) :
    MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hΩ.memLp_fn_of_eq_finrank hN hq ⟨u, Submodule.mem_top⟩

/-- Let $\Omega$ be an extension domain for $W^{1,N}$, with $N \ge 2$, and let $N \le q < \infty$.
Then $$W^{1,N}(\Omega) \hookrightarrow L^q(\Omega).$$ This is Corollary 9.14 of
[brezis2011functional], second case.

The embedding is the inclusion `SobolevMultiIndex.toLpₗ`. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_hasSobolevExtension_of_eq
    [Fact (1 ≤ (N : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N N Ω)
    (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 N Ω volume
      (SobolevEuclidean.memLp_fn_of_isSobolevExtensionDomain_of_eq_finrank hΩ hN hq)) := by
  obtain ⟨C, -, hC⟩ := hΩ.exists_forall_eLpNorm_fn_le_of_eq_finrank hN hq
  exact isContinuousEmbedding_toLpₗ_of_eLpNorm_le _ fun u ↦ by
    simpa using hC ⟨u, Submodule.mem_top⟩

/-! ### Corollary 9.14, the case $p > N$: the continuous representative up to the boundary -/

/-- Let $N < p < \infty$, and let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator.
Then there is $C \ge 0$ such that every $u \in S$ has a representative
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ with these properties: $\tilde u$ is continuous on
$\mathbb{R}^N$, $u = \tilde u$ almost everywhere on $\Omega$, and for all
$x, y \in \mathbb{R}^N$ $$|\tilde u(x) - \tilde u(y)| \le C \|u\| \, |x - y|^{1 - N/p}, \qquad
|\tilde u(x)| \le C \|u\|.$$ This is Corollary 9.14 of [brezis2011functional] for $p > N$, in
the form of Remark 20.

The representative is the continuous representative of $Pu$ given by Morrey's theorem, for an
extension operator $P$. Its bounds follow from $\|Pu\| \le \|P\| \|u\|$. -/
theorem HasSobolevExtensionOn.exists_forall_continuous_holderWith_ae_eq
    (hS : HasSobolevExtensionOn S) (hp : N < p) :
    ∃ C : ℝ≥0, ∀ u : S, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
      fn (u : SobolevEuclidean N 1 p Ω) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      HolderWith (C * ‖u‖₊) (1 - (N : ℝ≥0) / p) ũ ∧ ∀ x, ‖ũ x‖ ≤ C * ‖u‖ := by
  obtain ⟨P, C₀, hC₀, hP⟩ := hS.exists_forall_norm_le
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ≥0∞,
    K₁ = morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * N := ⟨_, rfl⟩
  have hK₁t : K₁ ≠ ⊤ := by
    rw [hK₁]
    exact ENNReal.mul_ne_top (morreyConst_ne_top _ _) (by simp)
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ,
    K₂ = (morreySupConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * (N + 1)).toReal :=
    ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := hK₂ ▸ ENNReal.toReal_nonneg
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  have hα : ((1 - (N : ℝ≥0) / p : ℝ≥0) : ℝ) = 1 - N / (p : ℝ) := by
    rw [NNReal.coe_sub ((div_le_one (by exact_mod_cast hp0)).2 hp.le)]
    simp
  have hα0 : (0 : ℝ) ≤ 1 - N / (p : ℝ) := by
    rw [← hα]
    exact NNReal.coe_nonneg _
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, C = max (K₁.toNNReal * C₀.toNNReal) (K₂ * C₀).toNNReal := ⟨_, rfl⟩
  refine ⟨C, fun u ↦ ?_⟩
  obtain ⟨ũ, hũ⟩ : ∃ ũ : EuclideanSpace ℝ (Fin N) →ᵇ ℝ, ũ = SobolevEuclidean.contRep hp (P u) :=
    ⟨_, rfl⟩
  refine ⟨ũ, ũ.continuous, ?_, ?_, ?_⟩
  · rw [hũ]
    exact (hP u).1.symm.trans (ae_restrict_of_ae (SobolevEuclidean.fn_ae_eq_contRep hp (P u)))
  · intro x y
    have h1 : ‖ũ x - ũ y‖ₑ
        ≤ K₁ * ENNReal.ofReal (C₀ * ‖u‖) * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ))) := by
      rw [hũ, hK₁]
      refine (SobolevEuclidean.enorm_contRep_sub_le hp (P u) x y).trans ?_
      calc morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
            * ∑ i, ENNReal.ofReal ‖weakDeriv (P u) (MultiIndexLE.single i)‖
          ≤ morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
            * (N * ENNReal.ofReal ‖P u‖) :=
            mul_le_mul' le_rfl (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le (P u))
        _ ≤ morreyConst volume p * ENNReal.ofReal (‖x - y‖ ^ (1 - N / (p : ℝ)))
            * (N * ENNReal.ofReal (C₀ * ‖u‖)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hP u).2))
        _ = _ := by ring
    have h2 : K₁ * ENNReal.ofReal (C₀ * ‖u‖)
        = ((K₁.toNNReal * C₀.toNNReal * ‖u‖₊ : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hK₁t, mul_assoc, ← ENNReal.coe_mul,
        ← norm_toNNReal, ← Real.toNNReal_mul hC₀]
      rfl
    have h3 : ((K₁.toNNReal * C₀.toNNReal * ‖u‖₊ : ℝ≥0) : ℝ≥0∞) ≤ ((C * ‖u‖₊ : ℝ≥0) : ℝ≥0∞) := by
      rw [hC]
      exact ENNReal.coe_le_coe.2 (mul_le_mul' (le_max_left _ _) le_rfl)
    rw [edist_eq_enorm_sub, edist_eq_enorm_sub, ← ofReal_norm (x - y), hα,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα0]
    exact h1.trans (mul_le_mul' (h2.le.trans h3) le_rfl)
  · intro x
    have h1 : ‖ũ x‖ ≤ K₂ * ‖P u‖ := by
      rw [hũ, hK₂]
      exact SobolevEuclidean.norm_contRep_apply_le hp (P u) x
    have h2 : (K₂ * C₀).toNNReal ≤ C := hC ▸ le_max_right _ _
    calc ‖ũ x‖ ≤ K₂ * ‖P u‖ := h1
      _ ≤ K₂ * (C₀ * ‖u‖) := mul_le_mul_of_nonneg_left (hP u).2 hK₂0
      _ = (K₂ * C₀).toNNReal * ‖u‖ := by
          rw [Real.coe_toNNReal _ (by positivity)]
          ring
      _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (norm_nonneg _)

/-- Let $N < p < \infty$, and let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator.
Then there is $C \ge 0$ with $\|u\|_{L^\infty(\Omega)} \le C \|u\|$ for all $u \in S$. -/
theorem HasSobolevExtensionOn.exists_forall_eLpNorm_fn_top_le (hS : HasSobolevExtensionOn S)
    (hp : N < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) ⊤
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖) := by
  obtain ⟨C, hC⟩ := hS.exists_forall_continuous_holderWith_ae_eq hp
  refine ⟨C, C.coe_nonneg, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, -, hb⟩ := hC u
  rw [eLpNorm_congr_ae hae]
  refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal (C * ‖u‖))
    hc.aestronglyMeasurable.restrict (Eventually.of_forall fun x ↦ ?_)).trans (by simp)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hb x)

/-- Let $N < p < \infty$. If $S$ is a subspace of $W^{1,p}(\Omega)$ with an extension operator, then
every $u \in S$ lies in $L^\infty(\Omega)$. -/
theorem HasSobolevExtensionOn.memLp_fn_top_of_lt (hS : HasSobolevExtensionOn S) (hp : N < p)
    (u : S) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) ⊤
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_top_le hp
  exact memLp_iff.2 ((hC u).trans_lt ENNReal.ofReal_lt_top)

/-- Let $N < p < \infty$. If $S$ is a subspace of $W^{1,p}(\Omega)$ with an extension operator, then
$S \hookrightarrow L^\infty(\Omega)$. This is Corollary 9.14 of [brezis2011functional], third
case, in the form of Remark 20.

The embedding is the inclusion `SobolevMultiIndex.toLpₗOn`. -/
theorem HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_top_of_lt (hS : HasSobolevExtensionOn S)
    (hp : N < p) :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      (hS.memLp_fn_top_of_lt hp)) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_top_le hp
  exact isContinuousEmbedding_toLpₗOn _ hC

/-- Let $\Omega$ be an extension domain for $W^{1,p}$, and let $N < p < \infty$. Then there is
$C \ge 0$ such that every $u \in W^{1,p}(\Omega)$ has a representative
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ with these properties: $\tilde u$ is continuous on
$\mathbb{R}^N$, $u = \tilde u$ almost everywhere on $\Omega$, and for all
$x, y \in \mathbb{R}^N$ $$|\tilde u(x) - \tilde u(y)| \le C \|u\| \, |x - y|^{1 - N/p}, \qquad
|\tilde u(x)| \le C \|u\|.$$ This is Corollary 9.14 of [brezis2011functional] for $p > N$, with
$W^{1,p}(\Omega) \subset C(\bar\Omega)$ of footnote 15.

The representative is continuous on all of $\mathbb{R}^N$, and so in particular on $\bar\Omega$.
The sup bound gives $W^{1,p}(\Omega) \subset L^\infty(\Omega)$. -/
theorem SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p) :
    ∃ C : ℝ≥0, ∀ u : SobolevEuclidean N 1 p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      HolderWith (C * ‖u‖₊) (1 - (N : ℝ≥0) / p) ũ ∧ ∀ x, ‖ũ x‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := hΩ.exists_forall_continuous_holderWith_ae_eq hp
  exact ⟨C, fun u ↦ hC ⟨u, Submodule.mem_top⟩⟩

/-- Let $\Omega$ be an extension domain for $W^{1,p}$, and let $N < p < \infty$. Then every
$u \in W^{1,p}(\Omega)$ lies in $L^\infty(\Omega)$. -/
theorem SobolevEuclidean.memLp_fn_top_of_isSobolevExtensionDomain_of_lt
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p) (u : SobolevEuclidean N 1 p Ω) :
    MemLp (fn u) ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hΩ.memLp_fn_top_of_lt hp ⟨u, Submodule.mem_top⟩

/-- Let $\Omega$ be an extension domain for $W^{1,p}$, and let $N < p < \infty$. Then
$$W^{1,p}(\Omega) \hookrightarrow L^\infty(\Omega).$$ This is Corollary 9.14 of
[brezis2011functional], third case.

The embedding is the inclusion `SobolevMultiIndex.toLpₗ`. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_top_of_hasSobolevExtension_of_lt
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclidean.memLp_fn_top_of_isSobolevExtensionDomain_of_lt hΩ hp)) := by
  obtain ⟨C, -, hC⟩ := hΩ.exists_forall_eLpNorm_fn_top_le hp
  exact isContinuousEmbedding_toLpₗ_of_eLpNorm_le _ fun u ↦ by
    simpa using hC ⟨u, Submodule.mem_top⟩

end Domain

/-! ### The continuous representative on a compact set: $W^{1,p}(\Omega) \subset C(\bar\Omega)$ -/

section ToContinuousMap

open scoped BoundedContinuousFunction

/-- Let $E$ be a topological space and $K \subseteq E$ compact. The **restriction to $K$** is the
bounded linear map $f \mapsto f|_K$ from the bounded continuous functions on $E$ to $C(K)$, of
norm at most $1$. -/
def BoundedContinuousFunction.restrictCLM {E : Type*} [TopologicalSpace E] (K : Set E)
    [CompactSpace K] : (E →ᵇ ℝ) →L[ℝ] C(K, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (f : C(E, ℝ)).restrict K
      map_add' := fun f g ↦ by ext x; simp
      map_smul' := fun c f ↦ by ext x; simp }
    1 fun f ↦ by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ f.norm_coe_le_norm x

/-- The restriction `BoundedContinuousFunction.restrictCLM K f` takes the value $f(x)$ at $x \in K$.
-/
@[simp]
theorem BoundedContinuousFunction.restrictCLM_apply {E : Type*} [TopologicalSpace E] (K : Set E)
    [CompactSpace K] (f : E →ᵇ ℝ) (x : K) : restrictCLM K f x = f x :=
  rfl

/-- The restriction to a compact set $K$ does not increase the sup norm: $\|f|_K\| \le \|f\|$. -/
theorem BoundedContinuousFunction.norm_restrictCLM_apply_le {E : Type*} [TopologicalSpace E]
    (K : Set E) [CompactSpace K] (f : E →ᵇ ℝ) : ‖restrictCLM K f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ f.norm_coe_le_norm x

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- Let $N < p < \infty$, let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator, and
let $K \subseteq \mathbb{R}^N$ be compact. The **continuous representative on $K$** is the
bounded linear map $S \to C(K)$ that sends $u$ to $\widetilde{Pu}|_K$, where $P$ is a chosen
extension operator and $\widetilde{Pu}$ is the continuous representative of $Pu$.

The values on $K \cap \bar\Omega$ do not depend on the choice of $P$, by
`HasSobolevExtensionOn.toContinuousMapOnL_apply_of_ae_eq`. For $K \supseteq \Omega$, typically
$K = \bar\Omega$, this is the map $W^{1,p}(\Omega) \subset C(\bar\Omega)$ of footnote 15 to
Corollary 9.14 of [brezis2011functional], and the map that the third case of Theorem 9.16 makes
compact. -/
noncomputable def HasSobolevExtensionOn.toContinuousMapOnL (hS : HasSobolevExtensionOn S)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K] : S →L[ℝ] C(K, ℝ) :=
  (BoundedContinuousFunction.restrictCLM K).comp
    ((SobolevEuclidean.toBoundedContinuousMapL N p hp).comp hS.choose)

/-- The value of `HasSobolevExtensionOn.toContinuousMapOnL` at $u$ and $x \in K$ is
$\widetilde{Pu}(x)$, the value of `SobolevEuclidean.contRep` at $Pu$, for the chosen extension
operator $P$. -/
theorem HasSobolevExtensionOn.toContinuousMapOnL_apply (hS : HasSobolevExtensionOn S)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K] (u : S) (x : K) :
    hS.toContinuousMapOnL hp K u x = SobolevEuclidean.contRep hp (hS.choose u) x :=
  rfl

/-- Let $N < p < \infty$, and let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator.
For every $u \in S$, $u = \widetilde{Pu}$ almost everywhere on $\Omega$, where $\widetilde{Pu}$
is the continuous representative of $Pu$ for the chosen extension operator $P$. This is the
function that `HasSobolevExtensionOn.toContinuousMapOnL` restricts to $K$. -/
theorem HasSobolevExtensionOn.fn_ae_eq_toContinuousMapOnL (hS : HasSobolevExtensionOn S)
    (hp : N < p) (u : S) :
    fn (u : SobolevEuclidean N 1 p Ω) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      SobolevEuclidean.contRep hp (hS.choose u) :=
  (hS.choose_spec u).symm.trans
    (ae_restrict_of_ae (SobolevEuclidean.fn_ae_eq_contRep hp (hS.choose u)))

/-- Let $N < p < \infty$, let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator, and
let $K$ be compact. Let $u \in S$, and let $g$ be a continuous function on $\mathbb{R}^N$ with
$u = g$ almost everywhere on $\Omega$. Then the image of $u$ under
`HasSobolevExtensionOn.toContinuousMapOnL` agrees with $g$ on $K \cap \bar\Omega$.

So on $K \cap \bar\Omega$ the map does not depend on the extension operator. Two continuous
functions that agree almost everywhere on the open set $\Omega$ agree on $\Omega$, and hence on
$\bar\Omega$. -/
theorem HasSobolevExtensionOn.toContinuousMapOnL_apply_of_ae_eq (hS : HasSobolevExtensionOn S)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K] (u : S)
    {g : EuclideanSpace ℝ (Fin N) → ℝ} (hg : Continuous g)
    (hu : fn (u : SobolevEuclidean N 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g)
    (x : K) (hx : (x : EuclideanSpace ℝ (Fin N)) ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    hS.toContinuousMapOnL hp K u x = g x := by
  rw [hS.toContinuousMapOnL_apply]
  have heq : EqOn (SobolevEuclidean.contRep hp (hS.choose u)) g
      (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
    Measure.eqOn_open_of_ae_eq ((hS.fn_ae_eq_toContinuousMapOnL hp u).symm.trans hu) Ω.isOpen
      (SobolevEuclidean.contRep hp (hS.choose u)).continuous.continuousOn hg.continuousOn
  exact heq.of_subset_closure (SobolevEuclidean.contRep hp (hS.choose u)).continuous.continuousOn
    hg.continuousOn subset_closure subset_rfl hx

/-- Let $N < p < \infty$, let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator, and
let $K$ be compact. Then there is $C \ge 0$ with $\|\tilde u|_K\|_\infty \le C \|u\|$ for all
$u \in S$, where $\tilde u|_K$ is the image of $u$ under
`HasSobolevExtensionOn.toContinuousMapOnL`. -/
theorem HasSobolevExtensionOn.exists_forall_norm_toContinuousMapOnL_le
    (hS : HasSobolevExtensionOn S) (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N)))
    [CompactSpace K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, ‖hS.toContinuousMapOnL hp K u‖ ≤ C * ‖u‖ := by
  refine ⟨‖hS.toContinuousMapOnL hp K‖, norm_nonneg _, fun u ↦ ?_⟩
  exact (hS.toContinuousMapOnL hp K).le_opNorm u

/-- Let $N < p < \infty$, let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator, and
let $K \supseteq \Omega$ be compact. Then `HasSobolevExtensionOn.toContinuousMapOnL` is
injective on $S$: if the continuous representative of $u$ vanishes on $K$, then $u = 0$ almost
everywhere on $\Omega$. -/
theorem HasSobolevExtensionOn.toContinuousMapOnL_injective (hS : HasSobolevExtensionOn S)
    (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    Function.Injective (hS.toContinuousMapOnL hp K) := by
  intro u v huv
  refine Subtype.ext (ext_of_fn_ae_eq ?_)
  refine (hS.fn_ae_eq_toContinuousMapOnL hp u).trans
    (Filter.EventuallyEq.trans ?_ (hS.fn_ae_eq_toContinuousMapOnL hp v).symm)
  refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx ↦ ?_
  have := congrArg (fun f : C(K, ℝ) ↦ f ⟨x, hK hx⟩) huv
  simpa [HasSobolevExtensionOn.toContinuousMapOnL_apply] using this

/-- Let $N < p < \infty$, let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator, and
let $K$ be compact. Then there is $C \ge 0$ such that, for all $u \in S$ and $x, y \in K$,
$$|\tilde u(x) - \tilde u(y)| \le C \|u\| \, |x - y|^{1 - N/p},$$ where $\tilde u$ is the image
of $u$ under `HasSobolevExtensionOn.toContinuousMapOnL`.

The images of the unit ball of $S$ are therefore equicontinuous. This is the equicontinuity that
the Arzelà–Ascoli theorem needs in the third case of Theorem 9.16 of [brezis2011functional]. -/
theorem HasSobolevExtensionOn.exists_forall_norm_toContinuousMapOnL_sub_le
    (hS : HasSobolevExtensionOn S) (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N)))
    [CompactSpace K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : S) (x y : K), ‖hS.toContinuousMapOnL hp K u x
      - hS.toContinuousMapOnL hp K u y‖ ≤ C * ‖u‖ * ‖(x : EuclideanSpace ℝ (Fin N)) - y‖
        ^ (1 - N / (p : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = ‖hS.choose‖ := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := hC₀ ▸ norm_nonneg _
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ≥0∞,
    K₁ = morreyConst (volume : Measure (EuclideanSpace ℝ (Fin N))) p * N := ⟨_, rfl⟩
  have hK₁t : K₁ ≠ ⊤ := by
    rw [hK₁]
    exact ENNReal.mul_ne_top (morreyConst_ne_top _ _) (by simp)
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg N) hp
  refine ⟨K₁.toReal * C₀, by positivity, fun u x y ↦ ?_⟩
  simp only [HasSobolevExtensionOn.toContinuousMapOnL_apply]
  have h1 : ‖SobolevEuclidean.contRep hp (hS.choose u) x
      - SobolevEuclidean.contRep hp (hS.choose u) y‖ₑ
      ≤ K₁ * ENNReal.ofReal ‖(hS.choose u : SobolevEuclidean N 1 p ⊤)‖
        * ENNReal.ofReal (‖(x : EuclideanSpace ℝ (Fin N)) - y‖ ^ (1 - N / (p : ℝ))) := by
    rw [hK₁]
    refine (SobolevEuclidean.enorm_contRep_sub_le hp (hS.choose u) x y).trans ?_
    calc morreyConst volume p * ENNReal.ofReal (‖(x : EuclideanSpace ℝ (Fin N)) - y‖
            ^ (1 - N / (p : ℝ)))
          * ∑ i, ENNReal.ofReal ‖weakDeriv (hS.choose u) (MultiIndexLE.single i)‖
        ≤ morreyConst volume p * ENNReal.ofReal (‖(x : EuclideanSpace ℝ (Fin N)) - y‖
            ^ (1 - N / (p : ℝ)))
            * (N * ENNReal.ofReal ‖(hS.choose u : SobolevEuclidean N 1 p ⊤)‖) :=
          mul_le_mul' le_rfl (SobolevEuclidean.sum_ofReal_norm_weakDeriv_single_le _)
      _ = _ := by ring
  have h2 : ‖(hS.choose u : SobolevEuclidean N 1 p ⊤)‖ ≤ C₀ * ‖u‖ := by
    rw [hC₀]
    exact hS.choose.le_opNorm u
  rw [← toReal_enorm]
  refine (ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK₁t ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
    h1).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal (by positivity)]
  calc K₁.toReal * ‖(hS.choose u : SobolevEuclidean N 1 p ⊤)‖
        * ‖(x : EuclideanSpace ℝ (Fin N)) - y‖ ^ (1 - N / (p : ℝ))
      ≤ K₁.toReal * (C₀ * ‖u‖) * ‖(x : EuclideanSpace ℝ (Fin N)) - y‖ ^ (1 - N / (p : ℝ)) := by
        gcongr
    _ = K₁.toReal * C₀ * ‖u‖ * ‖(x : EuclideanSpace ℝ (Fin N)) - y‖ ^ (1 - N / (p : ℝ)) := by
        ring

/-- Let $\Omega$ be an extension domain for $W^{1,p}$, let $N < p < \infty$, and let
$K \subseteq \mathbb{R}^N$ be compact. The **continuous representative on $K$** is the bounded
linear map $W^{1,p}(\Omega) \to C(K)$, $u \mapsto \tilde u|_K$. For $K \supseteq \Omega$,
typically $K = \bar\Omega$, it is the inclusion $W^{1,p}(\Omega) \subset C(\bar\Omega)$ of
footnote 15 to Corollary 9.14 of [brezis2011functional].

It is `HasSobolevExtensionOn.toContinuousMapOnL` for the subspace $S = W^{1,p}(\Omega)$. -/
noncomputable def SobolevEuclidean.toContinuousMapL (hΩ : IsSobolevExtensionDomain N p Ω)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K] :
    SobolevEuclidean N 1 p Ω →L[ℝ] C(K, ℝ) :=
  (hΩ.toContinuousMapOnL hp K).comp
    ((ContinuousLinearMap.id ℝ (SobolevEuclidean N 1 p Ω)).codRestrict ⊤ fun _ ↦ Submodule.mem_top)

/-- The map `SobolevEuclidean.toContinuousMapL` at $u$ is `HasSobolevExtensionOn.toContinuousMapOnL`
for the subspace $W^{1,p}(\Omega)$ at $u$. -/
theorem SobolevEuclidean.toContinuousMapL_apply (hΩ : IsSobolevExtensionDomain N p Ω)
    (hp : N < p) (K : Set (EuclideanSpace ℝ (Fin N))) [CompactSpace K]
    (u : SobolevEuclidean N 1 p Ω) :
    SobolevEuclidean.toContinuousMapL hΩ hp K u
      = hΩ.toContinuousMapOnL hp K ⟨u, Submodule.mem_top⟩ :=
  rfl

/-- Let $\Omega$ be an extension domain for $W^{1,p}$, and let $N < p < \infty$. For every
$u \in W^{1,p}(\Omega)$, $u = \widetilde{Pu}$ almost everywhere on $\Omega$, where
$\widetilde{Pu}$ is the continuous representative of $Pu$ for the chosen extension operator $P$. -/
theorem SobolevEuclidean.fn_ae_eq_toContinuousMapL (hΩ : IsSobolevExtensionDomain N p Ω)
    (hp : N < p) (u : SobolevEuclidean N 1 p Ω) :
    fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      SobolevEuclidean.contRep hp (hΩ.choose ⟨u, Submodule.mem_top⟩) :=
  hΩ.fn_ae_eq_toContinuousMapOnL hp ⟨u, Submodule.mem_top⟩

/-- Let $\Omega$ be an extension domain for $W^{1,p}$, let $N < p < \infty$, and let
$K \supseteq \Omega$ be compact. Then the map $W^{1,p}(\Omega) \to C(K)$ of
`SobolevEuclidean.toContinuousMapL` is injective. -/
theorem SobolevEuclidean.toContinuousMapL_injective (hΩ : IsSobolevExtensionDomain N p Ω)
    (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))} [CompactSpace K]
    (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    Function.Injective (SobolevEuclidean.toContinuousMapL hΩ hp K) := fun u v huv ↦ by
  have := hΩ.toContinuousMapOnL_injective hp hK huv
  simpa using congrArg Subtype.val this

/-- Let $\Omega$ be an extension domain for $W^{1,p}$, let $N < p < \infty$, and let
$K \supseteq \Omega$ be compact. Then $$W^{1,p}(\Omega) \hookrightarrow C(K).$$ This is the
inclusion $W^{1,p}(\Omega) \subset C(\bar\Omega)$ of Corollary 9.14 of [brezis2011functional],
with continuous injection.

The embedding is `SobolevEuclidean.toContinuousMapL`. -/
theorem SobolevEuclidean.isContinuousEmbedding_toContinuousMapL
    (hΩ : IsSobolevExtensionDomain N p Ω) (hp : N < p) {K : Set (EuclideanSpace ℝ (Fin N))}
    [CompactSpace K] (hK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) :
    IsContinuousEmbedding (SobolevEuclidean.toContinuousMapL hΩ hp K).toLinearMap :=
  ⟨SobolevEuclidean.toContinuousMapL_injective hΩ hp hK, _,
    (SobolevEuclidean.toContinuousMapL hΩ hp K).le_opNorm⟩

end ToContinuousMap

/-! ### Corollary 9.15: the higher-order embeddings on an extension domain -/

section HigherOrderDomain

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

variable (N Ω) in
/-- An open set $\Omega \subseteq \mathbb{R}^N$ is an **extension domain for every exponent** if it
is an extension domain for $W^{1,q}$ for every $q \in [1, \infty]$.

This is the hypothesis of Corollary 9.15 of [brezis2011functional], which assumes an open set of
class $C^1$ with bounded boundary, or the half space. The higher-order embeddings apply
Corollary 9.14 at the exponents that arise in the induction. -/
def IsSobolevExtensionDomainAll : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], IsSobolevExtensionDomain N q Ω

/-- If $\Omega$ is an extension domain for every exponent, then it is an extension domain for
$W^{1,q}$ for each $q \in [1, \infty]$. -/
theorem IsSobolevExtensionDomainAll.isSobolevExtensionDomain (h : IsSobolevExtensionDomainAll N Ω)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] : IsSobolevExtensionDomain N q Ω :=
  h q

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class $C^1$, in the sense of charts,
with bounded boundary. Then $\Omega$ is an extension domain for every exponent. So the
hypothesis of Corollary 9.15 of [brezis2011functional] holds for such a set.

The extension operators come from Theorem 9.7,
`IsSobolevExtensionDomain.of_isContDiffChartDomain`. -/
theorem IsSobolevExtensionDomainAll.of_isContDiffChartDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsSobolevExtensionDomainAll (d + 1) Ω :=
  fun _ _ ↦ IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ hΓ

/-- Let $1 \le p \le q < \infty$ with $1/p - 1/N \le 1/q$, and suppose that $N \ge 2$ or $p > 1$.
Let $\Omega$ be an extension domain for $W^{1,p}$. Then there is a finite $K \ge 0$ with
$$\|u\|_{L^q(\Omega)} \le K \|u\| \qquad \text{for all } u \in W^{1,p}(\Omega).$$ This covers
the $L^q$ clauses of Corollary 9.14 of [brezis2011functional] in one statement: $q \le p^*$ for
$p < N$, any $q \ge N$ for $p = N$, and any $q \ge p$ for $p > N$.

The proof transfers the whole-space statement
`SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le` along the extension operator. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le_of_hasSobolevExtension {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N p Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N 1 p Ω,
      eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        ≤ K * ENNReal.ofReal ‖u‖ := by
  obtain ⟨K, hK, hKu⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le (N := N) hN hpq hq
  obtain ⟨C, hC0, hC⟩ := hΩ.exists_forall_eLpNorm_fn_le (K := K.toReal) fun v ↦ by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
    exact hKu v
  exact ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun u ↦ by
    rw [← ENNReal.ofReal_mul hC0]
    exact hC ⟨u, Submodule.mem_top⟩⟩

/-- Let $m \in \mathbb{N}$ and $1 \le p \le q < \infty$ with $1/p - m/N \le 1/q$, and suppose that
$N \ge 2$ or $p > 1$. Let $\Omega$ be an extension domain for every exponent. Then there is a
finite $K \ge 0$ with $$\|u\|_{L^q(\Omega)} \le K \|u\| \qquad \text{for all } u \in
W^{m,p}(\Omega).$$ This is the $L^q$ bound of Corollary 9.15 of [brezis2011functional].

The proof is by induction on $m$, through
`SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le`, as for
Corollary 9.13. This is the "repeated application of Corollary 9.14" of the source. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension (m : ℕ)
    {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N m p Ω,
      eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        ≤ K * ENNReal.ofReal ‖u‖ := by
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
      exact SobolevMultiIndex.eLpNorm_fn_le_ofReal_norm u⟩
  | succ m ih =>
    have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
    obtain ⟨r, hpr, hrq, hr₁, hr₂⟩ :=
      NNReal.exists_intermediate_sobolev_exponent (N := N) m (zero_lt_one.trans_le hp1) hpq hq
    have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
    have hNr : 2 ≤ N ∨ 1 < r := hN.imp id fun h ↦ h.trans_le hpr
    obtain ⟨K₁, hK₁, hK₁u⟩ := ih (q := r) hN hpr hr₁
    obtain ⟨K₂, hK₂, hK₂u⟩ :=
      SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le_of_hasSobolevExtension (hΩ r)
        hNr hrq hr₂
    refine ⟨K₂ * ((N + 1) * K₁), ENNReal.mul_ne_top hK₂ (ENNReal.mul_ne_top (by simp) hK₁),
      fun u ↦ ?_⟩
    obtain ⟨w, hw, hwn⟩ :=
      SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le hK₁ hK₁u u
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

/-- Let $m \in \mathbb{N}$ and $1 \le p \le q < \infty$ with $1/p - m/N \le 1/q$, and suppose that
$N \ge 2$ or $p > 1$. If $\Omega$ is an extension domain for every exponent, then every
$u \in W^{m,p}(\Omega)$ lies in $L^q(\Omega)$. This is the $L^q$ clauses of Corollary 9.15 of
[brezis2011functional].

For $1/p - m/N > 0$ the largest $q$ is given by $1/q = 1/p - m/N$. For $1/p - m/N \le 0$ every
$q \in [p, \infty)$ is allowed. -/
theorem SobolevEuclidean.memLp_fn_of_order_of_hasSobolevExtension {m : ℕ} {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) (u : SobolevEuclidean N m p Ω) :
    MemLp (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨K, hK, hKu⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension m hΩ hN hpq hq
  exact memLp_iff.2 ((hKu u).trans_lt (ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top))

/-- Let $m \in \mathbb{N}$ and $1 \le p \le q < \infty$ with $1/p - m/N \le 1/q$, and suppose that
$N \ge 2$ or $p > 1$. If $\Omega$ is an extension domain for every exponent, then
$$W^{m,p}(\Omega) \hookrightarrow L^q(\Omega).$$ This is the $L^q$ clauses of Corollary 9.15 of
[brezis2011functional].

The embedding is the inclusion `SobolevMultiIndex.toLpₗ`. -/
theorem SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension {m : ℕ}
    {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - m / N ≤ (q : ℝ)⁻¹) :
    IsContinuousEmbedding (toLpₗ ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m p Ω volume
      (SobolevEuclidean.memLp_fn_of_order_of_hasSobolevExtension hΩ hN hpq hq)) := by
  obtain ⟨K, hK, hKu⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension m hΩ hN hpq hq
  refine isContinuousEmbedding_toLpₗ_of_eLpNorm_le _ (C := K.toReal) fun u ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
  exact hKu u

/-- Let $m \in \mathbb{N}$ and $1 \le p < \infty$ with $m > N/p$, and suppose that $N \ge 2$ or
$p > 1$. Let $\Omega$ be an extension domain for every exponent. Then there are $C \ge 0$ and
$\theta \in (0, 1]$, with $\theta = m - N/p$ when $m - N/p < 1$, such that every
$u \in W^{m,p}(\Omega)$ has a representative $\tilde u : \mathbb{R}^N \to \mathbb{R}$ with these
properties: $\tilde u$ is continuous on $\mathbb{R}^N$, $u = \tilde u$ almost everywhere on
$\Omega$, and for all $x, y \in \mathbb{R}^N$ $$|\tilde u(x)| \le C \|u\|, \qquad |\tilde u(x) -
\tilde u(y)| \le C \|u\| \, |x - y|^\theta.$$ In particular $W^{m,p}(\Omega) \subset
L^\infty(\Omega) \cap C(\bar\Omega)$ when $1/p - m/N < 0$. This is Corollary 9.15 of
[brezis2011functional], footnote 16 for $k = 0$.

The proof embeds $W^{m,p}(\Omega)$ in $W^{1,r}(\Omega)$ for the exponent $r > N$ of
`NNReal.exists_morrey_exponent`, and then applies Corollary 9.14 for $r > N$. -/
theorem SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension {m : ℕ}
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hN : 2 ≤ N ∨ 1 < p) (hm : (N : ℝ) / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p < 1 → θ = m - N / p) ∧
      ∀ u : SobolevEuclidean N m p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
        (∀ x, ‖ũ x‖ ≤ C * ‖u‖) ∧ ∀ x y, ‖ũ x - ũ y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ≥0) < p := zero_lt_one.trans_le hp1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    refine ⟨m - 1, ?_⟩
    have : 0 < m := by exact_mod_cast (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ N / p) hm)
    omega
  obtain ⟨r, hpr, hNr, hr₁, hθ⟩ := NNReal.exists_morrey_exponent (N := N) m' hp0 hm
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpr⟩
  obtain ⟨K₁, hK₁, hK₁u⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension m' hΩ hN hpr hr₁
  obtain ⟨C₁, hC₁⟩ := SobolevEuclidean.exists_continuousOn_closure_holderWith_ae_eq (hΩ r) hNr
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (N + 1) * K₁.toReal := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ by positivity
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (Nat.cast_nonneg N) (by exact_mod_cast hNr)
  have hα : ((1 - (N : ℝ≥0) / r : ℝ≥0) : ℝ) = 1 - N / (r : ℝ) := by
    rw [NNReal.coe_sub ((div_le_one (by exact_mod_cast hr0)).2 hNr.le)]
    simp
  refine ⟨C₁ * D, 1 - N / r, by positivity, ?_, ?_, hθ, fun u ↦ ?_⟩
  · exact sub_pos.2 ((div_lt_one hr0).2 (by exact_mod_cast hNr))
  · exact sub_le_self _ (by positivity)
  obtain ⟨w, hw, hwn⟩ :=
    SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le hK₁ hK₁u u
  rw [← hD] at hwn
  obtain ⟨ũ, hũc, hũae, hũh, hũb⟩ := hC₁ w
  refine ⟨ũ, hũc, hw.symm.trans hũae, fun x ↦ ?_, fun x y ↦ ?_⟩
  · calc ‖ũ x‖ ≤ C₁ * ‖w‖ := hũb x
      _ ≤ C₁ * (D * ‖u‖) := mul_le_mul_of_nonneg_left hwn C₁.coe_nonneg
      _ = C₁ * D * ‖u‖ := by ring
  · have h1 := hũh.dist_le x y
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, hα] at h1
    calc ‖ũ x - ũ y‖ ≤ C₁ * ‖w‖ * ‖x - y‖ ^ (1 - N / (r : ℝ)) := h1
      _ ≤ C₁ * (D * ‖u‖) * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by gcongr
      _ = C₁ * D * ‖u‖ * ‖x - y‖ ^ (1 - N / (r : ℝ)) := by ring

/-- Let $m \in \mathbb{N}$ and $1 \le p < \infty$ with $m > N/p$, and suppose that $N \ge 2$ or
$p > 1$. If $\Omega$ is an extension domain for every exponent, then every
$u \in W^{m,p}(\Omega)$ lies in $L^\infty(\Omega)$. This is the inclusion
$W^{m,p}(\Omega) \subset L^\infty(\Omega)$ of Corollary 9.15 of [brezis2011functional] for
$1/p - m/N < 0$. -/
theorem SobolevEuclidean.memLp_fn_top_of_order_of_hasSobolevExtension {m : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hm : (N : ℝ) / p < m) (u : SobolevEuclidean N m p Ω) :
    MemLp (fn u) ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨C, θ, hC0, -, -, -, hC⟩ :=
    SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension hΩ hN hm
  obtain ⟨ũ, hc, hae, hb, -⟩ := hC u
  refine memLp_iff.2 ?_
  rw [eLpNorm_congr_ae hae]
  refine (eLpNorm_le_of_ae_enorm_bound (C := ENNReal.ofReal (C * ‖u‖))
    hc.aestronglyMeasurable.restrict (Eventually.of_forall fun x ↦ ?_)).trans_lt (by simp)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hb x)

/-- Let $k, m \in \mathbb{N}$ and $1 \le p < \infty$ with $k + N/p < m$, and suppose that $N \ge 2$
or $p > 1$. Let $\Omega$ be an extension domain for every exponent. Then there are $C \ge 0$ and
$\theta \in (0, 1]$, with $\theta = m - N/p - k$ when $m - N/p - k < 1$, such that every
$u \in W^{m,p}(\Omega)$ has a representative $\tilde u : \mathbb{R}^N \to \mathbb{R}$ with these
properties.

* $\tilde u$ is continuous on $\mathbb{R}^N$, of class $C^k$ on $\Omega$, and $u = \tilde u$
  almost everywhere on $\Omega$.
* For each $j \le k$ there is a continuous $G_j$ on $\mathbb{R}^N$ with $D^j \tilde u = G_j$ on
  $\Omega$ and $\|G_j(x)\| \le C \|u\|$ for all $x$.
* There is a continuous $G$ on $\mathbb{R}^N$ with $D^k \tilde u = G$ on $\Omega$,
  $\|G(x)\| \le C \|u\|$ and $\|G(x) - G(y)\| \le C \|u\| \, |x - y|^\theta$ for all $x, y$.

This is the clause $W^{m,p}(\Omega) \subset C^k(\bar\Omega)$ of Corollary 9.15 of
[brezis2011functional], footnote 16, in the form that the induction needs. The functions $G_j$
are the continuous extensions to $\bar\Omega$ of the derivatives, which define $C^k(\bar\Omega)$
in the source.

The proof is by induction on $k$, as in
`SobolevEuclidean.exists_forall_contDiff_ae_eq_of_order`. The derivatives are assembled from the
extensions of the derivatives of the partial derivatives. -/
theorem SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order (k : ℕ) {m : ℕ}
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p - k < 1 → θ = m - N / p - k) ∧
      ∀ u : SobolevEuclidean N m p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        ContDiffOn ℝ k ũ Ω ∧ fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
        (∀ j ≤ k, ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
          Continuous G ∧ EqOn (iteratedFDeriv ℝ j ũ) G Ω ∧ ∀ x, ‖G x‖ ≤ C * ‖u‖) ∧
        ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×k]→L[ℝ] ℝ),
          Continuous G ∧ EqOn (iteratedFDeriv ℝ k ũ) G Ω ∧ (∀ x, ‖G x‖ ≤ C * ‖u‖) ∧
          ∀ x y, ‖G x - G y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  induction k generalizing m with
  | zero =>
    rw [Nat.cast_zero, zero_add] at hm
    obtain ⟨C, θ, hC0, hθ0, hθ1, hθ, hC⟩ :=
      SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension hΩ hN hm
    refine ⟨C, θ, hC0, hθ0, hθ1, fun h ↦ ?_, fun u ↦ ?_⟩
    · rw [Nat.cast_zero, sub_zero] at h ⊢
      exact hθ h
    obtain ⟨ũ, hc, hae, hb, hh⟩ := hC u
    have hG : ∀ j ≤ 0, ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ j ũ) G Ω ∧ ∀ x, ‖G x‖ ≤ C * ‖u‖ := by
      intro j hj
      obtain rfl : j = 0 := Nat.le_zero.1 hj
      refine ⟨iteratedFDeriv ℝ 0 ũ, ?_, fun x _ ↦ rfl, fun x ↦ ?_⟩
      · rw [iteratedFDeriv_zero_eq_comp]
        exact (continuousMultilinearCurryFin0 ℝ _ ℝ).symm.continuous.comp hc
      · rw [norm_iteratedFDeriv_zero]
        exact hb x
    refine ⟨ũ, hc, contDiffOn_zero.2 hc.continuousOn, hae, hG, iteratedFDeriv ℝ 0 ũ, ?_,
      fun x _ ↦ rfl, fun x ↦ ?_, fun x y ↦ ?_⟩
    · rw [iteratedFDeriv_zero_eq_comp]
      exact (continuousMultilinearCurryFin0 ℝ _ ℝ).symm.continuous.comp hc
    · rw [norm_iteratedFDeriv_zero]
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
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : SobolevEuclidean N m' p Ω,
        v₀ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume
          (Nat.le_succ m') u :=
      ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin N → SobolevEuclidean N m' p Ω,
        v = fun i ↦ partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume i u :=
      ⟨_, rfl⟩
    have hv₀fn : fn v₀ = fn u := by rw [hv₀]; rfl
    have hv₀n : ‖v₀‖ ≤ ‖u‖ := by rw [hv₀]; exact norm_toLowerOrder_le _ u
    have hvn : ∀ i, ‖v i‖ ≤ ‖u‖ := fun i ↦ by rw [hv]; exact norm_partialDeriv_le i u
    obtain ⟨ũ, hũc, hũk, hũae, hũG, -⟩ := hC v₀
    rw [hv₀fn] at hũae
    choose g hgc hgk hgae hgG hgH using fun i ↦ hC (v i)
    choose H hHc hHeq hHb hHh using hgH
    -- the tensor weak derivative of `fn u` on `Ω`, continuous
    obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
        w = fun x ↦ ∑ i, g i x • PiLp.proj 2 (fun _ : Fin N ↦ ℝ) i := ⟨_, rfl⟩
    have hwk : ContDiffOn ℝ k w Ω := by
      rw [hw]
      exact ContDiffOn.sum fun i _ ↦ (hgk i).smul contDiffOn_const
    have hwc : Continuous w := by
      rw [hw]
      exact continuous_finsetSum _ fun i _ ↦ (hgc i).smul continuous_const
    have hweak : HasWeakFDerivOn (fn u) w Ω volume := by
      rw [hw]
      exact SobolevEuclidean.hasWeakFDerivOn_sum_smul_proj u fun i ↦ by
        have h := hgae i
        rw [hv] at h
        exact h
    -- `ũ` is `C¹` on `Ω` with derivative `w`
    obtain ⟨v', hv'c, hv'ae, hv'd⟩ :=
      hweak.exists_contDiffOn_ae_eq_of_continuousOn hwc.continuousOn
    have hv'ũ : EqOn v' ũ Ω :=
      Measure.eqOn_open_of_ae_eq (hv'ae.symm.trans hũae) Ω.isOpen hv'c.continuousOn
        hũc.continuousOn
    have hd : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), HasFDerivAt ũ (w x) x := fun x hx ↦
      (hv'd x hx).congr_of_eventuallyEq (by
        filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
        exact (hv'ũ hy).symm)
    have hfd : EqOn (fderiv ℝ ũ) w Ω := fun x hx ↦ (hd x hx).fderiv
    have hũk' : ContDiffOn ℝ (k + 1) ũ Ω := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen Ω.isOpen]
      exact ⟨fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt, by simp,
        hwk.congr fun x hx ↦ hfd hx⟩
    -- the top derivative on `Ω`, and its extension
    have hDw : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), iteratedFDeriv ℝ k w x
        = ∑ i, (L i).compContinuousMultilinearMap (H i x) := by
      intro x hx
      rw [hw, hL, iteratedFDeriv_fun_sum_smul_const_of_contDiffAt
        (fun i ↦ (hgk i).contDiffAt (Ω.isOpen.mem_nhds hx)) _ le_rfl]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hHeq i hx]
    have hDũ : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), iteratedFDeriv ℝ (k + 1) ũ x
        = (continuousMultilinearCurryRightEquiv' ℝ k (EuclideanSpace ℝ (Fin N)) ℝ).symm
          (∑ i, (L i).compContinuousMultilinearMap (H i x)) := by
      intro x hx
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, ← hDw x hx]
      congr 1
      refine ((Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) ?_ k).eq_of_nhds)
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact hfd hy
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×(k + 1)]→L[ℝ] ℝ),
        G = fun x ↦ (continuousMultilinearCurryRightEquiv' ℝ k (EuclideanSpace ℝ (Fin N)) ℝ).symm
          (∑ i, (L i).compContinuousMultilinearMap (H i x)) := ⟨_, rfl⟩
    have hGc : Continuous G := by
      rw [hG]
      refine (continuousMultilinearCurryRightEquiv' ℝ k _ ℝ).symm.continuous.comp
        (continuous_finsetSum _ fun i _ ↦ ?_)
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ ℝ _ (L i)).continuous.comp
        (hHc i)
    have hGeq : EqOn (iteratedFDeriv ℝ (k + 1) ũ) G Ω := fun x hx ↦ by
      rw [hG, hDũ x hx]
    have hGb : ∀ x, ‖G x‖ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := fun x ↦ by
      rw [hG, LinearIsometryEquiv.norm_map]
      calc ‖∑ i, (L i).compContinuousMultilinearMap (H i x)‖
          ≤ ∑ i, ‖L i‖ * ‖H i x‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
              ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
        _ ≤ ∑ i, ‖L i‖ * (C₀ * ‖u‖) := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_left ((hHb i x).trans
              (mul_le_mul_of_nonneg_left (hvn i) hC₀)) (norm_nonneg _)
        _ = C₀ * (∑ i, ‖L i‖) * ‖u‖ := by rw [← Finset.sum_mul]; ring
        _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by gcongr; linarith
    refine ⟨ũ, hũc, hũk', hũae, fun j hj ↦ ?_, G, hGc, hGeq, hGb, fun x y ↦ ?_⟩
    · rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
      · obtain ⟨G', hG'c, hG'eq, hG'b⟩ := hũG j (Nat.lt_succ_iff.1 hjk)
        refine ⟨G', hG'c, hG'eq, fun x ↦ (hG'b x).trans ?_⟩
        calc C₀ * ‖v₀‖ ≤ C₀ * ‖u‖ := mul_le_mul_of_nonneg_left hv₀n hC₀
          _ = C₀ * 1 * ‖u‖ := by ring
          _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ := by gcongr; linarith
      · obtain rfl : j = k + 1 := le_antisymm hj hjk
        exact ⟨G, hGc, hGeq, hGb⟩
    · rw [hG, ← map_sub, LinearIsometryEquiv.norm_map, ← Finset.sum_sub_distrib]
      calc ‖∑ i, ((L i).compContinuousMultilinearMap (H i x)
              - (L i).compContinuousMultilinearMap (H i y))‖
          ≤ ∑ i, ‖L i‖ * ‖H i x - H i y‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
              ContinuousLinearMap.norm_compContinuousMultilinearMap_sub_le _ _ _)
        _ ≤ ∑ i, ‖L i‖ * (C₀ * ‖u‖ * ‖x - y‖ ^ θ) := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_left ((hHh i x y).trans (by gcongr; exact hvn i)) (norm_nonneg _)
        _ = C₀ * (∑ i, ‖L i‖) * ‖u‖ * ‖x - y‖ ^ θ := by rw [← Finset.sum_mul]; ring
        _ ≤ C₀ * (1 + ∑ i, ‖L i‖) * ‖u‖ * ‖x - y‖ ^ θ := by gcongr; linarith

/-- Let $k, m \in \mathbb{N}$ and $1 \le p < \infty$ with $0 < m - N/p - k < 1$, and suppose that
$N \ge 2$ or $p > 1$. Let $\Omega$ be an extension domain for every exponent. Then there is
$C \ge 0$ such that every $u \in W^{m,p}(\Omega)$ has a representative
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ with these properties.

* $\tilde u$ is continuous on $\mathbb{R}^N$, of class $C^k$ on $\Omega$, and $u = \tilde u$
  almost everywhere on $\Omega$.
* For each $j \le k$ there is a continuous $G_j$ on $\mathbb{R}^N$ with $D^j \tilde u = G_j$ on
  $\Omega$ and $\|G_j(x)\| \le C \|u\|$ for all $x$.
* There is a continuous $G$ on $\mathbb{R}^N$ with $D^k \tilde u = G$ on $\Omega$ and $\|G(x) -
  G(y)\| \le C \|u\| \, |x - y|^{m - N/p - k}$ for all $x, y$.

This is the clause $W^{m,p}(\Omega) \subset C^k(\bar\Omega)$ of Corollary 9.15 of
[brezis2011functional], footnote 16, for $m - N/p$ not an integer, $k = \lfloor m - N/p \rfloor$
and $\theta = m - N/p - k$.

The conditions on $k$ and $\theta$ are encoded as $0 < m - N/p - k < 1$. -/
theorem SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order {m k : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hθ0 : 0 < (m : ℝ) - N / p - k) (hθ1 : (m : ℝ) - N / p - k < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N m p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ,
      Continuous ũ ∧ ContDiffOn ℝ k ũ Ω ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      (∀ j ≤ k, ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ j ũ) G Ω ∧ ∀ x, ‖G x‖ ≤ C * ‖u‖) ∧
      ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×k]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ k ũ) G Ω ∧
        ∀ x y, ‖G x - G y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ ((m : ℝ) - N / p - k) := by
  obtain ⟨C, θ, hC0, -, -, hθ, hC⟩ :=
    SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order (N := N) k (m := m) hΩ hN
      (by linarith)
  obtain rfl := hθ hθ1
  refine ⟨C, hC0, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hk, hae, hG, G, hGc, hGeq, -, hGh⟩ := hC u
  exact ⟨ũ, hc, hk, hae, hG, G, hGc, hGeq, hGh⟩

/-- Let $k, m \in \mathbb{N}$ and $1 \le p < \infty$ with $k + N/p < m$, and suppose that $N \ge 2$
or $p > 1$. Let $\Omega$ be an extension domain for every exponent. Then there are $C \ge 0$ and
$\theta \in (0, 1]$ such that every $u \in W^{m,p}(\Omega)$ has a representative
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ with these properties.

* $\tilde u$ is continuous on $\mathbb{R}^N$, of class $C^k$ on $\Omega$, and $u = \tilde u$
  almost everywhere on $\Omega$.
* For each $j \le k$ there is a continuous $G_j$ on $\mathbb{R}^N$ with $D^j \tilde u = G_j$ on
  $\Omega$ and $\|G_j(x)\| \le C \|u\|$ for all $x$.
* There is a continuous $G$ on $\mathbb{R}^N$ with $D^k \tilde u = G$ on $\Omega$ and
  $\|G(x) - G(y)\| \le C \|u\| \, |x - y|^\theta$ for all $x, y$.

This is the clause $W^{m,p}(\Omega) \subset C^k(\bar\Omega)$ of Corollary 9.15 of
[brezis2011functional] without the condition that $m - N/p$ is not an integer.

The sup bound makes the map into $C^k(\bar\Omega)$ bounded, as the proofs of Theorems 10.1 and
10.8 of [brezis2011functional] need for the heat equation. -/
theorem SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_lt {m k : ℕ} {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p)
    (hm : (k : ℝ) + N / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ∀ u : SobolevEuclidean N m p Ω,
      ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧ ContDiffOn ℝ k ũ Ω ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      (∀ j ≤ k, ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ j ũ) G Ω ∧ ∀ x, ‖G x‖ ≤ C * ‖u‖) ∧
      ∃ G : EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×k]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ k ũ) G Ω ∧
        ∀ x y, ‖G x - G y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  obtain ⟨C, θ, hC0, hθ0, hθ1, -, hC⟩ :=
    SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order (N := N) k hΩ hN hm
  refine ⟨C, θ, hC0, hθ0, hθ1, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hk, hae, hG, G, hGc, hGeq, -, hGh⟩ := hC u
  exact ⟨ũ, hc, hk, hae, hG, G, hGc, hGeq, hGh⟩

end HigherOrderDomain

/-! ### Lowering the order: $W^{m+j+1,p}(\Omega) \to W^{j+1,q}(\Omega)$ as a bounded linear map -/

section Lower

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- Let $j, m \in \mathbb{N}$ and $p, q \in [1, \infty]$, and let $\Omega \subseteq \mathbb{R}^N$ be
open. Suppose that there is a finite $K$ with $\|v\|_{L^q(\Omega)} \le K \|v\|$ for every
$v \in W^{m,p}(\Omega)$. Then there is a bounded linear map
$T : W^{m+j+1,p}(\Omega) \to W^{j+1,q}(\Omega)$ with $Tu = u$ almost everywhere on $\Omega$ for
every $u$.

The proof is by induction on $j$. The case $j = 0$ is
`SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le`, and the step is
`SobolevMultiIndex.exists_succ_of_partialDeriv`, applied to $u$ and its partial derivatives. The
map is unique by `SobolevMultiIndex.ext_of_fn_ae_eq`, and hence linear. This is the "repeated
application" in the proof of Corollary 9.15 of [brezis2011functional]. -/
theorem SobolevEuclidean.exists_continuousLinearMap_of_forall_eLpNorm_fn_le (j : ℕ) {m : ℕ}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ v : SobolevEuclidean N m p Ω, eLpNorm (fn v) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖v‖) :
    ∃ T : SobolevEuclidean N (m + j + 1) p Ω →L[ℝ] SobolevEuclidean N (j + 1) q Ω,
      ∀ u, fn (T u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u := by
  induction j with
  | zero =>
    choose w hw hwn using fun u : SobolevEuclidean N (m + 0 + 1) p Ω ↦
      SobolevEuclidean.exists_sobolevEuclidean_one_of_forall_eLpNorm_fn_restrict_le hK h u
    refine ⟨LinearMap.mkContinuous
      { toFun := w
        map_add' := fun u v ↦ ext_of_fn_ae_eq ?_
        map_smul' := fun c u ↦ ext_of_fn_ae_eq ?_ } ((N + 1) * K.toReal) fun u ↦ hwn u, hw⟩
    · exact (hw _).trans ((fn_add u v).trans
        (((hw u).symm.add (hw v).symm).trans (fn_add _ _).symm))
    · exact (hw _).trans ((fn_smul c u).trans
        (((hw u).symm.const_smul c).trans (fn_smul _ _).symm))
  | succ j ih =>
    obtain ⟨T, hT⟩ := ih
    have hstep : ∀ u : SobolevEuclidean N (m + j + 1 + 1) p Ω,
        ∃ z : SobolevEuclidean N (j + 1 + 1) q Ω,
          fn z =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u ∧
          ‖z‖ ≤ Fintype.card (MultiIndexLE (Fin N) (j + 1 + 1)) * ((N + 1) * ‖T‖) * ‖u‖ := by
      intro u
      obtain ⟨v₀, hv₀⟩ : ∃ v₀ : SobolevEuclidean N (m + j + 1) p Ω,
          v₀ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume
            (Nat.le_succ _) u :=
        ⟨_, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v : Fin N → SobolevEuclidean N (m + j + 1) p Ω,
          v = fun i ↦ partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume i u :=
        ⟨_, rfl⟩
      have hv₀fn : fn v₀ = fn u := by rw [hv₀]; rfl
      have hv₀n : ‖v₀‖ ≤ ‖u‖ := by rw [hv₀]; exact norm_toLowerOrder_le _ u
      have hvn : ∀ i, ‖v i‖ ≤ ‖u‖ := fun i ↦ by rw [hv]; exact norm_partialDeriv_le i u
      have hw₀ : fn (T v₀) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u :=
        hv₀fn ▸ hT v₀
      have hw : ∀ i, fn (T (v i)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
          fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume i u) :=
        fun i ↦ by rw [hv] at *; exact hT _
      obtain ⟨z, hz, hzn⟩ := exists_succ_of_partialDeriv u (T v₀) hw₀ (fun i ↦ T (v i)) hw
      refine ⟨z, hz, hzn.trans ?_⟩
      have hT₀ : ‖T v₀‖ ≤ ‖T‖ * ‖u‖ :=
        (T.le_opNorm v₀).trans (mul_le_mul_of_nonneg_left hv₀n (norm_nonneg _))
      have hTi : ∑ i, ‖T (v i)‖ ≤ N * (‖T‖ * ‖u‖) := by
        calc ∑ i, ‖T (v i)‖ ≤ ∑ _i : Fin N, ‖T‖ * ‖u‖ := Finset.sum_le_sum fun i _ ↦
              (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hvn i) (norm_nonneg _))
          _ = N * (‖T‖ * ‖u‖) := by simp
      calc (Fintype.card (MultiIndexLE (Fin N) (j + 1 + 1)) : ℝ) * (‖T v₀‖ + ∑ i, ‖T (v i)‖)
          ≤ Fintype.card (MultiIndexLE (Fin N) (j + 1 + 1)) * (‖T‖ * ‖u‖ + N * (‖T‖ * ‖u‖)) := by
            gcongr
        _ = Fintype.card (MultiIndexLE (Fin N) (j + 1 + 1)) * ((N + 1) * ‖T‖) * ‖u‖ := by ring
    choose z hz hzn using hstep
    refine ⟨LinearMap.mkContinuous
      { toFun := z
        map_add' := fun u v ↦ ext_of_fn_ae_eq ?_
        map_smul' := fun c u ↦ ext_of_fn_ae_eq ?_ }
      (Fintype.card (MultiIndexLE (Fin N) (j + 1 + 1)) * ((N + 1) * ‖T‖)) fun u ↦ hzn u, hz⟩
    · exact (hz _).trans ((fn_add u v).trans
        (((hz u).symm.add (hz v).symm).trans (fn_add _ _).symm))
    · exact (hz _).trans ((fn_smul c u).trans
        (((hz u).symm.const_smul c).trans (fn_smul _ _).symm))

/-- Let $m \in \mathbb{N}$ and $1 \le p \le r < \infty$ with $1/p - m/N \le 1/r$, and suppose that
$N \ge 2$ or $p > 1$. Let $\Omega$ be an extension domain for every exponent. Then there is a
bounded linear map $T : W^{m+1,p}(\Omega) \to W^{1,r}(\Omega)$ with $Tu = u$ almost everywhere
on $\Omega$ for every $u$.

This is the case $j = 0$ of
`SobolevEuclidean.exists_continuousLinearMap_of_forall_eLpNorm_fn_le`, for the $L^r$ bound of
Corollary 9.15 of [brezis2011functional] at order $m$,
`SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension`. Through it, the
embeddings of $W^{m+1,p}(\Omega)$ follow from those of $W^{1,r}(\Omega)$. -/
theorem SobolevEuclidean.exists_continuousLinearMap_orderOne (m : ℕ) {p r : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (r : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hN : 2 ≤ N ∨ 1 < p) (hpr : p ≤ r) (hr : (p : ℝ)⁻¹ - m / N ≤ (r : ℝ)⁻¹) :
    ∃ T : SobolevEuclidean N (m + 1) p Ω →L[ℝ] SobolevEuclidean N 1 r Ω,
      ∀ u, fn (T u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u := by
  obtain ⟨K, hK, hKu⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension m hΩ hN hpr hr
  exact SobolevEuclidean.exists_continuousLinearMap_of_forall_eLpNorm_fn_le 0 hK hKu

/-- Let $m \in \mathbb{N}$ and $p, r \in [0, \infty]$, and let $\Omega \subseteq \mathbb{R}^N$ be
open. Suppose that every function in $W^{m+1,p}(\Omega)$ lies in $W^{1,r}(\Omega)$. Then, for
every $j \in \mathbb{N}$, every function in $W^{m+1+j,p}(\Omega)$ lies in $W^{j+1,r}(\Omega)$.

Here the spaces are read through the membership predicate `MemSobolevMultiIndex` for the
standard basis. The proof is by induction on $j$ through `memSobolevMultiIndex_succ_iff`: each
partial derivative of a function in $W^{m+1+(j+1),p}(\Omega)$ lies in $W^{m+1+j,p}(\Omega)$. -/
theorem MemSobolevMultiIndex.of_forall_mem_one (m : ℕ) {p r : ℝ≥0∞}
    (h1 : ∀ f : EuclideanSpace ℝ (Fin N) → ℝ,
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f (m + 1) p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f 1 r Ω volume)
    (j : ℕ) : ∀ f : EuclideanSpace ℝ (Fin N) → ℝ,
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f (m + 1 + j) p Ω volume →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f (j + 1) r Ω volume := by
  induction j with
  | zero => exact fun f hf ↦ h1 f hf
  | succ j ih =>
    intro f hf
    obtain ⟨hf0, hfd⟩ := memSobolevMultiIndex_succ_iff.1 hf
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih f hf0, fun i ↦ ?_⟩
    obtain ⟨g, hg, hgm⟩ := hfd i
    exact ⟨g, hg, ih g hgm⟩

/-- Let $m, j \in \mathbb{N}$ and $1 \le p \le r < \infty$ with $1/p - m/N \le 1/r$, and suppose
that $N \ge 2$ or $p > 1$. Let $\Omega$ be an extension domain for every exponent. Then there is
a bounded linear map $T : W^{m+1+j,p}(\Omega) \to W^{j+1,r}(\Omega)$ with $Tu = u$ almost
everywhere on $\Omega$ for every $u$.

The proof applies the inclusion $W^{m+1,p}(\Omega) \to W^{1,r}(\Omega)$ of
`SobolevEuclidean.exists_continuousLinearMap_orderOne` to the derivatives of order at most $j$,
and obtains the bound from the closed graph theorem,
`SobolevMultiIndex.exists_continuousLinearMap_of_forall_memSobolevMultiIndex`. Through it, the
embeddings of $W^{m+1+j,p}(\Omega)$ into the Hölder spaces $C^{j,\beta}$ follow from those of
$W^{j+1,r}(\Omega)$ for every large $r$. This is the integer case of the Sobolev embedding
theorem. -/
theorem SobolevEuclidean.exists_continuousLinearMap_lower_of_order (m j : ℕ) {p r : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (r : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hN : 2 ≤ N ∨ 1 < p) (hpr : p ≤ r) (hr : (p : ℝ)⁻¹ - m / N ≤ (r : ℝ)⁻¹) :
    ∃ T : SobolevEuclidean N (m + 1 + j) p Ω →L[ℝ] SobolevEuclidean N (j + 1) r Ω,
      ∀ u, fn (T u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u := by
  obtain ⟨T₁, hT₁⟩ := SobolevEuclidean.exists_continuousLinearMap_orderOne m hΩ hN hpr hr
  have h1 : ∀ f : EuclideanSpace ℝ (Fin N) → ℝ,
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f (m + 1) p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f 1 r Ω volume := by
    intro f hf
    obtain ⟨v, hv⟩ := hf.exists_sobolevMultiIndex
    exact (memSobolevMultiIndex (T₁ v)).congr_ae ((hT₁ v).trans hv)
  have hmem := MemSobolevMultiIndex.of_forall_mem_one m h1 j
  obtain ⟨G, hG⟩ : ∃ G : SobolevEuclidean N (m + 1 + j) p Ω →L[ℝ]
      Lp ℝ r (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ u, (G u : EuclideanSpace ℝ (Fin N) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u :=
    ⟨(fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 r Ω volume).comp (T₁.comp
      (toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p Ω volume
        (Nat.le_add_right (m + 1) j))), fun u ↦ by
      simp only [ContinuousLinearMap.comp_apply, fnL_apply]
      exact hT₁ _⟩
  obtain ⟨T, hT⟩ := SobolevMultiIndex.exists_continuousLinearMap_of_forall_memSobolevMultiIndex G
    fun u ↦ (hmem (fn u) (memSobolevMultiIndex u)).congr_ae (hG u).symm
  refine ⟨T, fun u ↦ ?_⟩
  have := congrArg (fun w : Lp ℝ r (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦
    (w : EuclideanSpace ℝ (Fin N) → ℝ)) (hT u)
  rw [fnL_apply] at this
  exact (Filter.EventuallyEq.of_eq this).trans (hG u)

end Lower

/-! ### Balls are domains of class $C^\infty$ -/

section Ball

variable {d : ℕ}

/-- Let $a > 0$. Then there is a function $\varphi : \mathbb{R} \to \mathbb{R}$ of class $C^\infty$
with $\varphi(s) > 0$ for all $s$ and $\varphi(s) = a - s$ for $0 \le s \le a/4$.

One such function is $a - s \chi(s)$, for a smooth bump $\chi$ that equals $1$ on $[-a/4, a/4]$
and vanishes outside $(-a/2, a/2)$. -/
theorem exists_contDiff_pos_eq_sub {a : ℝ} (ha : 0 < a) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ s, 0 < φ s) ∧ ∀ s, 0 ≤ s → s ≤ a / 4 → φ s = a - s := by
  obtain ⟨χ, hχ⟩ : ∃ χ : ContDiffBump (0 : ℝ), χ = ⟨a / 4, a / 2, by positivity, by linarith⟩ :=
    ⟨_, rfl⟩
  have hIn : χ.rIn = a / 4 := by rw [hχ]
  have hOut : χ.rOut = a / 2 := by rw [hχ]
  refine ⟨fun s ↦ a - s * χ s, contDiff_const.sub (contDiff_id.mul (χ.contDiff (n := ⊤))),
    fun s ↦ ?_, fun s hs0 hs ↦ ?_⟩
  · have h0 : 0 ≤ χ s := χ.nonneg
    have h1 : χ s ≤ 1 := χ.le_one
    rcases le_or_gt s 0 with hs | hs
    · nlinarith
    · rcases le_or_gt s (a / 2) with hs2 | hs2
      · nlinarith
      · have : χ s = 0 := χ.zero_of_le_dist (by
          rw [hOut, dist_zero_right, Real.norm_eq_abs, abs_of_pos hs]
          exact hs2.le)
        change 0 < a - s * χ s
        rw [this]
        linarith
  · have : χ s = 1 := χ.one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff, Real.norm_eq_abs, hIn, abs_le]
      constructor <;> linarith)
    change a - s * χ s = a - s
    rw [this, mul_one]

/-- Let $c \in \mathbb{R}^{d+1}$ and $r > 0$. The open ball $B(c, r)$ is a domain of class
$C^\infty$ in the graph sense of `IsContDiffDomain`.

Near a boundary point $x_0$, a rigid motion $x \mapsto R(x - c)$ takes the unit vector from
$x_0$ to $c$ to the last basis vector, so that $x_0$ becomes the south pole $-r e_{d+1}$. On the
ball of radius $r/2$ about $x_0$, the ball $B(c, r)$ is then the region above the graph of
$y' \mapsto -\sqrt{r^2 - |y'|^2}$. This function is made smooth on all of $\mathbb{R}^d$ by
changing $r^2 - |y'|^2$ away from $|y'|^2 \le r^2/4$, with `exists_contDiff_pos_eq_sub`. -/
theorem isContDiffDomain_ball (c : EuclideanSpace ℝ (Fin (d + 1))) {r : ℝ} (hr : 0 < r) :
    IsContDiffDomain ∞ (ball c r) := by
  refine ⟨isOpen_ball, fun x₀ hx₀ ↦ ?_⟩
  rw [frontier_ball c hr.ne'] at hx₀
  have hx₀' : ‖x₀ - c‖ = r := by rwa [mem_sphere_iff_norm] at hx₀
  -- the rigid motion
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin (d + 1)), v = r⁻¹ • (c - x₀) := ⟨_, rfl⟩
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, Real.norm_of_nonneg hr.le, norm_sub_rev, hx₀', inv_mul_cancel₀
      hr.ne']
  obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin (d + 1)), e = EuclideanSpace.single (Fin.last d) 1 :=
    ⟨_, rfl⟩
  have hen : ‖e‖ = 1 := by rw [he, PiLp.norm_single, norm_one]
  obtain ⟨R, hR⟩ : ∃ R : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)),
      R = Submodule.reflection (ℝ ∙ (v - e))ᗮ := ⟨_, rfl⟩
  have hRv : R v = e := by rw [hR]; exact Submodule.reflection_sub (hvn.trans hen.symm)
  obtain ⟨T, hT⟩ : ∃ T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)),
      T = (AffineIsometryEquiv.constVAdd ℝ _ (-c)).trans R.toAffineIsometryEquiv := ⟨_, rfl⟩
  have hTx : ∀ x, T x = R (x - c) := fun x ↦ by
    simp only [hT, AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.coe_constVAdd, LinearIsometryEquiv.coe_toAffineIsometryEquiv,
      vadd_eq_add, neg_add_eq_sub]
  -- the graph function
  obtain ⟨φ, hφs, hφpos, hφeq⟩ := exists_contDiff_pos_eq_sub (a := r ^ 2) (by positivity)
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, g = fun y' ↦ -√(φ (‖y'‖ ^ 2)) := ⟨_, rfl⟩
  have hgs : ContDiff ℝ ∞ g := by
    rw [hg]
    exact ((hφs.comp (contDiff_norm_sq ℝ)).sqrt fun y' ↦ (hφpos _).ne').neg
  refine ⟨r / 2, by positivity, T, g, hgs, ?_⟩
  -- the graph identity on the small ball
  have key : ∀ x ∈ ball x₀ (r / 2),
      (x ∈ ball c r ↔ g (EuclideanSpace.init (T x)) < T x (Fin.last d)) := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y, y = T x := ⟨_, rfl⟩
    have hy' : y = R (x - c) := by rw [hy, hTx]
    have h1 : y + r • e = R (x - x₀) := by
      rw [hy', ← hRv, ← map_smul, ← map_add, hv, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      congr 1
      abel
    have h2 : ‖y + r • e‖ < r / 2 := by
      rw [h1, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
      exact hx
    have h3 : EuclideanSpace.init (y + r • e) = EuclideanSpace.init y := by
      rw [EuclideanSpace.init_add, EuclideanSpace.init_smul, he, EuclideanSpace.init_single_last,
        smul_zero, add_zero]
    have h4 : ‖EuclideanSpace.init y‖ < r / 2 := by
      rw [← h3]
      exact (EuclideanSpace.norm_init_le _).trans_lt h2
    have h5 : (y + r • e) (Fin.last d) = y (Fin.last d) + r := by
      simp [he]
    have h6 : y (Fin.last d) + r < r / 2 := by
      rw [← h5]
      exact (le_abs_self _).trans_lt ((EuclideanSpace.abs_apply_last_le _).trans_lt h2)
    have hs : ‖EuclideanSpace.init y‖ ^ 2 ≤ r ^ 2 / 4 := by
      have : ‖EuclideanSpace.init y‖ ^ 2 < (r / 2) ^ 2 := by
        gcongr
      nlinarith
    have hφ : φ (‖EuclideanSpace.init y‖ ^ 2) = r ^ 2 - ‖EuclideanSpace.init y‖ ^ 2 :=
      hφeq _ (by positivity) hs
    have hnorm : ‖x - c‖ ^ 2 = ‖EuclideanSpace.init y‖ ^ 2 + y (Fin.last d) ^ 2 := by
      rw [← EuclideanSpace.norm_sq_eq_init_add_last, hy', LinearIsometryEquiv.norm_map]
    rw [← hy, hg]
    change x ∈ ball c r ↔ -√(φ (‖EuclideanSpace.init y‖ ^ 2)) < y (Fin.last d)
    rw [hφ, mem_ball, dist_eq_norm, neg_lt, Real.lt_sqrt (by linarith), neg_sq]
    constructor
    · intro h
      have : ‖x - c‖ ^ 2 < r ^ 2 := by
        have := norm_nonneg (x - c)
        nlinarith
      linarith
    · intro h
      nlinarith [norm_nonneg (x - c)]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hxΩ, hxB⟩
    exact ⟨hxB, (key x hxB).1 hxΩ⟩
  · rintro ⟨hxB, hgx⟩
    exact ⟨(key x hxB).2 hgx, hxB⟩

/-- Let $c \in \mathbb{R}^{d+1}$, $r > 0$, and $n \in \mathbb{N} \cup \{\infty\}$. The open ball
$B(c, r)$ is an open set of class $C^n$ in the sense of charts of §9.2 of
[brezis2011functional].

This follows from `isContDiffDomain_ball` and `IsContDiffDomain.isContDiffChartDomain`. The ball
is the standard example of a $C^1$ domain with bounded boundary, on which Corollary 9.15 gives
the interior regularity of the Dirichlet eigenfunctions in Theorem 9.31 of
[brezis2011functional]. -/
theorem isContDiffChartDomain_ball (n : ℕ∞) (c : EuclideanSpace ℝ (Fin (d + 1))) {r : ℝ}
    (hr : 0 < r) : IsContDiffChartDomain n (ball c r) :=
  (isContDiffDomain_ball c hr).isContDiffChartDomain.of_le (by exact_mod_cast le_top)

end Ball

/-! ### Remark 15: an equivalent norm on $W^{1,p}(\Omega)$ -/

section EquivalentNorm

/-- Let $A, B, G, K \in [0, \infty]$ with $A < \infty$, and let $0 < \theta \le 1$. If
$A \le B^\theta (K (A + G))^{1 - \theta}$, then $$A \le \max\{1, (2K)^{(1 - \theta)/\theta}\} \,
(B + G).$$

This is the absorption step of an Ehrling-type inequality. Either $A \le G$, or $A + G \le 2A$
and then $A^\theta \le B^\theta (2K)^{1 - \theta}$. -/
theorem ENNReal.le_max_mul_add_of_le_rpow_mul_rpow {A B G K : ℝ≥0∞} (hA : A ≠ ⊤) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (h : A ≤ B ^ θ * (K * (A + G)) ^ (1 - θ)) :
    A ≤ max 1 ((2 * K) ^ ((1 - θ) / θ)) * (B + G) := by
  rcases le_or_gt A G with hAG | hGA
  · calc A ≤ G := hAG
      _ ≤ 1 * (B + G) := by rw [one_mul]; exact le_add_self
      _ ≤ max 1 ((2 * K) ^ ((1 - θ) / θ)) * (B + G) := by gcongr; exact le_max_left _ _
  · have hA0 : A ≠ 0 := (lt_of_le_of_lt zero_le hGA).ne'
    have h2 : A + G ≤ 2 * A := by
      rw [two_mul]
      exact add_le_add le_rfl hGA.le
    have h3 : A ≤ B ^ θ * (2 * K) ^ (1 - θ) * A ^ (1 - θ) := by
      calc A ≤ B ^ θ * (K * (A + G)) ^ (1 - θ) := h
        _ ≤ B ^ θ * (K * (2 * A)) ^ (1 - θ) := by gcongr
        _ = B ^ θ * (2 * K) ^ (1 - θ) * A ^ (1 - θ) := by
            rw [show K * (2 * A) = 2 * K * A by ring,
              ENNReal.mul_rpow_of_nonneg _ _ (by linarith), mul_assoc]
    have h4 : A ^ θ ≤ B ^ θ * (2 * K) ^ (1 - θ) := by
      have hne : A ^ (1 - θ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hA).ne'
      have hnt : A ^ (1 - θ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hA
      have : A ^ θ * A ^ (1 - θ) ≤ B ^ θ * (2 * K) ^ (1 - θ) * A ^ (1 - θ) := by
        rwa [← ENNReal.rpow_add _ _ hA0 hA, add_sub_cancel, ENNReal.rpow_one]
      exact (ENNReal.mul_le_mul_iff_left hne hnt).1 this
    have h5 : A ≤ B * (2 * K) ^ ((1 - θ) / θ) := by
      calc A = (A ^ θ) ^ (1 / θ) := by
            rw [← ENNReal.rpow_mul, mul_one_div_cancel hθ0.ne', ENNReal.rpow_one]
        _ ≤ (B ^ θ * (2 * K) ^ (1 - θ)) ^ (1 / θ) := ENNReal.rpow_le_rpow h4 (by positivity)
        _ = B * (2 * K) ^ ((1 - θ) / θ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
              mul_one_div_cancel hθ0.ne', ENNReal.rpow_one, ← ENNReal.rpow_mul]
            congr 2
            ring
    calc A ≤ B * (2 * K) ^ ((1 - θ) / θ) := h5
      _ ≤ (B + G) * max 1 ((2 * K) ^ ((1 - θ) / θ)) := by gcongr <;> simp
      _ = max 1 ((2 * K) ^ ((1 - θ) / θ)) * (B + G) := mul_comm _ _

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

/-- Let $p \ge 1$. For $u \in W^{1,p}(\Omega)$, $$\|u\| \le \|u\|_{L^p(\Omega)} + n \|\nabla
u\|_p,$$ where $n$ is the number of vectors of the basis $b$.

The term $\|u\|_{L^p(\Omega)}$ is the norm of the weak derivative of order $0$,
`SobolevMultiIndex.weakDeriv u 0`. -/
theorem SobolevMultiIndex.norm_le_norm_weakDeriv_zero_add_gradNorm
    (u : SobolevMultiIndex F b 1 p Ω μ) :
    ‖u‖ ≤ ‖SobolevMultiIndex.weakDeriv u 0‖ + Fintype.card ι * SobolevMultiIndex.gradNorm u := by
  calc ‖u‖ ≤ ∑ α, ‖SobolevMultiIndex.weakDeriv u α‖ := by
        rw [← Submodule.norm_coe]
        exact PiLp.norm_le_sum_norm _
    _ = ‖SobolevMultiIndex.weakDeriv u 0‖
        + ∑ i, ‖SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)‖ :=
        MultiIndexLE.sum_univ_one _
    _ ≤ ‖SobolevMultiIndex.weakDeriv u 0‖ + ∑ _i : ι, SobolevMultiIndex.gradNorm u :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦
          SobolevMultiIndex.norm_weakDeriv_single_le_gradNorm u i)
    _ = ‖SobolevMultiIndex.weakDeriv u 0‖ + Fintype.card ι * SobolevMultiIndex.gradNorm u := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end EquivalentNorm

section Remark15

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- Let $1 \le q \le r \le \infty$. Then $1/q - 1/r \ge 0$, with $1/\infty = 0$. This is the
exponent of $|\Omega|$ in $\|f\|_q \le |\Omega|^{1/q - 1/r} \|f\|_r$.

The reciprocals are taken of `ENNReal.toReal`, so that $1/\infty$ is $1/0 = 0$ in Lean. -/
theorem ENNReal.one_div_toReal_sub_nonneg_of_le {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r) :
    0 ≤ 1 / q.toReal - 1 / r.toReal := by
  rw [sub_nonneg]
  rcases eq_or_ne r ⊤ with rfl | hr
  · simp
  · exact one_div_le_one_div_of_le (ENNReal.toReal_pos (one_pos.trans_le hq).ne'
      (ne_top_of_le_ne_top hr hqr)) (ENNReal.toReal_mono hr hqr)

/-- Let $p \ge 1$, $q \le r$ in $[0, \infty]$, and $K \in [0, \infty]$. Suppose that
$\|u\|_{L^r(\Omega)} \le K \|u\|$ for every $u \in W^{1,p}(\Omega)$. Then for every
$u \in W^{1,p}(\Omega)$ $$\|u\|_{L^q(\Omega)} \le K \, |\Omega|^{1/q - 1/r} \, \|u\|.$$ This
lowers the exponent of an embedding.

The exponent is computed with `ENNReal.toReal`, so $1/\infty = 0$. When $|\Omega| = \infty$ and
$1/q > 1/r$, the factor $|\Omega|^{1/q - 1/r}$ is $\infty$. -/
theorem SobolevEuclidean.eLpNorm_fn_le_mul_of_le
    {q r : ℝ≥0∞} (hqr : q ≤ r)
    {K : ℝ≥0∞}
    (hKu : ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖)
    (u : SobolevEuclidean N 1 p Ω) :
    eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ K * volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ^ (1 / q.toReal - 1 / r.toReal)
        * ENNReal.ofReal ‖u‖ := by
  calc eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ eLpNorm (fn u) r (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) univ
          ^ (1 / q.toReal - 1 / r.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqr
          (SobolevMultiIndex.memLp u).aestronglyMeasurable
    _ ≤ K * ENNReal.ofReal ‖u‖
        * volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ^ (1 / q.toReal - 1 / r.toReal) := by
        rw [Measure.restrict_apply_univ]
        gcongr
        exact hKu u
    _ = _ := by ring

/-- Let $p \ge 1$, $|\Omega| < \infty$, and $1 \le q \le r \le \infty$. Suppose that there is a
finite $K$ with $\|u\|_{L^r(\Omega)} \le K \|u\|$ for every $u \in W^{1,p}(\Omega)$, as
Corollary 9.14 gives. Then there is $C \ge 0$ with $$\|\nabla u\|_p + \|u\|_{L^q(\Omega)} \le C
\|u\| \qquad \text{for all } u \in W^{1,p}(\Omega).$$ This is the upper bound of Remark 15 of
[brezis2011functional].

It follows from $\|u\|_q \le |\Omega|^{1/q - 1/r} \|u\|_r$. -/
theorem SobolevEuclidean.exists_forall_gradNorm_add_eLpNorm_le_norm
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hKu : ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω,
      gradNorm u + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0∞, M = K * volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
      ^ (1 / q.toReal - 1 / r.toReal) := ⟨_, rfl⟩
  have hMt : M ≠ ⊤ := hM ▸ ENNReal.mul_ne_top hK (ENNReal.rpow_ne_top_of_nonneg
    (ENNReal.one_div_toReal_sub_nonneg_of_le hq hqr) hΩ)
  refine ⟨1 + M.toReal, by positivity, fun u ↦ ?_⟩
  have h2 : (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
      ≤ M.toReal * ‖u‖ := by
    rw [← ENNReal.toReal_ofReal (norm_nonneg u), ← ENNReal.toReal_mul, hM]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (hM ▸ hMt) ENNReal.ofReal_ne_top)
      (SobolevEuclidean.eLpNorm_fn_le_mul_of_le hqr hKu u)
  calc gradNorm u + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
      ≤ ‖u‖ + M.toReal * ‖u‖ := add_le_add (gradNorm_le_norm u) h2
    _ = (1 + M.toReal) * ‖u‖ := by ring

/-- Let $p \ge 1$, $|\Omega| < \infty$, $1 \le q \le r \le \infty$ and $p < r$. Suppose that there
is a finite $K$ with $\|u\|_{L^r(\Omega)} \le K \|u\|$ for every $u \in W^{1,p}(\Omega)$, as
Corollary 9.14 gives. Then there is $C \ge 0$ with $$\|u\| \le C \left( \|\nabla u\|_p +
\|u\|_{L^q(\Omega)} \right) \qquad \text{for all } u \in W^{1,p}(\Omega).$$ This is the lower
bound of Remark 15 of [brezis2011functional].

The name refers to a bounded set, but the statement assumes only $|\Omega| < \infty$. With
`SobolevEuclidean.exists_forall_gradNorm_add_eLpNorm_le_norm` it gives the equivalence of the
two norms, `SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le`. For $q \ge p$ the
proof uses $\|u\|_p \le |\Omega|^{1/p - 1/q} \|u\|_q$. For $q < p$ it uses the interpolation
inequality $\|u\|_p \le \|u\|_q^\theta \|u\|_r^{1 - \theta}$, the bound
$\|u\|_r \le K (\|u\|_p + N \|\nabla u\|_p)$, and the absorption step
`ENNReal.le_max_mul_add_of_le_rpow_mul_rpow`. -/
theorem SobolevEuclidean.norm_le_gradNorm_add_eLpNorm_of_isBounded
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    (hpr : p < r) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hKu : ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  -- the `L^q` norm is finite
  have hBt : ∀ u : SobolevEuclidean N 1 p Ω,
      eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≠ ⊤ := fun u ↦
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK (ENNReal.rpow_ne_top_of_nonneg
      (ENNReal.one_div_toReal_sub_nonneg_of_le hq hqr) hΩ)) ENNReal.ofReal_ne_top)
      (SobolevEuclidean.eLpNorm_fn_le_mul_of_le hqr hKu u)
  -- the norm through the function and the gradient
  have hnorm : ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤
      (eLpNorm (fn u) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        + N * gradNorm u := fun u ↦ by
    have := SobolevMultiIndex.norm_le_norm_weakDeriv_zero_add_gradNorm u
    rwa [Fintype.card_fin, Lp.norm_def] at this
  rcases le_or_gt p q with hpq | hqp
  · -- `p ≤ q`: `‖u‖_p ≤ |Ω|^{1/p − 1/q} ‖u‖_q`
    obtain ⟨M, hM⟩ : ∃ M : ℝ≥0∞, M = volume (Ω : Set (EuclideanSpace ℝ (Fin N)))
        ^ (1 / p.toReal - 1 / q.toReal) := ⟨_, rfl⟩
    have hMt : M ≠ ⊤ := hM ▸ ENNReal.rpow_ne_top_of_nonneg
      (ENNReal.one_div_toReal_sub_nonneg_of_le hp1 hpq) hΩ
    refine ⟨max M.toReal N, le_max_of_le_right (Nat.cast_nonneg N), fun u ↦ ?_⟩
    have h1 : (eLpNorm (fn u) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ M.toReal * (eLpNorm (fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
      rw [← ENNReal.toReal_mul, mul_comm]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top (hBt u) hMt) ?_
      have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq
        (SobolevMultiIndex.memLp u).aestronglyMeasurable
        (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      rwa [Measure.restrict_apply_univ, ← hM] at this
    calc ‖u‖ ≤ (eLpNorm (fn u) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
          + N * gradNorm u := hnorm u
      _ ≤ M.toReal * (eLpNorm (fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal + N * gradNorm u :=
          add_le_add h1 le_rfl
      _ ≤ max M.toReal N * (gradNorm u + (eLpNorm (fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) := by
          have h3 := gradNorm_nonneg u
          have h4 := ENNReal.toReal_nonneg (a := eLpNorm (fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
          nlinarith [le_max_left M.toReal N, le_max_right M.toReal N]
  · -- `q < p`: interpolation between `q` and `r`, and absorption
    obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_inv_eq_ofReal_mul_inv_add hq0 hqp.le hpr.le
    have hθpos : 0 < θ := by
      rcases hθ0.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, ENNReal.ofReal_zero, zero_mul, zero_add, sub_zero, ENNReal.ofReal_one,
          one_mul] at hθ
        exact hpr.ne (inv_inj.1 hθ)
    obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ≥0∞, C₀ = max 1 ((2 * (K * (N + 1))) ^ ((1 - θ) / θ)) := ⟨_, rfl⟩
    have hC₀t : C₀ ≠ ⊤ := by
      rw [hC₀]
      exact max_ne_top ENNReal.one_ne_top (ENNReal.rpow_ne_top_of_nonneg
        (div_nonneg (by linarith) hθpos.le)
        (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hK (by simp))))
    refine ⟨(C₀.toReal + 1) * (N + 1), by positivity, fun u ↦ ?_⟩
    -- the key inequality in `ℝ≥0∞`
    obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞,
      A = eLpNorm (fn u) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞,
      B = eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : ℝ≥0∞, G = ENNReal.ofReal (gradNorm u) := ⟨_, rfl⟩
    have hAt : A ≠ ⊤ := hA ▸ (SobolevMultiIndex.memLp u).eLpNorm_ne_top
    have hBt' : B ≠ ⊤ := hB ▸ hBt u
    have hGt : G ≠ ⊤ := hG ▸ ENNReal.ofReal_ne_top
    have hu : ENNReal.ofReal ‖u‖ ≤ (N + 1) * (A + G) := by
      calc ENNReal.ofReal ‖u‖ ≤ ENNReal.ofReal (A.toReal + N * gradNorm u) := by
            rw [hA]
            exact ENNReal.ofReal_le_ofReal (hnorm u)
        _ = A + N * G := by
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg
              (mul_nonneg (Nat.cast_nonneg N) (gradNorm_nonneg u)), ENNReal.ofReal_toReal hAt,
              ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast, hG]
        _ ≤ (N + 1) * (A + G) := by
            have : (N + 1 : ℝ≥0∞) * (A + G) = A + N * G + (N * A + G) := by ring
            rw [this]
            exact le_self_add
    have hinterp : A ≤ B ^ θ * ((K * (N + 1)) * (A + G)) ^ (1 - θ) := by
      calc A ≤ B ^ θ * (eLpNorm (fn u) r
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ^ (1 - θ) := by
            rw [hA, hB]
            exact eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow
              (SobolevMultiIndex.memLp u).aestronglyMeasurable hθ0 hθ1 hθ
        _ ≤ B ^ θ * (K * ((N + 1) * (A + G))) ^ (1 - θ) := by
            gcongr
            exact (hKu u).trans (mul_le_mul' le_rfl hu)
        _ = B ^ θ * ((K * (N + 1)) * (A + G)) ^ (1 - θ) := by rw [mul_assoc]
    have hkey : A ≤ C₀ * (B + G) := by
      rw [hC₀]
      exact ENNReal.le_max_mul_add_of_le_rpow_mul_rpow hAt hθpos hθ1 hinterp
    -- back to real numbers
    have hkey' : A.toReal ≤ C₀.toReal * (B.toReal + gradNorm u) := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC₀t (ENNReal.add_ne_top.2 ⟨hBt', hGt⟩))
        hkey
      rwa [ENNReal.toReal_mul, ENNReal.toReal_add hBt' hGt, hG,
        ENNReal.toReal_ofReal (gradNorm_nonneg u)] at h
    have hC₀0 : 0 ≤ C₀.toReal := ENNReal.toReal_nonneg
    have hg0 := gradNorm_nonneg u
    have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
    calc ‖u‖ ≤ A.toReal + N * gradNorm u := hA ▸ hnorm u
      _ ≤ C₀.toReal * (B.toReal + gradNorm u) + N * gradNorm u := add_le_add hkey' le_rfl
      _ ≤ (C₀.toReal + 1) * (N + 1) * (gradNorm u + B.toReal) := by
          nlinarith [mul_nonneg hC₀0 hg0, mul_nonneg hC₀0 hB0, mul_nonneg (Nat.cast_nonneg N) hg0,
            mul_nonneg (Nat.cast_nonneg N) hB0,
            mul_nonneg (mul_nonneg hC₀0 (Nat.cast_nonneg N)) hg0,
            mul_nonneg (mul_nonneg hC₀0 (Nat.cast_nonneg N)) hB0]
      _ = (C₀.toReal + 1) * (N + 1) * (gradNorm u
          + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal) := by
          rw [hB]

/-- Let $p \ge 1$, $|\Omega| < \infty$, $1 \le q \le r \le \infty$ and $p < r$. Suppose that there
is a finite $K$ with $\|u\|_{L^r(\Omega)} \le K \|u\|$ for every $u \in W^{1,p}(\Omega)$. Then
$\|\nabla u\|_p + \|u\|_{L^q(\Omega)}$ is equivalent to the norm of $W^{1,p}(\Omega)$: there are
$C, C' \ge 0$ with $$\|u\| \le C \left( \|\nabla u\|_p + \|u\|_{L^q(\Omega)} \right), \qquad
\|\nabla u\|_p + \|u\|_{L^q(\Omega)} \le C' \|u\|$$ for all $u \in W^{1,p}(\Omega)$. This is
Remark 15 of [brezis2011functional], with the embedding as a hypothesis. -/
theorem SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    (hpr : p < r) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hKu : ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ :=
  ⟨SobolevEuclidean.norm_le_gradNorm_add_eLpNorm_of_isBounded hΩ hq hqr hpr hK hKu,
    SobolevEuclidean.exists_forall_gradNorm_add_eLpNorm_le_norm hΩ hq hqr hK hKu⟩

/-- Let $p \ge 1$ and $r \in [0, \infty]$. Suppose that there is $C \ge 0$ with
$\|u\|_{L^r(\Omega)} \le C \|u\|$ for every $u \in W^{1,p}(\Omega)$. Then there is a finite
$K \in [0, \infty]$ with $\|u\|_{L^r(\Omega)} \le K \|u\|$ for every $u \in W^{1,p}(\Omega)$.

This converts the bound of Corollary 9.14, which is stated on the subspace $S = W^{1,p}(\Omega)$
with a real constant, to the form with a constant in `ℝ≥0∞` that the results of Remark 15 use. -/
theorem SobolevEuclidean.exists_forall_eLpNorm_fn_le_mul_ofReal_of_exists_forall
    {r : ℝ≥0∞} (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (⊤ : Submodule ℝ (SobolevEuclidean N 1 p Ω)),
      eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) r
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖)) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : SobolevEuclidean N 1 p Ω, eLpNorm (fn u) r
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ K * ENNReal.ofReal ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun u ↦ ?_⟩
  rw [← ENNReal.ofReal_mul hC0]
  exact hC ⟨u, Submodule.mem_top⟩

variable {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- Let $\Omega$ be a bounded extension domain for $W^{1,p}$, let $1 \le p < N$, let
$1/p^* = 1/p - 1/N$, and let $1 \le q \le p^*$. Then $\|\nabla u\|_p + \|u\|_{L^q(\Omega)}$ is
equivalent to the norm of $W^{1,p}(\Omega)$: there are $C, C' \ge 0$ with $$\|u\| \le C \left(
\|\nabla u\|_p + \|u\|_{L^q(\Omega)} \right), \qquad \|\nabla u\|_p + \|u\|_{L^q(\Omega)} \le C'
\|u\|$$ for all $u \in W^{1,p}(\Omega)$. This is Remark 15 of [brezis2011functional] for
$p < N$. -/
theorem SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_lt
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqp' : q ≤ p') :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hN0 : (0 : ℝ) < N := hp0.trans (by exact_mod_cast hpN)
  have hpp' : p < p' := by
    have h1 : (0 : ℝ) < (p' : ℝ)⁻¹ := by
      rw [hp', sub_pos]
      exact inv_strictAnti₀ hp0 (by exact_mod_cast hpN)
    rw [← NNReal.coe_lt_coe, ← inv_lt_inv₀ (inv_pos.1 h1) hp0, hp']
    exact sub_lt_self _ (by positivity)
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_mul_ofReal_of_exists_forall
    (hΩ.exists_forall_eLpNorm_fn_le_of_le_of_le hpN hp' hpp'.le le_rfl)
  exact SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le hb.measure_lt_top.ne hq hqp'
    (by exact_mod_cast hpp') hK hKu

/-- Let $N \ge 2$, let $\Omega$ be a bounded extension domain for $W^{1,N}$, and let
$1 \le q < \infty$. Then $\|\nabla u\|_N + \|u\|_{L^q(\Omega)}$ is equivalent to the norm of
$W^{1,N}(\Omega)$: there are $C, C' \ge 0$ with $$\|u\| \le C \left( \|\nabla u\|_N +
\|u\|_{L^q(\Omega)} \right), \qquad \|\nabla u\|_N + \|u\|_{L^q(\Omega)} \le C' \|u\|$$ for all
$u \in W^{1,N}(\Omega)$. This is Remark 15 of [brezis2011functional] for $p = N$. -/
theorem SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_eq_finrank
    [Fact (1 ≤ (N : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomain N N Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hN : 2 ≤ N) {q : ℝ≥0}
    (hq : 1 ≤ q) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 N Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 N Ω, gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_mul_ofReal_of_exists_forall
    (hΩ.exists_forall_eLpNorm_fn_le_of_eq_finrank hN (q := max q (N + 1)) (le_max_of_le_right
      (by exact_mod_cast Nat.le_succ N)))
  have hNlt : ((N : ℝ≥0) : ℝ≥0∞) < ((max q (N + 1) : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast lt_max_of_lt_right (by exact_mod_cast Nat.lt_succ_self N)
  exact SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le hb.measure_lt_top.ne
    (by exact_mod_cast hq) (by exact_mod_cast le_max_left q (N + 1)) hNlt hK hKu

/-- Let $\Omega$ be a bounded extension domain for $W^{1,p}$, let $N < p < \infty$, and let
$1 \le q \le \infty$. Then $\|\nabla u\|_p + \|u\|_{L^q(\Omega)}$ is equivalent to the norm of
$W^{1,p}(\Omega)$: there are $C, C' \ge 0$ with $$\|u\| \le C \left( \|\nabla u\|_p +
\|u\|_{L^q(\Omega)} \right), \qquad \|\nabla u\|_p + \|u\|_{L^q(\Omega)} \le C' \|u\|$$ for all
$u \in W^{1,p}(\Omega)$. This is Remark 15 of [brezis2011functional] for $p > N$. -/
theorem SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le_of_gt
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hp : N < p) {q : ℝ≥0∞}
    (hq : 1 ≤ q) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, ‖u‖ ≤ C * (gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω, gradNorm u
      + (eLpNorm (fn u) q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * ‖u‖ := by
  obtain ⟨K, hK, hKu⟩ := SobolevEuclidean.exists_forall_eLpNorm_fn_le_mul_ofReal_of_exists_forall
    (hΩ.exists_forall_eLpNorm_fn_top_le hp)
  exact SobolevEuclidean.exists_norm_le_gradNorm_add_eLpNorm_and_le hb.measure_lt_top.ne hq le_top
    ENNReal.coe_lt_top hK hKu

end Remark15

/-! ### Remark 20: the embeddings on $W_0^{1,p}(\Omega)$ of an arbitrary open set -/

section Zero

open SobolevMultiIndex

variable {N : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {S : Submodule ℝ (SobolevEuclidean N 1 p Ω)}

/-- Let $1 \le p \le q < \infty$ with $1/p - 1/N \le 1/q$, and suppose that $N \ge 2$ or $p > 1$.
Let $S$ be a subspace of $W^{1,p}(\Omega)$ with an extension operator. Then there is $C \ge 0$
with $\|u\|_{L^q(\Omega)} \le C \|u\|$ for all $u \in S$. This covers the $L^q$ clauses of
Corollary 9.14 of [brezis2011functional] in one statement: $q \le p^*$ for $p < N$, any
$q \ge N$ for $p = N$, and any $q \ge p$ for $p > N$.

The proof transfers the whole-space bound
`SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le`, which is Corollary 9.13 of
[brezis2011functional] for $m = 1$. -/
theorem HasSobolevExtensionOn.exists_forall_eLpNorm_fn_le_of_le (hS : HasSobolevExtensionOn S)
    (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S, eLpNorm (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ≤ ENNReal.ofReal (C * ‖u‖) := by
  obtain ⟨K, hK, hKu⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_le_of_le (N := N) hN hpq hq
  refine hS.exists_forall_eLpNorm_fn_le (K := K.toReal) fun v ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
  exact hKu v

/-- Let $1 \le p \le q < \infty$ with $1/p - 1/N \le 1/q$, and suppose that $N \ge 2$ or $p > 1$. If
$S$ is a subspace of $W^{1,p}(\Omega)$ with an extension operator, then every $u \in S$ lies in
$L^q(\Omega)$. -/
theorem HasSobolevExtensionOn.memLp_fn_of_le (hS : HasSobolevExtensionOn S) (hN : 2 ≤ N ∨ 1 < p)
    (hpq : p ≤ q) (hq : (p : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (u : S) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_le hN hpq hq
  exact memLp_iff.2 ((hC u).trans_lt ENNReal.ofReal_lt_top)

/-- Let $1 \le p \le q < \infty$ with $1/p - 1/N \le 1/q$, and suppose that $N \ge 2$ or $p > 1$. If
$S$ is a subspace of $W^{1,p}(\Omega)$ with an extension operator, then
$S \hookrightarrow L^q(\Omega)$. This is the $L^q$ clauses of Corollary 9.14 of
[brezis2011functional], in the form of Remark 20.

The embedding is the inclusion `SobolevMultiIndex.toLpₗOn`. -/
theorem HasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_le [Fact (1 ≤ (q : ℝ≥0∞))]
    (hS : HasSobolevExtensionOn S) (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume S
      (hS.memLp_fn_of_le hN hpq hq)) := by
  obtain ⟨C, -, hC⟩ := hS.exists_forall_eLpNorm_fn_le_of_le hN hpq hq
  exact isContinuousEmbedding_toLpₗOn _ hC

namespace SobolevEuclideanZero

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, let $1 \le p \le q < \infty$ with
$1/p - 1/N \le 1/q$, and suppose that $N \ge 2$ or $p > 1$. Then every $u \in W_0^{1,p}(\Omega)$
lies in $L^q(\Omega)$. This is Remark 20 of [brezis2011functional] for the $L^q$ clauses.

The proof uses the extension by zero, `SobolevEuclideanZero.hasSobolevExtensionOn`. -/
theorem memLp_fn_of_le (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (u : SobolevEuclideanZero N 1 p Ω) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hasSobolevExtensionOn.memLp_fn_of_le hN hpq hq u

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, let $1 \le p \le q < \infty$ with
$1/p - 1/N \le 1/q$, and suppose that $N \ge 2$ or $p > 1$. Then $$W_0^{1,p}(\Omega)
\hookrightarrow L^q(\Omega).$$ The admissible $q$ are $q \le p^*$ for $p < N$, any $q \ge N$ for
$p = N \ge 2$, and any $q \ge p$ for $p > N$. This is Remark 20 of [brezis2011functional]: "the
conclusion of Corollary 9.14 is true for $W_0^{1,p}(\Omega)$ with an arbitrary open set
$\Omega$". No regularity of $\Omega$ is needed.

The embedding is the inclusion `SobolevMultiIndex.toLpₗOn` of the subspace
`SobolevEuclideanZero N 1 p Ω`. The three cases separately are
`SobolevEuclideanZero.isContinuousEmbedding_toLp_of_lt`,
`SobolevEuclideanZero.isContinuousEmbedding_toLp_of_eq`, and, into $L^\infty(\Omega)$ with the
continuous Hölder representative, `SobolevEuclideanZero.isContinuousEmbedding_toLp_top_of_lt`
and `SobolevEuclideanZero.exists_forall_continuous_holderWith_ae_eq`. Each is the corresponding
statement for `HasSobolevExtensionOn` with the extension by zero,
`SobolevEuclideanZero.hasSobolevExtensionOn`. The case $N = 1 = p$ is excluded, as in Corollary
9.13. -/
theorem isContinuousEmbedding_toLp [Fact (1 ≤ (q : ℝ≥0∞))] (hN : 2 ≤ N ∨ 1 < p) (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclideanZero N 1 p Ω) (memLp_fn_of_le hN hpq hq)) :=
  hasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_le hN hpq hq

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, let $1 \le p < N$, let
$1/p^* = 1/p - 1/N$, and let $p \le q \le p^*$. Then every $u \in W_0^{1,p}(\Omega)$ lies in
$L^q(\Omega)$. -/
theorem memLp_fn_of_lt {p' : ℝ≥0} (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹)
    (hpq : p ≤ q) (hqp' : q ≤ p') (u : SobolevEuclideanZero N 1 p Ω) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hasSobolevExtensionOn.memLp_fn_of_le_of_le hpN hp' hpq hqp' u

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, let $1 \le p < N$, let
$1/p^* = 1/p - 1/N$, and let $p \le q \le p^*$. Then $$W_0^{1,p}(\Omega) \hookrightarrow
L^q(\Omega).$$ This is Remark 20 of [brezis2011functional] for the first case of Corollary 9.14.

The embedding is the inclusion `SobolevMultiIndex.toLpₗOn`. -/
theorem isContinuousEmbedding_toLp_of_lt [Fact (1 ≤ (q : ℝ≥0∞))] {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclideanZero N 1 p Ω) (memLp_fn_of_lt hpN hp' hpq hqp')) :=
  hasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_le_of_le hpN hp' hpq hqp'

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, let $N \ge 2$, and let
$N \le q < \infty$. Then every $u \in W_0^{1,N}(\Omega)$ lies in $L^q(\Omega)$. -/
theorem memLp_fn_of_eq [Fact (1 ≤ (N : ℝ≥0∞))] (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q)
    (u : SobolevEuclideanZero N 1 N Ω) :
    MemLp (fn (u : SobolevEuclidean N 1 N Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hasSobolevExtensionOn.memLp_fn_of_eq_finrank hN hq u

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, let $N \ge 2$, and let
$N \le q < \infty$. Then $$W_0^{1,N}(\Omega) \hookrightarrow L^q(\Omega).$$ This is Remark 20 of
[brezis2011functional] for the second case of Corollary 9.14.

The embedding is the inclusion `SobolevMultiIndex.toLpₗOn`. -/
theorem isContinuousEmbedding_toLp_of_eq [Fact (1 ≤ (N : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hN : 2 ≤ N) (hq : (N : ℝ≥0) ≤ q) :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 N Ω volume
      (SobolevEuclideanZero N 1 N Ω) (memLp_fn_of_eq hN hq)) :=
  hasSobolevExtensionOn.isContinuousEmbedding_toLpOn_of_eq_finrank hN hq

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, and let $N < p < \infty$. Then
there is $C \ge 0$ such that every $u \in W_0^{1,p}(\Omega)$ has a representative
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ with these properties: $\tilde u$ is continuous on
$\mathbb{R}^N$, $u = \tilde u$ almost everywhere on $\Omega$, and for all
$x, y \in \mathbb{R}^N$ $$|\tilde u(x) - \tilde u(y)| \le C \|u\| \, |x - y|^{1 - N/p}, \qquad
|\tilde u(x)| \le C \|u\|.$$ So $W_0^{1,p}(\Omega) \subset C(\bar\Omega) \cap L^\infty(\Omega)$.
This is Remark 20 of [brezis2011functional] for the case $p > N$ of Corollary 9.14. -/
theorem exists_forall_continuous_holderWith_ae_eq (hp : N < p) :
    ∃ C : ℝ≥0, ∀ u : SobolevEuclideanZero N 1 p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ,
      Continuous ũ ∧
      fn (u : SobolevEuclidean N 1 p Ω) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      HolderWith (C * ‖u‖₊) (1 - (N : ℝ≥0) / p) ũ ∧ ∀ x, ‖ũ x‖ ≤ C * ‖u‖ :=
  hasSobolevExtensionOn.exists_forall_continuous_holderWith_ae_eq hp

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, and let $N < p < \infty$. Then
every $u \in W_0^{1,p}(\Omega)$ lies in $L^\infty(\Omega)$. -/
theorem memLp_fn_top_of_lt (hp : N < p) (u : SobolevEuclideanZero N 1 p Ω) :
    MemLp (fn (u : SobolevEuclidean N 1 p Ω)) ⊤
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hasSobolevExtensionOn.memLp_fn_top_of_lt hp u

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, and let $N < p < \infty$. Then
$$W_0^{1,p}(\Omega) \hookrightarrow L^\infty(\Omega).$$ This is Remark 20 of
[brezis2011functional] for the third case of Corollary 9.14.

The embedding is the inclusion `SobolevMultiIndex.toLpₗOn`. -/
theorem isContinuousEmbedding_toLp_top_of_lt (hp : N < p) :
    IsContinuousEmbedding (toLpₗOn ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
      (SobolevEuclideanZero N 1 p Ω) (memLp_fn_top_of_lt hp)) :=
  hasSobolevExtensionOn.isContinuousEmbedding_toLpOn_top_of_lt hp

end SobolevEuclideanZero

end Zero

/-! ### Functions of class $C^1(\bar\Omega)$ on a bounded open set lie in $W^{1,p}(\Omega)$ -/

section ClassicalMembership

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N))) {u : EuclideanSpace ℝ (Fin N) → ℝ}

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set, and let $u$ be of class
$C^n(\bar\Omega)$ for some $n$. Then $u \in L^p(\Omega)$ for every $p \in [0, \infty]$.

The function $u$ is bounded on $\Omega$, because it is the restriction of a function that is
continuous on the compact set $\bar\Omega$. -/
theorem ContDiffOnClosure.memLp_of_isBounded {n : WithTop ℕ∞}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ n u Ω) (p : ℝ≥0∞) :
    MemLp u p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  have hΩm := Ω.isOpen.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  obtain ⟨g, hgc, hg⟩ := hu.continuousOn_closure
  obtain ⟨C, hC⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hgc
  refine MemLp.of_bound (hu.contDiffOn.continuousOn.aestronglyMeasurable hΩm) C ?_
  filter_upwards [ae_restrict_mem hΩm] with x hx
  rw [← hg hx]
  exact hC x (subset_closure hx)

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set, let $u$ be of class
$C^n(\bar\Omega)$, and let $m \in \mathbb{N}$ with $m \le n$. Then $u \in W^{m,p}(\Omega)$ for
every $p \in [0, \infty]$.

The derivatives of $u$ of order at most $n$ extend continuously to the compact set $\bar\Omega$,
as `ContDiffOnClosure` requires. So they are bounded on $\Omega$ and lie in $L^p(\Omega)$. The
classical derivatives are the weak derivatives, by `ContDiffOn.hasWeakIteratedFDerivOn`. -/
theorem ContDiffOnClosure.memSobolevMultiIndex_of_isBounded_of_le {n : WithTop ℕ∞}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ n u Ω) (p : ℝ≥0∞) {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ n) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis u m p Ω volume := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  have hbound : ∀ k : ℕ, (k : WithTop ℕ∞) ≤ n →
      MemLp (iteratedFDeriv ℝ k u) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
    intro k hk
    obtain ⟨g, hgc, hge⟩ := hu.exists_continuousOn_closure_iteratedFDeriv hk
    obtain ⟨C, hC⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hgc
    refine MemLp.of_bound
      ((hu.contDiffOn.continuousOn_iteratedFDeriv hk).aestronglyMeasurable hΩm) C ?_
    filter_upwards [ae_restrict_mem hΩm] with x hx
    rw [← hge hx]
    exact hC x (subset_closure hx)
  refine MemSobolev.memSobolevMultiIndex ⟨hu.memLp_of_isBounded Ω hΩ p, fun k hk ↦ ?_⟩
  have hk' : (k : WithTop ℕ∞) ≤ n := (by exact_mod_cast hk : (k : WithTop ℕ∞) ≤ m).trans hm
  exact ⟨iteratedFDeriv ℝ k u, hu.contDiffOn.hasWeakIteratedFDerivOn hk', hbound k hk'⟩

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set, and let $u$ be of class
$C^1(\bar\Omega)$. Then $u \in W^{1,p}(\Omega)$ for every $p \in [0, \infty]$.

This is the case $m = n = 1$ of `ContDiffOnClosure.memSobolevMultiIndex_of_isBounded_of_le`,
whose proof shows that the classical partial derivatives of $u$ are its weak derivatives. It is
Remark 2 of Chapter 9 of [brezis2011functional] read on $\bar\Omega$, the membership step of
Step A of Example 1 in §9.5. -/
theorem ContDiffOnClosure.memSobolevMultiIndex_of_isBounded
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ 1 u Ω) (p : ℝ≥0∞) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis u 1 p Ω volume :=
  hu.memSobolevMultiIndex_of_isBounded_of_le Ω hΩ p le_rfl

end ClassicalMembership

/-! ### Remark 16: an unbounded function of $W^{1,N}(B(0, 1/2))$ -/

section Remark16

variable {N : ℕ}

/-- For every $r > 0$, $\log(1/r) \le 4 r^{-1/4}$. The logarithm grows more slowly than any power.
-/
theorem Real.neg_log_le_four_mul_rpow {r : ℝ} (hr0 : 0 < r) :
    -Real.log r ≤ 4 * r ^ (-1 / 4 : ℝ) := by
  have hs : (0 : ℝ) < r ^ (-1 / 4 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hlog : Real.log (r ^ (-1 / 4 : ℝ)) = (-1 / 4 : ℝ) * Real.log r := Real.log_rpow hr0 _
  have h1 : Real.log (r ^ (-1 / 4 : ℝ)) ≤ r ^ (-1 / 4 : ℝ) - 1 := Real.log_le_sub_one_of_pos hs
  rw [hlog] at h1
  linarith

/-- For $\alpha \in \mathbb{R}$, the **function of Remark 16** of Chapter 9 of
[brezis2011functional] is $u(x) = (-\log |x|)^\alpha = (\log(1/|x|))^\alpha$ on $\mathbb{R}^N$.

Lean's conventions $\log 0 = 0$ and $0^\alpha = 0$ for $\alpha \neq 0$ give $u(0) = 0$ for
$\alpha \neq 0$. -/
def logRpow (α : ℝ) (x : EuclideanSpace ℝ (Fin N)) : ℝ := (-Real.log ‖x‖) ^ α

/-- For all $x \in \mathbb{R}^N$, `logRpow α x` is $(\log(1/|x|))^\alpha$, the form of the function
in the source. -/
theorem logRpow_eq (α : ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    logRpow α x = Real.log (1 / ‖x‖) ^ α := by
  rw [logRpow, one_div, Real.log_inv]

/-- The **classical gradient** of $u(x) = (\log(1/|x|))^\alpha$, as a linear functional: $$h \mapsto
-\alpha \, (\log(1/|x|))^{\alpha - 1} \, \frac{\langle x, h \rangle}{|x|^2}.$$
-/
def logRpowGrad (α : ℝ) (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
  (-(α * (-Real.log ‖x‖) ^ (α - 1)) * (‖x‖ ^ 2)⁻¹) • innerSL ℝ x

/-- Let $x \in \mathbb{R}^N$ with $0 < |x| < 1$. Then `logRpow α` is differentiable at $x$, with
derivative `logRpowGrad α x`. -/
theorem hasFDerivAt_logRpow {α : ℝ} {x : EuclideanSpace ℝ (Fin N)} (hx0 : x ≠ 0)
    (hx1 : ‖x‖ < 1) : HasFDerivAt (logRpow α) (logRpowGrad α x) x := by
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg hn hx1
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin N) ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x :=
    hasFDerivAt_norm_of_ne_zero hx0
  have hneg : HasDerivAt (fun t : ℝ ↦ -Real.log t) (-‖x‖⁻¹) ‖x‖ :=
    (Real.hasDerivAt_log hn.ne').neg
  have hpow : HasDerivAt (fun s : ℝ ↦ s ^ α) (α * (-Real.log ‖x‖) ^ (α - 1)) (-Real.log ‖x‖) :=
    Real.hasDerivAt_rpow_const (Or.inl (by linarith))
  have h3 := (hpow.comp ‖x‖ hneg).comp_hasFDerivAt x h1
  have hcoef : (α * (-Real.log ‖x‖) ^ (α - 1) * -‖x‖⁻¹) • (‖x‖⁻¹ • innerSL ℝ x)
      = logRpowGrad α x := by
    rw [logRpowGrad, smul_smul]
    congr 1
    field_simp
  rw [hcoef] at h3
  exact h3

/-- Let $\alpha > 0$, and let $x \in \mathbb{R}^N$ with $0 < |x| < 1$. Then the gradient of
$u(x) = (\log(1/|x|))^\alpha$ has norm $$|\nabla u(x)| = \frac{\alpha \, (\log(1/|x|))^{\alpha -
1}}{|x|}.$$
-/
theorem norm_logRpowGrad {α : ℝ} (hα : 0 < α) {x : EuclideanSpace ℝ (Fin N)} (hx0 : x ≠ 0)
    (hx1 : ‖x‖ < 1) : ‖logRpowGrad α x‖ = α * (-Real.log ‖x‖) ^ (α - 1) / ‖x‖ := by
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
  have hlog : 0 < -Real.log ‖x‖ := by linarith [Real.log_neg hn hx1]
  have hpos : 0 < α * (-Real.log ‖x‖) ^ (α - 1) := mul_pos hα (Real.rpow_pos_of_pos hlog _)
  rw [logRpowGrad, norm_smul, Real.norm_eq_abs, innerSL_apply_norm, abs_mul, abs_neg,
    abs_of_pos hpos, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ ^ 2)]
  field_simp

/-- The function `logRpow α` is measurable. -/
theorem measurable_logRpow (α : ℝ) : Measurable (logRpow (N := N) α) :=
  (Real.measurable_log.comp measurable_norm).neg.pow_const α

/-- The gradient `logRpowGrad α` is almost everywhere strongly measurable, for every measure. -/
theorem aestronglyMeasurable_logRpowGrad (α : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin N))) :
    AEStronglyMeasurable (logRpowGrad α) μ :=
  AEStronglyMeasurable.smul
    (((measurable_const.mul ((Real.measurable_log.comp measurable_norm).neg.pow_const _)).neg.mul
      (measurable_norm.pow_const 2).inv).aestronglyMeasurable)
    (innerSL ℝ).continuous.aestronglyMeasurable

/-- Let $\alpha > 0$. For every $x \in B(0, 1/2)$, the function $u(x) = (\log(1/|x|))^\alpha$
satisfies $|u(x)| \le 4^\alpha |x|^{-\alpha/4}$. -/
theorem abs_logRpow_le {α : ℝ} (hα : 0 < α) :
    ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2),
      |logRpow α x| ≤ 4 ^ α * ‖x‖ ^ (-(α / 4)) := by
  intro x hx
  have hxb : ‖x‖ < 1 / 2 := mem_ball_zero_iff.1 hx
  rcases eq_or_ne x 0 with rfl | hx0
  · have h0 : logRpow α (0 : EuclideanSpace ℝ (Fin N)) = 0 := by
      rw [logRpow, norm_zero, Real.log_zero, neg_zero, Real.zero_rpow hα.ne']
    rw [h0, abs_zero]
    positivity
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
  have hlog : 0 < -Real.log ‖x‖ := by linarith [Real.log_neg hn (by linarith)]
  rw [logRpow, abs_of_nonneg (Real.rpow_nonneg hlog.le _)]
  calc (-Real.log ‖x‖) ^ α ≤ (4 * ‖x‖ ^ (-1 / 4 : ℝ)) ^ α :=
        Real.rpow_le_rpow hlog.le (Real.neg_log_le_four_mul_rpow hn) hα.le
    _ = 4 ^ α * ‖x‖ ^ (-(α / 4)) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hn.le _), ← Real.rpow_mul hn.le]
        ring_nf

/-- Let $N \ge 1$, $t \in \mathbb{R}$ and $s \in \mathbb{R}$ with $sN > -N$. Then $x \mapsto |x|^s$
lies in $L^N(B(0, t))$. -/
theorem memLp_norm_rpow_ball (hN : 1 ≤ N) {s : ℝ} (hs : -(N : ℝ) < s * N) (t : ℝ) :
    MemLp (fun x : EuclideanSpace ℝ (Fin N) ↦ ‖x‖ ^ s) N (volume.restrict (ball 0 t)) := by
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmeas : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin N) ↦ ‖x‖ ^ s)
      (volume.restrict (ball 0 t)) := (measurable_norm.pow_const s).aestronglyMeasurable
  refine (memLp_norm_rpow_iff hmeas hN0 (ENNReal.natCast_ne_top N)).1 ?_
  rw [ENNReal.div_self hN0 (ENNReal.natCast_ne_top N), memLp_one_iff_integrable]
  have h := integrableOn_norm_rpow_ball_zero (E := EuclideanSpace ℝ (Fin N)) (μ := volume)
    (by rw [hfr]; exact hN) (s := s * N) (by rw [hfr]; exact hs) t
  refine h.congr_fun (fun x _ ↦ ?_) measurableSet_ball
  simp only [ENNReal.toReal_natCast, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [← Real.rpow_mul (norm_nonneg _)]

/-- Let $N \ge 1$ and $0 < \alpha < 1$. Then $u(x) = (\log(1/|x|))^\alpha$ lies in $L^N(B(0, 1/2))$.
-/
theorem memLp_logRpow (hN : 1 ≤ N) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    MemLp (logRpow α) N (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2))) := by
  have hpow : MemLp (fun x : EuclideanSpace ℝ (Fin N) ↦ 4 ^ α * ‖x‖ ^ (-(α / 4))) N
      (volume.restrict (ball 0 (1 / 2))) := by
    refine (memLp_norm_rpow_ball hN (s := -(α / 4)) ?_ _).const_mul _
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : α / 4 * N < 1 * N := mul_lt_mul_of_pos_right (by linarith) (by linarith)
    linarith
  refine hpow.of_le (measurable_logRpow α).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ α * ‖x‖ ^ (-(α / 4)))]
  exact abs_logRpow_le hα x hx

/-- Let $c \neq 0$ and $0 < y < 1$. The function $t \mapsto -(\log(1/t))^c / c$ has the derivative
$(\log(1/y))^{c - 1} / y$ at $y$. So it is an antiderivative of the radial integrand of
Remark 16. -/
theorem hasDerivAt_neg_neg_log_rpow_div {c : ℝ} (hc : c ≠ 0) {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun t : ℝ ↦ -((-Real.log t) ^ c / c)) ((-Real.log y) ^ (c - 1) / y) y := by
  have hlog : 0 < -Real.log y := by linarith [Real.log_neg hy0 hy1]
  have hl : HasDerivAt (fun t : ℝ ↦ -Real.log t) (-y⁻¹) y := (Real.hasDerivAt_log hy0.ne').neg
  have hp : HasDerivAt (fun s : ℝ ↦ s ^ c) (c * (-Real.log y) ^ (c - 1)) (-Real.log y) :=
    Real.hasDerivAt_rpow_const (Or.inl hlog.ne')
  have h := ((hp.comp y hl).div_const c).neg
  refine h.congr_deriv ?_
  field_simp

/-- Let $c < 0$. The function $t \mapsto -(\log(1/t))^c / c$ is continuous on $[0, 1/2]$, with the
value $0$ at $t = 0$.

The value at $0$ is the limit, and it is also the value that Lean's conventions give:
$\log 0 = 0$ and $0^c = 0$. -/
theorem continuousOn_neg_neg_log_rpow_div {c : ℝ} (hc : c < 0) :
    ContinuousOn (fun t : ℝ ↦ -((-Real.log t) ^ c / c)) (Icc 0 (1 / 2)) := by
  intro t ht
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [← continuousWithinAt_sdiff_self]
    have hzero : -((-Real.log (0 : ℝ)) ^ c / c) = 0 := by simp [Real.zero_rpow hc.ne]
    rw [ContinuousWithinAt, hzero]
    have hlim : Tendsto (fun t : ℝ ↦ -((-Real.log t) ^ c / c)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ ↦ -Real.log t) (𝓝[>] (0 : ℝ)) atTop :=
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
      have h2 : Tendsto (fun t : ℝ ↦ (-Real.log t) ^ c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (neg_pos.2 hc)).comp h1
        simpa [Function.comp_def] using this
      simpa using (h2.div_const c).neg
    have hsub : (Icc (0 : ℝ) (1 / 2) \ {0}) ⊆ Ioi 0 := fun s hs ↦
      lt_of_le_of_ne hs.1.1 (Ne.symm hs.2)
    exact hlim.mono_left (nhdsWithin_mono 0 hsub)
  · refine ContinuousAt.continuousWithinAt ?_
    have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hlog : 0 < -Real.log t := by linarith [Real.log_neg hpos (by linarith [ht.2])]
    exact (((Real.continuousAt_log ht0).neg.rpow_const (Or.inl hlog.ne')).div_const c).neg

/-- Let $c < 0$. Then $y \mapsto (\log(1/y))^{c - 1} / y$ is integrable on $(0, 1/2)$. Equivalently,
$\int_0^{1/2} (\log(1/r))^{-\beta} \, dr/r < \infty$ for $\beta > 1$. This is the radial
integrability of Remark 16 of [brezis2011functional].

The antiderivative $-(\log(1/r))^c / c$ is continuous and monotone on $[0, 1/2]$. -/
theorem integrableOn_neg_log_rpow_div {c : ℝ} (hc : c < 0) :
    IntegrableOn (fun y : ℝ ↦ (-Real.log y) ^ (c - 1) / y) (Ioo 0 (1 / 2)) := by
  have hd : ∀ y ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt (fun t : ℝ ↦ -((-Real.log t) ^ c / c))
      ((-Real.log y) ^ (c - 1) / y) y := fun y hy ↦
    hasDerivAt_neg_neg_log_rpow_div hc.ne hy.1 (by linarith [hy.2])
  have hpos : ∀ y ∈ Ioo (0 : ℝ) (1 / 2), 0 ≤ (-Real.log y) ^ (c - 1) / y := fun y hy ↦ by
    have hlog : 0 < -Real.log y := by linarith [Real.log_neg hy.1 (by linarith [hy.2])]
    exact div_nonneg (Real.rpow_nonneg hlog.le _) hy.1.le
  exact (intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_neg_neg_log_rpow_div hc) hd
    hpos).mono_set Ioo_subset_Ioc_self

/-- Let $0 < \alpha < 1$ and $N \ge 1$. For every $x \in B(0, 1/2)$, including the origin, $$|\nabla
u(x)|^N = \alpha^N \, (\log(1/|x|))^{N(\alpha - 1)} \, |x|^{-N}.$$

Both sides vanish at the origin under Lean's conventions. -/
theorem norm_logRpowGrad_rpow_eq {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hN : 1 ≤ N) :
    ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2), ‖logRpowGrad α x‖ ^ (N : ℝ)
      = α ^ (N : ℝ) * ((-Real.log ‖x‖) ^ ((N : ℝ) * (α - 1)) * ‖x‖ ^ (-(N : ℝ))) := by
  intro x hx
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rcases eq_or_ne x 0 with rfl | hx0
  · have hne : (N : ℝ) * (α - 1) ≠ 0 := mul_ne_zero hN0 (by linarith)
    simp [logRpowGrad, Real.zero_rpow hN0, Real.zero_rpow hne, Real.zero_rpow (neg_ne_zero.2 hN0)]
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
  have hlog : 0 < -Real.log ‖x‖ := by
    linarith [Real.log_neg hn (by linarith [mem_ball_zero_iff.1 hx])]
  rw [norm_logRpowGrad hα hx0 (by linarith [mem_ball_zero_iff.1 hx]),
    Real.div_rpow (by positivity) hn.le, Real.mul_rpow hα.le (Real.rpow_nonneg hlog.le _),
    ← Real.rpow_mul hlog.le, Real.rpow_neg hn.le]
  rw [div_eq_mul_inv, mul_assoc]
  congr 3
  ring

/-- Let $N \ge 2$ and $0 < \alpha < 1 - 1/N$. Then $|\nabla u|^N$ is integrable on $B(0, 1/2)$, for
$u(x) = (\log(1/|x|))^\alpha$.

In polar coordinates the integral is a multiple of $\int_0^{1/2} r^{N-1} \alpha^N
(\log(1/r))^{N(\alpha - 1)} r^{-N} \, dr = \alpha^N \int_0^{1/2} (\log(1/r))^{-\beta} \, dr/r$
with $\beta = N(1 - \alpha) > 1$, which is finite by `integrableOn_neg_log_rpow_div`. -/
theorem integrableOn_norm_logRpowGrad_rpow (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1 - 1 / N) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin N) ↦ ‖logRpowGrad α x‖ ^ (N : ℝ))
      (ball 0 (1 / 2)) volume := by
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hα1' : α < 1 := by
    have : (0 : ℝ) < 1 / N := by positivity
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = N * (α - 1) + 1 := ⟨_, rfl⟩
  have hc0 : c < 0 := by
    have h1 : (N : ℝ) * (1 - 1 / N) = N - 1 := by field_simp
    have h2 : (N : ℝ) * (α - 1) < N * (1 - 1 / N - 1) :=
      mul_lt_mul_of_pos_left (by linarith) hNpos
    rw [hc]
    nlinarith
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun y ↦
    α ^ (N : ℝ) * ((-Real.log y) ^ ((N : ℝ) * (α - 1)) * y ^ (-(N : ℝ))) := ⟨_, rfl⟩
  have hcongr : EqOn (fun x : EuclideanSpace ℝ (Fin N) ↦ g ‖x‖)
      (fun x ↦ ‖logRpowGrad α x‖ ^ (N : ℝ)) (ball 0 (1 / 2)) := fun x hx ↦ by
    rw [hg]
    exact (norm_logRpowGrad_rpow_eq hα hα1' (by omega) x hx).symm
  have : Nontrivial (EuclideanSpace ℝ (Fin N)) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; omega)
  refine IntegrableOn.congr_fun ?_ hcongr measurableSet_ball
  refine (integrableOn_fun_norm_addHaar (μ := volume) (f := g)).2 ?_
  rw [hfr]
  refine IntegrableOn.congr_fun ((integrableOn_neg_log_rpow_div hc0).const_mul (α ^ (N : ℝ)))
    (fun y hy ↦ ?_) measurableSet_Ioo
  have hy0 : 0 < y := hy.1
  have hpow : (y : ℝ) ^ (N - 1) * (y ^ N)⁻¹ = y⁻¹ := by
    rw [pow_sub₀ y hy0.ne' (by omega : 1 ≤ N), pow_one]
    field_simp
  have key : ∀ a L : ℝ, a * (L / y) = y ^ (N - 1) * (a * (L * (y ^ N)⁻¹)) := by
    intro a L
    rw [div_eq_mul_inv, ← hpow]
    ring
  simp only [hg, smul_eq_mul]
  rw [hc, show (N : ℝ) * (α - 1) + 1 - 1 = N * (α - 1) by ring, Real.rpow_neg hy0.le]
  simp only [Real.rpow_natCast]
  exact key _ _

/-- Let $N \ge 2$ and $0 < \alpha < 1 - 1/N$. Then the gradient of $u(x) = (\log(1/|x|))^\alpha$
lies in $L^N(B(0, 1/2))$. -/
theorem memLp_logRpowGrad (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α) (hα1 : α < 1 - 1 / N) :
    MemLp (logRpowGrad α) N (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2))) := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  refine (memLp_norm_rpow_iff (aestronglyMeasurable_logRpowGrad α _) hN0
    (ENNReal.natCast_ne_top N)).1 ?_
  rw [ENNReal.div_self hN0 (ENNReal.natCast_ne_top N), memLp_one_iff_integrable]
  simp only [ENNReal.toReal_natCast]
  exact integrableOn_norm_logRpowGrad_rpow hN hα hα1

/-- The restriction of Lebesgue measure to a ball of $\mathbb{R}^N$ is a finite measure. -/
theorem isFiniteMeasure_volume_restrict_ball (c : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    IsFiniteMeasure (volume.restrict (ball c t)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩

/-- Let $N \ge 2$ and $0 < \alpha < 1 - 1/N$. The classical gradient of
$u(x) = (\log(1/|x|))^\alpha$ on $B(0, 1/2) \setminus \{0\}$ is its weak gradient on all of
$B(0, 1/2)$, the origin included.

The proof is the removable-singularity lemma `hasWeakFDerivOn_of_hasFDerivAt_compl_singleton`.
Its smallness hypothesis $\int_{B(0, \delta)} |u| = o(\delta)$ holds because
$|u(x)| \le 4^\alpha |x|^{-\alpha/4}$ and $-\alpha/4 > 1 - N$. -/
theorem hasWeakFDerivOn_logRpow (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α) (hα1 : α < 1 - 1 / N) :
    HasWeakFDerivOn (logRpow α) (logRpowGrad α)
      ⟨ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2), isOpen_ball⟩ volume := by
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hα1' : α < 1 := by
    have : (0 : ℝ) < 1 / N := by positivity
    linarith
  have hN1 : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have := isFiniteMeasure_volume_restrict_ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2)
  have : Nontrivial (EuclideanSpace ℝ (Fin N)) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; omega)
  have hu : IntegrableOn (logRpow α) (ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2)) volume :=
    (memLp_logRpow (by omega) hα hα1').integrable hN1
  have hw : IntegrableOn (logRpowGrad α) (ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2)) volume :=
    (memLp_logRpowGrad hN hα hα1).integrable hN1
  refine hasWeakFDerivOn_of_hasFDerivAt_compl_singleton (a := 0) hu.locallyIntegrableOn
    hw.locallyIntegrableOn (fun x hx hx0 ↦ hasFDerivAt_logRpow hx0
      (by linarith [mem_ball_zero_iff.1 hx])) ?_
  refine tendsto_inv_mul_setIntegral_norm_ball_zero (by rw [hfr]; omega) (C := 4 ^ α)
    (s := -(α / 4)) (R := 1 / 2) (by norm_num) (by rw [hfr]; linarith)
    (measurable_logRpow α).aestronglyMeasurable fun x hx ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_logRpow_le hα x hx

/-- Let $N \ge 2$ and $0 < \alpha < 1 - 1/N$. Then the function $u(x) = (\log(1/|x|))^\alpha$ lies
in $W^{1,N}(\Omega)$ for $\Omega = B(0, 1/2) \subseteq \mathbb{R}^N$. This is Remark 16 of
Chapter 9 of [brezis2011functional], the limiting case $p = N$, membership.

The space is read through the membership predicate `MemSobolevMultiIndex` for the standard
basis. The gradient $-\alpha (\log(1/|x|))^{\alpha - 1} x / |x|^2$ is the weak gradient on all
of $\Omega$, by `hasWeakFDerivOn_logRpow`. The function $|\nabla u|^N = \alpha^N
(\log(1/|x|))^{N(\alpha - 1)} |x|^{-N}$ is integrable near the origin because
$N(1 - \alpha) > 1$, by `integrableOn_norm_logRpowGrad_rpow`. The function $u$ lies in $L^N$
because the logarithm grows more slowly than any power, by `memLp_logRpow`. The function is not
essentially bounded, by `eLpNorm_logRpow_top`. -/
theorem memSobolevMultiIndex_logRpow (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α) (hα1 : α < 1 - 1 / N) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (fun x : EuclideanSpace ℝ (Fin N) ↦ Real.log (1 / ‖x‖) ^ α) 1 N
      ⟨ball 0 (1 / 2), isOpen_ball⟩ volume := by
  have hα1' : α < 1 := by
    have : (0 : ℝ) < 1 / N := by positivity
    linarith
  have e : (fun x : EuclideanSpace ℝ (Fin N) ↦ Real.log (1 / ‖x‖) ^ α) = logRpow α :=
    funext fun x ↦ (logRpow_eq α x).symm
  rw [e]
  exact ((hasWeakFDerivOn_logRpow hN hα hα1).memSobolev (memLp_logRpow (by omega) hα hα1')
    (memLp_logRpowGrad hN hα hα1)).memSobolevMultiIndex

/-- Let $N \ge 1$ and $\alpha > 0$. Then $u(x) = (\log(1/|x|))^\alpha$ is not essentially bounded on
$B(0, 1/2) \subseteq \mathbb{R}^N$: $\|u\|_{L^\infty(B(0, 1/2))} = \infty$. This is Remark 16 of
Chapter 9 of [brezis2011functional], unboundedness.

The function exceeds every constant on a small ball away from the origin, and such a ball has
positive measure. Since $u \in W^{1,N}(\Omega)$ for $\alpha < 1 - 1/N$ by
`memSobolevMultiIndex_logRpow`, the inclusion $W^{1,p}(\Omega) \subset L^\infty(\Omega)$ of
Corollary 9.14 fails for $p = N$. -/
theorem eLpNorm_logRpow_top (hN : 1 ≤ N) {α : ℝ} (hα : 0 < α) :
    eLpNorm (fun x : EuclideanSpace ℝ (Fin N) ↦ Real.log (1 / ‖x‖) ^ α) ⊤
      (volume.restrict (ball 0 (1 / 2))) = ⊤ := by
  have e : (fun x : EuclideanSpace ℝ (Fin N) ↦ Real.log (1 / ‖x‖) ^ α) = logRpow α :=
    funext fun x ↦ (logRpow_eq α x).symm
  rw [e]
  refine top_unique (le_trans ?_ eLpNormEssSup_le_eLpNorm_top)
  by_contra hlt
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞,
    K = eLpNormEssSup (logRpow α) (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2))) :=
    ⟨_, rfl⟩
  rw [← hK] at hlt
  have hKt : K ≠ ⊤ := fun h ↦ hlt (h ▸ le_rfl)
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin N))),
      x ∈ ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2) → ‖logRpow α x‖ₑ ≤ K := by
    rw [hK]
    exact (ae_restrict_iff' measurableSet_ball).1 ae_le_eLpNormEssSup
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = K.toReal := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ ENNReal.toReal_nonneg
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (1 / 2) (Real.exp (-((M + 1) ^ α⁻¹))) := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ lt_min (by norm_num) (Real.exp_pos _)
  have hr2 : r ≤ 1 / 2 := hr ▸ min_le_left _ _
  have hre : r ≤ Real.exp (-((M + 1) ^ α⁻¹)) := hr ▸ min_le_right _ _
  obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℝ (Fin N), ‖c‖ = r / 2 :=
    ⟨(r / 2) • EuclideanSpace.single (⟨0, by omega⟩ : Fin N) (1 : ℝ), by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      simp⟩
  have hbig : ∀ x ∈ ball c (r / 4), x ∈ ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2) ∧
      M < logRpow α x := by
    intro x hx
    have hxc : ‖x - c‖ < r / 4 := by rwa [mem_ball, dist_eq_norm] at hx
    have h1 := norm_sub_norm_le x c
    have h2 := norm_sub_norm_le c x
    rw [norm_sub_rev] at h2
    have hxr : ‖x‖ < r := by linarith
    have hx0 : 0 < ‖x‖ := by linarith
    have hlogx : Real.log ‖x‖ < -((M + 1) ^ α⁻¹) := by
      calc Real.log ‖x‖ < Real.log r := Real.log_lt_log hx0 hxr
        _ ≤ Real.log (Real.exp (-((M + 1) ^ α⁻¹))) := Real.log_le_log hr0 hre
        _ = -((M + 1) ^ α⁻¹) := Real.log_exp _
    have hpos : 0 ≤ (M + 1) ^ α⁻¹ := Real.rpow_nonneg (by linarith) _
    refine ⟨mem_ball_zero_iff.2 (by linarith), ?_⟩
    rw [logRpow]
    calc M < M + 1 := by linarith
      _ = ((M + 1) ^ α⁻¹) ^ α := (Real.rpow_inv_rpow (by linarith) hα.ne').symm
      _ < (-Real.log ‖x‖) ^ α := Real.rpow_lt_rpow hpos (by linarith) hα
  have hsub : ball c (r / 4) ⊆ {x | ¬ (x ∈ ball (0 : EuclideanSpace ℝ (Fin N)) (1 / 2) →
      ‖logRpow α x‖ₑ ≤ K)} := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hbig x hx
    simp only [mem_ofPred_eq, not_imp, not_le]
    refine ⟨hx1, ?_⟩
    rw [Real.enorm_eq_ofReal (by linarith), ← ENNReal.ofReal_toReal hKt, ← hM]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hx2
  have h0 : volume (ball c (r / 4)) = 0 := measure_mono_null hsub hae
  exact (measure_ball_pos volume c (by positivity)).ne' h0

end Remark16
