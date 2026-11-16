/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.Analysis.Sobolev.Operators
import Numlib.Analysis.Sobolev.Interval.Embedding

/-!
# Sobolev spaces of higher order on an open subset of the line

This module studies the spaces $W^{m,p}(I)$ of [brezis2011functional], §8.2, paragraph "The Sobolev
spaces $W^{m,p}$", for an open set $I \subseteq \mathbb{R}$ and every $1 \le p \le \infty$. For
$u \in W^{m,p}(I)$, write $D^j u \in L^p(I)$ for its weak derivative of order $j \le m$, and
$\|\cdot\|_p$ for the norm of $L^p(I)$. The module proves the characterization of $W^{m,p}(I)$ by
$m$ weak derivatives, the continuous and, for $p > 1$, compact injection
$W^{m+1,p}(a, b) \subseteq C^m[a, b]$, the inclusion $C^m[a, b] \subseteq W^{m,p}(a, b)$ with its
density for $p < \infty$ and its failure of surjectivity, the interpolation inequality
$$\|D^j u\|_p \le \varepsilon \|D^m u\|_p + C \|u\|_p \qquad (0 < j < m,\ \varepsilon > 0),$$
and the Leibniz formula for the product with a smooth function.

The space $W^{m,p}(I)$, its inductive description (`memSobolevIntervalLp_succ_iff`), its norm and
the inner product of $H^m(I)$ are in `Numlib.Analysis.Sobolev.Interval.Basic`. The space $C^m[a, b]$
is `ContDiffMapIcc` of `Numlib.Analysis.Calculus.ContDiffMapIcc`, with the norm
$\sum_{j \le m} \|u^{(j)}\|_\infty$.

## Main definitions

* `SobolevIntervalLp.derivOne`: the pair $(D^j u, D^{j+1} u)$ of $u \in W^{m+1,p}(I)$ as an element
  of $W^{1,p}(I)$.
* `SobolevIntervalLp.toContDiffMapIcc`: the embedding $W^{m+1,p}(a, b) \to C^m[a, b]$ that sends $u$
  to the continuous representatives of $u, u', \dots, u^{(m)}$.
* `ContDiffMapIcc.toSobolevIntervalLp`: the inclusion $C^k[a, b] \to W^{k,p}(a, b)$.
* `SobolevIntervalLp.shift`: the map $u \mapsto Du$ from $W^{m+1,p}(I)$ to $W^{m,p}(I)$.
* `SobolevIntervalLp.sobolevPrimitive`: the primitive $x \mapsto \int_{(a+b)/2}^x u$ of
  $u \in W^{m,p}(a, b)$, a right inverse of the shift.

## Main results

* `SobolevIntervalLp.memSobolevIntervalLp_iff_forall_integral`: $u \in W^{m,p}(I)$ if and only if
  $u \in L^p(I)$ and for every $1 \le j \le m$ there is $g_j \in L^p(I)$ with $\int_I u
  \varphi^{(j)} = (-1)^j \int_I g_j \varphi$ for every test function $\varphi$.
* `SobolevIntervalLp.toContDiffMapIcc_injective`,
  `SobolevIntervalLp.isCompactOperator_toContDiffMapIcc`: the embedding
  $W^{m+1,p}(a, b) \to C^m[a, b]$ is injective, and compact for $1 < p \le \infty$.
* `ContDiffMapIcc.norm_toSobolevIntervalLp_le`, `ContDiffMapIcc.toSobolevIntervalLp_injective`: the
  inclusion $C^k[a, b] \to W^{k,p}(a, b)$ is injective and has norm at most $(b - a)^{1/p}$.
* `ContDiffMapIcc.exists_not_mem_range_toSobolevIntervalLp`,
  `ContDiffMapIcc.not_surjective_toSobolevIntervalLp`: the inclusion $C^m[a, b] \to W^{m,p}(a, b)$
  is not surjective, for every $m$.
* `ContDiffMapIcc.denseRange_toSobolevIntervalLp`: $C^k[a, b]$ is dense in $W^{k,p}(a, b)$ for
  $1 \le p < \infty$.
* `SobolevIntervalLp.eLpNorm_integral_le`: the elementary **Poincaré inequality** $\|x \mapsto
  \int_a^x w\|_{L^p(a,b)} \le (b - a) p^{-1/p} \|w\|_{L^p(a,b)}$.
* `SobolevIntervalLp.eLpNorm_deriv_le_mul_add`: the **interpolation inequality** on every open
  interval and for every $1 \le p \le \infty$.
* `SobolevIntervalLp.exists_norm_le_mul_norm_deriv_add`: $\|u\|_p + \|D^m u\|_p$ is a norm
  equivalent to the norm of $W^{m,p}(I)$.
* `hasWeakIteratedDerivOn_sum_choose_mul`, `SobolevIntervalLp.exists_contDiff_mul`: the Leibniz
  formula $D^j(g u) = \sum_{i \le j} \binom{j}{i} g^{(j-i)} D^i u$, and multiplication by a smooth
  function with bounded derivatives preserves $W^{m,p}(I)$.

## Proof outline

The density of $C^k[a, b]$ is proved by induction on $k$. One approximates the shifted element $Du$
and takes an antiderivative, and the elementary Poincaré inequality controls the function component.
The non-surjectivity is proved by induction on $m$ through the primitive
`SobolevIntervalLp.sobolevPrimitive`, starting from $x \mapsto |x - (a + b)/2|$ in $W^{1,p}(a, b)$.
The interpolation inequality comes from an estimate at order two: a Taylor expansion over windows of
length $h$ and Young's inequality for convolutions give $\|v'\|_p \le 2h \|v''\|_p + (3/h) \|v\|_p$,
without a covering argument. An induction on the order then reaches all intermediate derivatives.

## Implementation notes

* The case $p = 2$ of the bounded theory, $H^m(a, b)$ in `Numlib.Analysis.Sobolev.Interval`
  (`ContDiffMapIcc.derivLp`, `ContDiffMapIcc.toSobolevInterval`), is the case $p = 2$ of the
  definitions here.
* The index $j$ of a derivative is an element of `Fin (m + 1)`. For $u$ in the type
  `SobolevIntervalLp (m + 1) p I`, the space is $W^{m+1,p}(I)$, and its image in
  `ContDiffMapIcc hab m` lies in $C^m[a, b]$.
* The function $u^{(j)}$ of an element of $C^k[a, b]$ is read on $\mathbb{R}$ through
  `ContinuousMap.IccExtend`, which is constant outside $[a, b]$.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Interval Topology

noncomputable section

namespace SobolevIntervalLp

variable {m : ℕ} {p : ℝ≥0∞} {I : Opens ℝ}

/-! ### The characterization by `m` weak derivatives -/

/-- **Characterization of $W^{m,p}(I)$ by $m$ weak derivatives.** Let $1 \le p \le \infty$, let
$I \subseteq \mathbb{R}$ be open, and let $u \colon \mathbb{R} \to \mathbb{R}$. Then
$u \in W^{m,p}(I)$ if and only if $u \in L^p(I)$ and for every $1 \le j \le m$ there is
$g_j \in L^p(I)$ with
$$\int_I u \, \varphi^{(j)} = (-1)^j \int_I g_j \, \varphi$$
for every test function $\varphi$ on $I$. This is the equivalence that [brezis2011functional],
§8.2, paragraph "The Sobolev spaces $W^{m,p}$", calls easily shown.

The functions $g_j$ are the weak derivatives `SobolevIntervalLp.deriv u j`. By
`SobolevIntervalLp.hasWeakDerivOn_deriv_succ`, $g_{j+1}$ is the weak derivative of $g_j$. -/
theorem memSobolevIntervalLp_iff_forall_integral [Fact (1 ≤ p)] {u : ℝ → ℝ} :
    MemSobolevIntervalLp u m p I ↔ MemLp u p (volume.restrict I) ∧ ∀ j ∈ Icc 1 m,
      ∃ g : ℝ → ℝ, MemLp g p (volume.restrict I) ∧ ∀ φ : 𝓓(I, ℝ),
        ∫ x in (I : Set ℝ), u x * iteratedDeriv j φ x
          = (-1) ^ j * ∫ x in (I : Set ℝ), g x * φ x := by
  rw [memSobolevIntervalLp_iff]
  refine and_congr_right fun hu ↦ ⟨fun h j hj ↦ ?_, fun h j hj ↦ ?_⟩
  · obtain ⟨w, hw, hwp⟩ := h j hj.2
    refine ⟨w, hwp, fun φ ↦ ?_⟩
    have := hw.integral_iteratedDeriv_mul φ
    simp only [mul_comm] at this ⊢
    exact this
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact ⟨u, HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        (hu.locallyIntegrableOn Fact.out), hu⟩
    obtain ⟨g, hg, hgφ⟩ := h j ⟨hj0, hj⟩
    refine ⟨g, hasWeakIteratedDerivOn_iff.2 ⟨hu.locallyIntegrableOn Fact.out,
      hg.locallyIntegrableOn Fact.out, fun φ ↦ ?_⟩, hg⟩
    have := hgφ φ
    simp only [mul_comm] at this ⊢
    exact this

/-! ### The successive derivatives as elements of $W^{1,p}(I)$ -/

/-- For $u \in W^{m+1,p}(I)$ and $j \le m$, the element of $W^{1,p}(I)$ whose function is $D^j u$
and whose weak derivative is $D^{j+1} u$. -/
def derivOne (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) : SobolevIntervalLp 1 p I :=
  SobolevIntervalLp.mk ![deriv u j.castSucc, deriv u j.succ] fun i ↦ by
    have h0 : HasWeakIteratedDerivOn 0 (deriv u j.castSucc) (deriv u j.castSucc) I :=
      HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        (hasWeakIteratedDerivOn_deriv u j.castSucc).locallyIntegrableOn_weakDeriv
    have h1 : HasWeakIteratedDerivOn 1 (deriv u j.castSucc) (deriv u j.succ) I :=
      hasWeakDerivOn_deriv_succ u j
    fin_cases i
    · exact h0
    · exact h1

/-- The function of `SobolevIntervalLp.derivOne u j`, as an element of $L^p(I)$, is $D^j u$. -/
@[simp]
theorem deriv_derivOne_zero (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    deriv (derivOne u j) 0 = deriv u j.castSucc := rfl

/-- The weak derivative of `SobolevIntervalLp.derivOne u j` is $D^{j+1} u$. -/
@[simp]
theorem deriv_derivOne_one (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    deriv (derivOne u j) 1 = deriv u j.succ := rfl

/-- The pair $(D^j u, D^{j+1} u)$ is additive in $u$: `derivOne (u + v) j = derivOne u j + derivOne
v j`. -/
theorem derivOne_add (u v : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    derivOne (u + v) j = derivOne u j + derivOne v j :=
  ext fun i ↦ by fin_cases i <;> rfl

/-- The pair $(D^j u, D^{j+1} u)$ is homogeneous in $u$: `derivOne (r • u) j = r • derivOne u j`. -/
theorem derivOne_smul (r : ℝ) (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    derivOne (r • u) j = r • derivOne u j :=
  ext fun i ↦ by fin_cases i <;> rfl

/-- For $j = 0$, the function of `SobolevIntervalLp.derivOne u 0` is the function of $u$. Thus
`derivOne u 0` is $u$ read in $W^{1,p}(I)$. -/
theorem fn_derivOne_zero (u : SobolevIntervalLp (m + 1) p I) : fn (derivOne u 0) = fn u := rfl

variable [Fact (1 ≤ p)]

/-- Let $1 \le p \le \infty$. For $u \in W^{m+1,p}(I)$ and $j \le m$, the pair $(D^j u, D^{j+1} u)$
has norm at most $2 \|u\|$ in $W^{1,p}(I)$. -/
theorem norm_derivOne_le (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    ‖derivOne u j‖ ≤ 2 * ‖u‖ := by
  refine (norm_le_sum_norm_deriv _).trans ?_
  rw [Fin.sum_univ_two, deriv_derivOne_zero, deriv_derivOne_one, two_mul]
  exact add_le_add (norm_deriv_le u _) (norm_deriv_le u _)

/-- Let $1 \le p \le \infty$, let $I$ be an open interval, let $u \in W^{m+1,p}(I)$ and let $j < m$.
At every point $x$ of the closure $\bar I$, the continuous representative of
$(D^j u, D^{j+1} u)$ has, within $\bar I$, the derivative equal to the value at $x$ of the
continuous representative of $(D^{j+1} u, D^{j+2} u)$.

Thus the continuous representatives of the successive derivatives are the classical derivatives
of each other on $\bar I$. -/
theorem hasDerivWithinAt_rep_derivOne (hI : (I : Set ℝ).OrdConnected)
    (u : SobolevIntervalLp (m + 1) p I) (j : Fin m) {x : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) :
    HasDerivWithinAt (rep (derivOne u j.castSucc)) (rep (derivOne u j.succ) x)
      (closure (I : Set ℝ)) x := by
  refine (contDiffOn_rep_of_continuousOn_deriv hI (derivOne u j.castSucc)
    (continuousOn_rep hI (derivOne u j.succ)) ?_).2 x hx
  rw [deriv_derivOne_one, Fin.succ_castSucc, ← deriv_derivOne_zero u j.succ, deriv_zero]
  exact fn_ae_eq_rep hI _

/-! ### The embedding $W^{m+1,p}(a, b) \hookrightarrow C^m[a, b]$ -/

variable {a b : ℝ}

/-- For $1 \le p \le \infty$, $a < b$, $u \in W^{m+1,p}(a, b)$ and $j \le m$, the continuous
representative of $D^j u$ (that is, of `SobolevIntervalLp.derivOne u j`), as a continuous
function on $[a, b]$. -/
def toContDiffMapIccTuple (hab : a < b) (u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b))
    (j : Fin (m + 1)) : C(Icc a b, ℝ) :=
  ⟨fun x ↦ rep (derivOne u j) x, (continuousOn_rep_Icc hab (derivOne u j)).comp_continuous
    continuous_subtype_val fun x ↦ x.2⟩

/-- For $1 \le p \le \infty$, $a < b$, $u \in W^{m+1,p}(a, b)$ and $j < m$, the continuous
representative of $D^{j+1} u$ on $[a, b]$ is the derivative of the continuous representative of
$D^j u$, at the endpoints as well (`ContinuousMap.HasDerivIcc`). This is the condition that
defines an element of $C^m[a, b]$. -/
theorem hasDerivIcc_toContDiffMapIccTuple (hab : a < b)
    (u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b)) (j : Fin m) :
    ContinuousMap.HasDerivIcc hab.le (toContDiffMapIccTuple hab u j.castSucc)
      (toContDiffMapIccTuple hab u j.succ) := by
  intro t
  have hcl : closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) = Icc a b := closure_coe_Ioo hab
  have h := hasDerivWithinAt_rep_derivOne (ordConnected_coe_Ioo a b) u j (x := t)
    (by rw [hcl]; exact t.2)
  rw [hcl] at h
  refine h.congr (fun y hy ↦ ?_) ?_
  · rw [ContinuousMap.coe_IccExtend, IccExtend_of_mem hab.le _ hy]; rfl
  · rw [ContinuousMap.coe_IccExtend, IccExtend_val]; rfl

/-- For $1 \le p \le \infty$ and $a < b$, the linear map $W^{m+1,p}(a, b) \to C^m[a, b]$ that sends
$u$ to the tuple of the continuous representatives of $u, u', \dots, u^{(m)}$ on $[a, b]$. -/
def toContDiffMapIccₗ (hab : a < b) :
    SobolevIntervalLp (m + 1) p (Opens.Ioo a b) →ₗ[ℝ] ContDiffMapIcc hab.le m where
  toFun u := ContDiffMapIcc.mk hab.le (toContDiffMapIccTuple hab u)
    (hasDerivIcc_toContDiffMapIccTuple hab u)
  map_add' u v := ContDiffMapIcc.ext fun j ↦ ContinuousMap.ext fun x ↦ by
    change rep (derivOne (u + v) j) x = rep (derivOne u j) x + rep (derivOne v j) x
    rw [derivOne_add]
    exact rep_add_Icc hab _ _ x.2
  map_smul' r u := ContDiffMapIcc.ext fun j ↦ ContinuousMap.ext fun x ↦ by
    change rep (derivOne (r • u) j) x = r * rep (derivOne u j) x
    rw [derivOne_smul]
    exact rep_smul_Icc hab _ _ x.2

/-- The derivative of order $j$ of the image of $u$ under the linear map
`SobolevIntervalLp.toContDiffMapIccₗ` is, at every $x \in [a, b]$, the continuous representative
of $(D^j u, D^{j+1} u)$. -/
theorem deriv_toContDiffMapIccₗ (hab : a < b) (u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b))
    (j : Fin (m + 1)) (x : Icc a b) :
    (toContDiffMapIccₗ hab u).deriv j x = rep (derivOne u j) x := rfl

/-- Let $1 \le p \le \infty$ and $a < b$. For $u \in W^{m+1,p}(a, b)$, the linear map $T$ into
$C^m[a, b]$ satisfies
$$\|T u\|_{C^m} \le 2 (m + 1) C \|u\|_{W^{m+1,p}},$$
where $C$ is `SobolevIntervalLp.embeddingConst p (Opens.Ioo a b)`, the constant of the embedding
$W^{1,p}(a, b) \subseteq L^\infty(a, b)$ of Theorem 8.8 (5) of [brezis2011functional]. -/
theorem norm_toContDiffMapIccₗ_le (hab : a < b) (u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b)) :
    ‖toContDiffMapIccₗ hab u‖
      ≤ (m + 1) * (2 * embeddingConst p (Opens.Ioo a b)) * ‖u‖ := by
  rw [ContDiffMapIcc.norm_def]
  have hC := embeddingConst_pos p (Opens.Ioo a b)
  have h : ∀ j : Fin (m + 1), ‖(toContDiffMapIccₗ hab u).deriv j‖
      ≤ 2 * embeddingConst p (Opens.Ioo a b) * ‖u‖ := fun j ↦ by
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x ↦ ?_
    rw [deriv_toContDiffMapIccₗ, Real.norm_eq_abs]
    calc |rep (derivOne u j) x|
        ≤ embeddingConst p (Opens.Ioo a b) * ‖derivOne u j‖ :=
          abs_rep_le (ordConnected_coe_Ioo a b) _ (by rw [closure_coe_Ioo hab]; exact x.2)
      _ ≤ embeddingConst p (Opens.Ioo a b) * (2 * ‖u‖) :=
          mul_le_mul_of_nonneg_left (norm_derivOne_le u j) hC.le
      _ = 2 * embeddingConst p (Opens.Ioo a b) * ‖u‖ := by ring
  calc ∑ j, ‖(toContDiffMapIccₗ hab u).deriv j‖
      ≤ ∑ _j : Fin (m + 1), 2 * embeddingConst p (Opens.Ioo a b) * ‖u‖ :=
        Finset.sum_le_sum fun j _ ↦ h j
    _ = (m + 1) * (2 * embeddingConst p (Opens.Ioo a b)) * ‖u‖ := by
        simp [Finset.sum_const, mul_assoc]

/-- **The embedding $W^{m+1,p}(a, b) \hookrightarrow C^m[a, b]$.** Let $1 \le p \le \infty$ and
$a < b$. The continuous linear map $T \colon W^{m+1,p}(a, b) \to C^m[a, b]$ sends $u$ to the
tuple of the continuous representatives of $u, u', \dots, u^{(m)}$, an element of the Banach
space `ContDiffMapIcc hab.le m`. Its operator norm is at most $2 (m + 1) C$, with $C$ the
constant `SobolevIntervalLp.embeddingConst p (Opens.Ioo a b)`. This is the inclusion
$W^{m,p}(I) \subseteq C^{m-1}(\bar I)$ with continuous injection of [brezis2011functional],
§8.2, paragraph "The Sobolev spaces $W^{m,p}$", for a bounded interval $I$.

It is injective (`SobolevIntervalLp.toContDiffMapIcc_injective`) and compact for
$1 < p \le \infty$ (`SobolevIntervalLp.isCompactOperator_toContDiffMapIcc`). For $m = 0$ its
only component is `SobolevIntervalLp.toContinuousMap`. -/
def toContDiffMapIcc (hab : a < b) :
    SobolevIntervalLp (m + 1) p (Opens.Ioo a b) →L[ℝ] ContDiffMapIcc hab.le m :=
  LinearMap.mkContinuous (toContDiffMapIccₗ hab)
    ((m + 1) * (2 * embeddingConst p (Opens.Ioo a b))) (fun u ↦ norm_toContDiffMapIccₗ_le hab u)

/-- Let $1 \le p \le \infty$ and $a < b$. For $u \in W^{m+1,p}(a, b)$ and $j \le m$, the derivative
of order $j$ of the image of $u$ in $C^m[a, b]$ is, at every $x \in [a, b]$, the continuous
representative of $(D^j u, D^{j+1} u)$. -/
theorem deriv_toContDiffMapIcc (hab : a < b) (u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b))
    (j : Fin (m + 1)) (x : Icc a b) : (toContDiffMapIcc hab u).deriv j x = rep (derivOne u j) x :=
  rfl

/-- Let $1 \le p \le \infty$ and $a < b$. For $u \in W^{m+1,p}(a, b)$, the function of the image of
$u$ in $C^m[a, b]$ is, at every $x \in [a, b]$, the continuous representative of $u$ (read in
$W^{1,p}(a, b)$ as `SobolevIntervalLp.derivOne u 0`). -/
theorem toContDiffMapIcc_apply (hab : a < b) (u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b))
    (x : Icc a b) : toContDiffMapIcc hab u x = rep (derivOne u 0) x :=
  rfl

/-- Let $1 \le p \le \infty$ and $a < b$. The embedding $T \colon W^{m+1,p}(a, b) \to C^m[a, b]$ has
operator norm $\|T\| \le 2 (m + 1) C$, with $C$ the constant `SobolevIntervalLp.embeddingConst p
(Opens.Ioo a b)`. -/
theorem norm_toContDiffMapIcc_le (hab : a < b) :
    ‖(toContDiffMapIcc hab : SobolevIntervalLp (m + 1) p (Opens.Ioo a b) →L[ℝ] _)‖
      ≤ (m + 1) * (2 * embeddingConst p (Opens.Ioo a b)) :=
  LinearMap.mkContinuous_norm_le _ (by have := embeddingConst_pos p (Opens.Ioo a b); positivity) _

/-- Let $1 \le p \le \infty$ and $a < b$. The embedding $W^{m+1,p}(a, b) \to C^m[a, b]$ is
injective.

The function of the image determines the element. -/
theorem toContDiffMapIcc_injective (hab : a < b) :
    Function.Injective (toContDiffMapIcc (p := p) (m := m) hab) := by
  intro u v huv
  refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
  have h1 := fn_ae_eq_rep (ordConnected_coe_Ioo a b) (derivOne u 0)
  have h2 := fn_ae_eq_rep (ordConnected_coe_Ioo a b) (derivOne v 0)
  rw [fn_derivOne_zero] at h1 h2
  refine h1.trans (EventuallyEq.trans ?_ h2.symm)
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
  have := congrArg (fun w : ContDiffMapIcc hab.le m ↦ w.deriv 0 ⟨x, Ioo_subset_Icc_self hx⟩) huv
  simpa only [deriv_toContDiffMapIcc] using this

end SobolevIntervalLp

/-! ### The inclusion $C^k[a, b] \to W^{k,p}(a, b)$ -/

namespace ContDiffMapIcc

variable {a b : ℝ} {hab : a ≤ b} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Let $a \le b$, let $p$ be an exponent, let $u \in C^k[a, b]$ and $j \le k$. The derivative
$u^{(j)}$, extended to $\mathbb{R}$ by its values at the endpoints, lies in $L^p(a, b)$. -/
theorem memLp_IccExtend_deriv (p : ℝ≥0∞) (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    MemLp (IccExtend hab (u.deriv j)) p (volume.restrict (Ioo a b)) :=
  (ContinuousMap.IccExtend hab (u.deriv j)).continuous.continuousOn.memLp_top_restrict_Ioo
    |>.mono_exponent le_top

variable (p) in
/-- For $u \in C^k[a, b]$ and $j \le k$, the derivative $u^{(j)}$, extended to $\mathbb{R}$ by its
values at the endpoints, as an element of $L^p(a, b)$. -/
def derivLpOf (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) : Lp ℝ p (volume.restrict (Ioo a b)) :=
  (memLp_IccExtend_deriv p u j).toLp _

omit [Fact (1 ≤ p)] in
/-- The element `ContDiffMapIcc.derivLpOf p u j` of $L^p(a, b)$ agrees almost everywhere on $(a, b)$
with the extension of $u^{(j)}$ by its endpoint values. -/
theorem coeFn_derivLpOf (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    derivLpOf p u j =ᵐ[volume.restrict (Ioo a b)] IccExtend hab (u.deriv j) :=
  MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
/-- The class of $u^{(j)}$ in $L^p(a, b)$ is additive in $u \in C^k[a, b]$. -/
theorem derivLpOf_add (u v : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    derivLpOf p (u + v) j = derivLpOf p u j + derivLpOf p v j := by
  refine Lp.ext ((coeFn_derivLpOf (p := p) _ _).trans ?_)
  refine ((Lp.coeFn_add _ _).trans ((coeFn_derivLpOf (p := p) u j).add
    (coeFn_derivLpOf (p := p) v j))).symm.trans ?_
  exact Eventually.of_forall fun x ↦ rfl

omit [Fact (1 ≤ p)] in
/-- The class of $u^{(j)}$ in $L^p(a, b)$ is homogeneous in $u \in C^k[a, b]$. -/
theorem derivLpOf_smul (c : ℝ) (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    derivLpOf p (c • u) j = c • derivLpOf p u j := by
  refine Lp.ext ((coeFn_derivLpOf (p := p) _ _).trans ?_)
  refine ((Lp.coeFn_smul _ _).trans ((coeFn_derivLpOf (p := p) u j).const_smul c)).symm.trans ?_
  exact Eventually.of_forall fun x ↦ rfl

omit [Fact (1 ≤ p)] in
/-- Let $a < b$, let $u \in C^k[a, b]$ and $j \le k$. On $(a, b)$, the class of $u^{(j)}$ in
$L^p(a, b)$ is the weak derivative of order $j$ of the class of $u$. -/
theorem hasWeakIteratedDerivOn_derivLpOf (hlt : a < b) (u : ContDiffMapIcc hab k)
    (j : Fin (k + 1)) :
    HasWeakIteratedDerivOn (j : ℕ) (derivLpOf p u 0) (derivLpOf p u j) (Opens.Ioo a b) := by
  have hcd : ContDiffOn ℝ k u.extend (Ioo a b) := (u.contDiffOn hlt).mono Ioo_subset_Icc_self
  have h := hasWeakIteratedDerivOn_of_contDiffOn (I := Opens.Ioo a b) hcd (k := j)
    (by exact_mod_cast Fin.is_le j)
  refine h.congr_ae ?_ ?_
  · exact (coeFn_derivLpOf u 0).symm
  · refine EventuallyEq.trans ?_ (coeFn_derivLpOf u j).symm
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
    have hx' : x ∈ Icc a b := Ioo_subset_Icc_self hx
    have e1 := u.deriv_eq_iteratedDerivWithin hlt j.2 ⟨x, hx'⟩
    have e2 := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
      ((hcd.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by exact_mod_cast Fin.is_le j)) hx'
    rw [← e2, ← e1, IccExtend_of_mem hab _ hx']

variable (p) in
/-- For $a < b$, the inclusion $C^k[a, b] \to W^{k,p}(a, b)$ as a linear map: $u$ goes to the
element whose component of order $j$ is the class of $u^{(j)}$ in $L^p(a, b)$.

The hypothesis $a \le b$ is the one in the type `ContDiffMapIcc hab k`, and $a < b$ is needed
for the weak derivatives. -/
def toSobolevIntervalLpₗ (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    ContDiffMapIcc hab k →ₗ[ℝ] SobolevIntervalLp k p (Opens.Ioo a b) where
  toFun u := SobolevIntervalLp.mk (derivLpOf p u) (hasWeakIteratedDerivOn_derivLpOf hlt u)
  map_add' u v := SobolevIntervalLp.ext fun j ↦ by
    change derivLpOf p (u + v) j = derivLpOf p u j + derivLpOf p v j
    exact derivLpOf_add u v j
  map_smul' c u := SobolevIntervalLp.ext fun j ↦ by
    change derivLpOf p (c • u) j = c • derivLpOf p u j
    exact derivLpOf_smul c u j

omit [Fact (1 ≤ p)] in
/-- The weak derivative of order $j$ of the image of $u \in C^k[a, b]$ under the linear inclusion
`ContDiffMapIcc.toSobolevIntervalLpₗ` is the class of $u^{(j)}$ in $L^p(a, b)$. -/
@[simp]
theorem deriv_toSobolevIntervalLpₗ (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k)
    (j : Fin (k + 1)) :
    SobolevIntervalLp.deriv (toSobolevIntervalLpₗ p hab hlt k u) j = derivLpOf p u j := rfl

omit [Fact (1 ≤ p)] in
/-- For every exponent $p$, $u \in C^k[a, b]$ and $j \le k$,
$$\|u^{(j)}\|_{L^p(a, b)} \le (b - a)^{1/p} \|u^{(j)}\|_\infty,$$
where the exponent $1/p$ is read as $0$ for $p = \infty$.

The exponent is `p.toReal⁻¹`, which is $0$ for $p = \infty$, so that the factor is then $1$. -/
theorem norm_derivLpOf_le (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    ‖derivLpOf p u j‖ ≤ (b - a) ^ p.toReal⁻¹ * ‖u.deriv j‖ := by
  rw [derivLpOf, Lp.norm_toLp]
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (Ioo a b)) (p := p)
    (f := IccExtend hab (u.deriv j)) (C := ‖u.deriv j‖)
    (ContinuousMap.IccExtend hab (u.deriv j)).continuous.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ (u.deriv j).norm_coe_le_norm _)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo] at h
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
    ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) h).trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (sub_nonneg.2 hab),
    ENNReal.toReal_ofReal (norm_nonneg _)]

/-- Let $1 \le p \le \infty$ and $a < b$. The linear inclusion
$\iota \colon C^k[a, b] \to W^{k,p}(a, b)$ satisfies
$$\|\iota u\|_{W^{k,p}} \le (b - a)^{1/p} \|u\|_{C^k},$$
with $1/p = 0$ for $p = \infty$. -/
theorem norm_toSobolevIntervalLpₗ_le (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k) :
    ‖toSobolevIntervalLpₗ p hab hlt k u‖ ≤ (b - a) ^ p.toReal⁻¹ * ‖u‖ := by
  refine (SobolevIntervalLp.norm_le_sum_norm_deriv _).trans ?_
  rw [norm_def, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦ by
    rw [deriv_toSobolevIntervalLpₗ]
    exact norm_derivLpOf_le u j

variable (p) in
/-- **The inclusion $C^k[a, b] \to W^{k,p}(a, b)$.** Let $1 \le p \le \infty$ and $a < b$. The
continuous linear map $\iota$ sends $u \in C^k[a, b]$ to the element of $W^{k,p}(a, b)$ whose
components are the derivatives $u, u', \dots, u^{(k)}$, extended by their values at the
endpoints. Its operator norm is at most $(b - a)^{1/p}$
(`ContDiffMapIcc.norm_toSobolevIntervalLp_le`). This is Remark 2 of [brezis2011functional],
§8.2, at every order $k$.

It is injective (`ContDiffMapIcc.toSobolevIntervalLp_injective`). The embedding
`SobolevIntervalLp.toContDiffMapIcc` composed with $\iota$ at order $k + 1$ is the inclusion
$C^{k+1}[a, b] \to C^k[a, b]$ (`ContDiffMapIcc.deriv_toContDiffMapIcc_toSobolevIntervalLp`). -/
def toSobolevIntervalLp (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    ContDiffMapIcc hab k →L[ℝ] SobolevIntervalLp k p (Opens.Ioo a b) :=
  LinearMap.mkContinuous (toSobolevIntervalLpₗ p hab hlt k) ((b - a) ^ p.toReal⁻¹)
    (fun u ↦ norm_toSobolevIntervalLpₗ_le hab hlt u)

/-- Let $1 \le p \le \infty$ and $a < b$. The weak derivative of order $j$ of the image of
$u \in C^k[a, b]$ in $W^{k,p}(a, b)$ is the class of $u^{(j)}$ in $L^p(a, b)$. -/
@[simp]
theorem deriv_toSobolevIntervalLp (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k)
    (j : Fin (k + 1)) :
    SobolevIntervalLp.deriv (toSobolevIntervalLp p hab hlt k u) j = derivLpOf p u j := rfl

/-- Let $1 \le p \le \infty$ and $a < b$. The function of the image of $u \in C^k[a, b]$ in
$W^{k,p}(a, b)$ agrees with $u$ almost everywhere on $(a, b)$. -/
theorem fn_toSobolevIntervalLp_ae_eq (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k) :
    SobolevIntervalLp.fn (toSobolevIntervalLp p hab hlt k u) =ᵐ[volume.restrict (Ioo a b)]
      u.extend :=
  coeFn_derivLpOf u 0

/-- Let $1 \le p \le \infty$ and $a < b$. The inclusion $\iota \colon C^k[a, b] \to W^{k,p}(a, b)$
satisfies
$$\|\iota u\|_{W^{k,p}} \le (b - a)^{1/p} \|u\|_{C^k}$$
for every $u \in C^k[a, b]$, with $1/p = 0$ for $p = \infty$. -/
theorem norm_toSobolevIntervalLp_le (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k) :
    ‖toSobolevIntervalLp p hab hlt k u‖ ≤ (b - a) ^ p.toReal⁻¹ * ‖u‖ :=
  norm_toSobolevIntervalLpₗ_le hab hlt u

/-- Let $1 \le p \le \infty$ and $a < b$. The inclusion $C^k[a, b] \to W^{k,p}(a, b)$ is injective.

A continuous function that vanishes almost everywhere on $(a, b)$ vanishes on $[a, b]$. -/
theorem toSobolevIntervalLp_injective (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    Function.Injective (toSobolevIntervalLp p hab hlt k) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  have h0 : derivLpOf p u 0 = 0 := by
    rw [← deriv_toSobolevIntervalLp hab hlt u 0, hu]
    rfl
  have hae : (IccExtend hab (u.deriv 0) : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ 0 :=
    (coeFn_derivLpOf u 0).symm.trans (by rw [h0]; exact Lp.coeFn_zero _ _ _)
  have heq := eqOn_Icc_of_ae_eq hlt
    (ContinuousMap.IccExtend hab (u.deriv 0)).continuous.continuousOn continuousOn_const hae
  refine coe_injective hlt ?_
  funext t
  have := heq t.2
  simp only [ContinuousMap.coe_IccExtend, IccExtend_of_mem hab _ t.2] at this
  exact this

/-- Let $1 \le p \le \infty$ and $a < b$. For $u \in C^{k+1}[a, b]$, the derivatives of order
$j \le k$ of the image of $u$ under the inclusion into $W^{k+1,p}(a, b)$ followed by the
embedding into $C^k[a, b]$ are the derivatives $u^{(j)}$ of $u$, at every point of $[a, b]$.

Thus the composition is the inclusion $C^{k+1}[a, b] \to C^k[a, b]$ that forgets the derivative
of order $k + 1$. -/
theorem deriv_toContDiffMapIcc_toSobolevIntervalLp (hlt : a < b) (u : ContDiffMapIcc hlt.le (k + 1))
    (j : Fin (k + 1)) (x : Icc a b) :
    (SobolevIntervalLp.toContDiffMapIcc hlt (toSobolevIntervalLp p hlt.le hlt (k + 1) u)).deriv j x
      = u.deriv j.castSucc x := by
  rw [SobolevIntervalLp.deriv_toContDiffMapIcc]
  refine (SobolevIntervalLp.rep_eq_of_continuousOn (SobolevIntervalLp.ordConnected_coe_Ioo a b) _
    (g := IccExtend hlt.le (u.deriv j.castSucc))
    (ContinuousMap.IccExtend hlt.le (u.deriv j.castSucc)).continuous.continuousOn
    ?_ (by rw [SobolevIntervalLp.closure_coe_Ioo hlt]; exact x.2)).trans ?_
  · exact coeFn_derivLpOf u j.castSucc
  · exact IccExtend_val hlt.le _ x

end ContDiffMapIcc


/-! ### Compactness of $W^{m+1,p}(a, b) \hookrightarrow C^m[a, b]$ -/

namespace SobolevIntervalLp

variable {m : ℕ} {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)] {a b : ℝ}

variable (m p I) in
/-- For $1 \le p \le \infty$ and $j \le m$, the map $u \mapsto (D^j u, D^{j+1} u)$ as a continuous
linear map $W^{m+1,p}(I) \to W^{1,p}(I)$, of norm at most $2$. -/
def derivOneCLM (j : Fin (m + 1)) : SobolevIntervalLp (m + 1) p I →L[ℝ] SobolevIntervalLp 1 p I :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ derivOne u j
      map_add' := fun u v ↦ derivOne_add u v j
      map_smul' := fun r u ↦ derivOne_smul r u j } 2 fun u ↦ norm_derivOne_le u j

/-- The continuous linear map `SobolevIntervalLp.derivOneCLM m p I j` sends $u$ to
`SobolevIntervalLp.derivOne u j`. -/
@[simp]
theorem derivOneCLM_apply (j : Fin (m + 1)) (u : SobolevIntervalLp (m + 1) p I) :
    derivOneCLM m p I j u = derivOne u j := rfl

/-- Let $1 \le p \le \infty$ and $a < b$. For $u \in W^{m+1,p}(a, b)$ and $j \le m$, the component
of order $j$ of the image of $u$ in $C^m[a, b]$ is the image of $(D^j u, D^{j+1} u)$ under the
embedding $W^{1,p}(a, b) \to C[a, b]$ (`SobolevIntervalLp.toContinuousMap`). -/
theorem deriv_toContDiffMapIcc_eq (hab : a < b) (u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b))
    (j : Fin (m + 1)) : (toContDiffMapIcc hab u).deriv j = toContinuousMap hab (derivOne u j) :=
  rfl

/-- **$W^{m+1,p}(a, b) \subseteq C^m[a, b]$ with compact injection.** Let $1 < p \le \infty$ and
$a < b$. Then the embedding `SobolevIntervalLp.toContDiffMapIcc` of $W^{m+1,p}(a, b)$ into
$C^m[a, b]$ is a compact operator. This is the compact injection of [brezis2011functional],
§8.2, paragraph "The Sobolev spaces $W^{m,p}$".

Each component $u \mapsto (D^j u, D^{j+1} u) \mapsto C[a, b]$ is compact by Theorem 8.8 (6) of
[brezis2011functional]. So the image of the unit ball lies in a finite product of compact
subsets of $C[a, b]$, and its preimage in the closed subspace $C^m[a, b]$ of the product is
compact. -/
theorem isCompactOperator_toContDiffMapIcc (hab : a < b) (hp : 1 < p) :
    IsCompactOperator
      (toContDiffMapIcc hab : SobolevIntervalLp (m + 1) p (Opens.Ioo a b) →L[ℝ] _) := by
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    (toContDiffMapIcc (p := p) (m := m) hab :
      SobolevIntervalLp (m + 1) p (Opens.Ioo a b) →ₗ[ℝ] ContDiffMapIcc hab.le m) one_pos).2 ?_
  have hF : ∀ j : Fin (m + 1), IsCompactOperator
      (((toContinuousMap hab).comp (derivOneCLM m p (Opens.Ioo a b) j) :
        SobolevIntervalLp (m + 1) p (Opens.Ioo a b) →ₗ[ℝ] C(Icc a b, ℝ))) := fun j ↦
    (isCompactOperator_toContinuousMap hab hp).comp_clm _
  let K : Fin (m + 1) → Set C(Icc a b, ℝ) := fun j ↦
    closure ((((toContinuousMap hab).comp (derivOneCLM m p (Opens.Ioo a b) j) :
      SobolevIntervalLp (m + 1) p (Opens.Ioo a b) →ₗ[ℝ] C(Icc a b, ℝ))) '' Metric.closedBall 0 1)
  have hKc : ∀ j, IsCompact (K j) := fun j ↦
    (isCompactOperator_iff_isCompact_closure_image_closedBall _ one_pos).1 (hF j)
  have hTc : IsCompact
      ((PiLp.homeomorph 1 fun _ : Fin (m + 1) ↦ C(Icc a b, ℝ)) ⁻¹' Set.pi univ K) :=
    (PiLp.homeomorph 1 _).isCompact_preimage.2 (isCompact_univ_pi hKc)
  have hT'c : IsCompact (Subtype.val ⁻¹'
      ((PiLp.homeomorph 1 fun _ : Fin (m + 1) ↦ C(Icc a b, ℝ)) ⁻¹' Set.pi univ K) :
        Set (ContDiffMapIcc hab.le m)) :=
    (ContDiffMapIcc.isClosed_submodule hab.le m).isClosedEmbedding_subtypeVal.isCompact_preimage hTc
  refine hT'c.of_isClosed_subset isClosed_closure (closure_minimal ?_ hT'c.isClosed)
  rintro w ⟨u, hu, rfl⟩ j -
  exact subset_closure ⟨u, hu, rfl⟩

/-- Let $1 < p \le \infty$ and $a < b$. The embedding $W^{m+1,p}(a, b) \to C^m[a, b]$ is a compact
embedding in the sense of `IsCompactEmbedding`. -/
theorem isCompactEmbedding_toContDiffMapIcc (hab : a < b) (hp : 1 < p) :
    IsCompactEmbedding
      (toContDiffMapIcc (p := p) (m := m) hab :
        SobolevIntervalLp (m + 1) p (Opens.Ioo a b) →ₗ[ℝ] ContDiffMapIcc hab.le m) :=
  isCompactEmbedding_iff_isCompactOperator.2
    ⟨toContDiffMapIcc_injective hab, isCompactOperator_toContDiffMapIcc hab hp⟩

end SobolevIntervalLp

/-! ### The inclusion $C^1[a, b] \to W^{1,p}(a, b)$ is not surjective -/

namespace ContDiffMapIcc

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let $1 \le p \le \infty$ and $a < c < b$. Then the function $x \mapsto |x - c|$ lies in
$W^{1,p}(a, b)$. This is Example (i) of [brezis2011functional], §8.2, translated to the point
$c$.

The function is continuous and piecewise $C^1$ for the partition $a < c < b$. -/
theorem memSobolevIntervalLp_abs_sub {c : ℝ} (hac : a < c) (hcb : c < b) :
    MemSobolevIntervalLp (fun x : ℝ ↦ |x - c|) 1 p (Opens.Ioo a b) := by
  have hx : StrictMono (![a, c, b] : Fin 3 → ℝ) := by
    refine Fin.strictMono_iff_lt_succ.2 fun i ↦ ?_
    fin_cases i <;> simp [hac, hcb]
  have hder : ∀ t : ℝ, t ≠ c → _root_.deriv (fun x : ℝ ↦ |x - c|) t = if c < t then 1 else -1 := by
    intro t ht
    have h : HasDerivAt (fun x : ℝ ↦ x - c) 1 t := (hasDerivAt_id t).sub_const c
    rcases (sub_ne_zero.2 ht).lt_or_gt with hlt | hgt
    · have : HasDerivAt (fun x : ℝ ↦ |x - c|) (-1 * 1) t :=
        (hasDerivAt_abs_neg hlt).comp t (h₂ := fun x ↦ |x|) h
      rw [this.deriv, ite_eq_right (not_lt.2 (by linarith)), mul_one]
    · have : HasDerivAt (fun x : ℝ ↦ |x - c|) (1 * 1) t :=
        (hasDerivAt_abs_pos hgt).comp t (h₂ := fun x ↦ |x|) h
      rw [this.deriv, ite_eq_left (by linarith), mul_one]
  have hg' : ∀ j : Fin 2, ContDiffOn ℝ 1 (fun x : ℝ ↦ |x - c|)
      (Ioo ((![a, c, b] : Fin 3 → ℝ) j.castSucc) ((![a, c, b] : Fin 3 → ℝ) j.succ)) := by
    intro j
    have hc : ContDiff ℝ 1 fun x : ℝ ↦ x - c := (contDiff_id.sub contDiff_const)
    fin_cases j
    · exact (contDiffOn_abs fun t ht ↦ ht).comp hc.contDiffOn
        fun t ht ↦ show t - c ∈ {x | x ≠ 0} from (sub_neg.2 (show t < c from ht.2)).ne
    · exact (contDiffOn_abs fun t ht ↦ ht).comp hc.contDiffOn
        fun t ht ↦ show t - c ∈ {x | x ≠ 0} from (sub_pos.2 (show c < t from ht.1)).ne'
  have hbdd : ∃ C, ∀ j : Fin 2, ∀ t ∈ Ioo ((![a, c, b] : Fin 3 → ℝ) j.castSucc)
      ((![a, c, b] : Fin 3 → ℝ) j.succ), |_root_.deriv (fun x : ℝ ↦ |x - c|) t| ≤ C := by
    refine ⟨1, fun j t ht ↦ ?_⟩
    have ht0 : t ≠ c := by
      fin_cases j
      · exact (show t < c from ht.2).ne
      · exact (show c < t from ht.1).ne'
    rw [hder t ht0]
    split_ifs <;> simp
  exact (memSobolevIntervalLp_of_piecewise_contDiffOn (p := p) hx rfl rfl
    (continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn hg' hbdd).1

/-- Let $1 \le p \le \infty$ and $a < b$. The inclusion $C^1[a, b] \to W^{1,p}(a, b)$ is not
surjective: some $u \in W^{1,p}(a, b)$ is not in its range. This follows from Example (i) of
[brezis2011functional], §8.2.

The function $x \mapsto |x - (a + b)/2|$ lies in $W^{1,p}(a, b)$. Its continuous representative
is unique and is not differentiable at the midpoint, so no $C^1$ function represents it. In
particular, for $p < \infty$, $C^1[a, b]$ is not complete for the norm of $W^{1,p}(a, b)$,
because it is a proper dense subspace of a Banach space
(`ContDiffMapIcc.denseRange_toSobolevIntervalLp`). -/
theorem exists_not_mem_range_toSobolevIntervalLp (hlt : a < b) :
    ∃ u : SobolevIntervalLp 1 p (Opens.Ioo a b),
      u ∉ Set.range (toSobolevIntervalLp p hlt.le hlt 1) := by
  set c := (a + b) / 2 with hc
  have hac : a < c := by rw [hc]; linarith
  have hcb : c < b := by rw [hc]; linarith
  obtain ⟨u, hu⟩ := (memSobolevIntervalLp_abs_sub (p := p) hac hcb).exists_sobolevIntervalLp
  refine ⟨u, fun ⟨v, hv⟩ ↦ ?_⟩
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo a b
  -- the representative of `u` is `|x - c|` on `[a, b]` and also `v.extend`
  have h1 : EqOn (SobolevIntervalLp.rep u) (fun x ↦ |x - c|) (Icc a b) := by
    have := SobolevIntervalLp.rep_eq_of_continuousOn hI u
      (continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn hu
    rwa [SobolevIntervalLp.closure_coe_Ioo hlt] at this
  have h2 : EqOn (SobolevIntervalLp.rep u) v.extend (Icc a b) := by
    have := SobolevIntervalLp.rep_eq_of_continuousOn hI u v.extend.continuous.continuousOn
      (by rw [← hv]; exact fn_toSobolevIntervalLp_ae_eq hlt.le hlt v)
    rwa [SobolevIntervalLp.closure_coe_Ioo hlt] at this
  have hcI : c ∈ Icc a b := ⟨hac.le, hcb.le⟩
  -- `v.extend` is differentiable at `c`, hence so is `|x - c|`
  have hd : HasDerivWithinAt v.extend (v.deriv 1 ⟨c, hcI⟩) (Icc a b) c :=
    v.hasDerivWithinAt_extend ⟨c, hcI⟩
  have hd' : HasDerivWithinAt (fun x ↦ |x - c|) (v.deriv 1 ⟨c, hcI⟩) (Icc a b) c :=
    hd.congr (fun x hx ↦ (h1 hx).symm.trans (h2 hx)) ((h1 hcI).symm.trans (h2 hcI))
  have hd'' : HasDerivAt (fun x ↦ |x - c|) (v.deriv 1 ⟨c, hcI⟩) c :=
    hd'.hasDerivAt (Icc_mem_nhds hac hcb)
  have hlin : HasDerivAt (fun y : ℝ ↦ y + c) 1 0 := (hasDerivAt_id 0).add_const c
  have hd3 : HasDerivAt (fun x ↦ |x - c|) (v.deriv 1 ⟨c, hcI⟩) ((fun y : ℝ ↦ y + c) 0) := by
    simpa using hd''
  have hcomp := hd3.comp 0 hlin
  have habs : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
    have e : (fun x ↦ |x - c|) ∘ (fun y : ℝ ↦ y + c) = abs := by funext y; simp
    rw [e] at hcomp
    exact hcomp.differentiableAt
  exact not_differentiableAt_abs_zero habs

end ContDiffMapIcc


/-! ### Poincaré's inequality, elementary form -/

namespace SobolevIntervalLp

variable {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

omit [Fact (1 ≤ p)] in
/-- For $a \le b$ and every exponent $p$, the Poincaré constant $(b - a)/p^{1/p}$ is nonnegative.

The number $p^{1/p}$ is `p.toReal ^ p.toReal⁻¹`, which is $1$ for $p = \infty$. -/
theorem poincareConst_nonneg (hab : a ≤ b) : 0 ≤ (b - a) / p.toReal ^ p.toReal⁻¹ :=
  div_nonneg (sub_nonneg.2 hab) (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- Let $1 \le p \le \infty$. For $u \in W^{m,p}(a, b)$ and $j \le m$, the weak derivative $D^j u$
is integrable on $(a, b)$. -/
theorem integrableOn_deriv_Ioo (u : SobolevIntervalLp m p (Opens.Ioo a b)) (j : Fin (m + 1)) :
    IntegrableOn (deriv u j) (Ioo a b) := by
  rcases lt_or_ge a b with hab | hab
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
    have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by
      rw [closure_coe_Ioo hab]
    exact intervalIntegrable_deriv (ordConnected_coe_Ioo a b) u j (hcl (left_mem_Icc.2 hab.le))
      (hcl (right_mem_Icc.2 hab.le))
  · rw [Ioo_eq_empty (not_lt.2 hab)]
    exact integrableOn_empty

/-- For $a \le b$ and a real number $q \ge 1$,
$$\int_a^b (x - a)^{q - 1} \, dx = \frac{(b - a)^q}{q},$$
as a Lebesgue integral in $[0, \infty]$ over $(a, b)$. -/
theorem lintegral_ofReal_sub_rpow (hab : a ≤ b) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ x in Ioo a b, ENNReal.ofReal ((x - a) ^ (q - 1)) = ENNReal.ofReal ((b - a) ^ q / q) := by
  have hint : IntegrableOn (fun x ↦ (x - a) ^ (q - 1)) (Ioo a b) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
    exact ContinuousOn.rpow_const (continuousOn_id.sub continuousOn_const)
      fun x _ ↦ Or.inr (by linarith)
  rw [← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioo).2
    (Eventually.of_forall fun x hx ↦ Real.rpow_nonneg (sub_nonneg.2 hx.1.le) _))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_right (fun x ↦ x ^ (q - 1)) a, sub_self,
    integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.zero_rpow (by linarith), sub_zero]

/-- **Poincaré's inequality, elementary form.** Let $1 \le p \le \infty$, let $a \le b$, and let $w$
be integrable on $(a, b)$. Then
$$\Bigl\|x \mapsto \int_a^x w\Bigr\|_{L^p(a, b)} \le \frac{b - a}{p^{1/p}} \|w\|_{L^p(a, b)},$$
with $p^{1/p} = 1$ for $p = \infty$.

The norms are in $[0, \infty]$. By Hölder's inequality
$|\int_a^x w| \le (x - a)^{1 - 1/p} \|w\|_p$, and
$\int_a^b (x - a)^{p - 1} \, dx = (b - a)^p / p$. The consequences for $W_0^{1,p}(a, b)$,
Proposition 8.13 of [brezis2011functional], are in `Numlib.Analysis.Sobolev.Interval.Zero`. -/
theorem eLpNorm_integral_le (hab : a ≤ b) {w : ℝ → ℝ} (hw : IntegrableOn w (Ioo a b)) :
    eLpNorm (fun x ↦ ∫ t in a..x, w t) p (volume.restrict (Ioo a b))
      ≤ ENNReal.ofReal ((b - a) / p.toReal ^ p.toReal⁻¹)
        * eLpNorm w p (volume.restrict (Ioo a b)) := by
  set W := eLpNorm w p (volume.restrict (Ioo a b)) with hW
  have hmeas : AEStronglyMeasurable (fun x ↦ ∫ t in a..x, w t) (volume.restrict (Ioo a b)) := by
    refine ContinuousOn.aestronglyMeasurable (s := Ioo a b) ?_ measurableSet_Ioo
    refine (intervalIntegral.continuousOn_primitive_interval ?_).mono
      (Ioo_subset_Icc_self.trans (Icc_subset_uIcc))
    rw [uIcc_of_le hab, integrableOn_Icc_iff_integrableOn_Ioo]
    exact hw
  -- the pointwise Hölder bound
  have hpt : ∀ x ∈ Ioo a b, ‖∫ t in a..x, w t‖ₑ ≤ ENNReal.ofReal (x - a) ^ (1 - p.toReal⁻¹) * W :=
    fun x hx ↦ by
    refine (enorm_intervalIntegral_le_rpow_mul_eLpNorm (p := p) w a x).trans ?_
    rw [abs_of_nonneg (sub_nonneg.2 hx.1.le)]
    gcongr
    rw [uIoc_of_le hx.1.le]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono (Ioc_subset_Ioo_right hx.2) le_rfl)
  rcases eq_or_ne p ⊤ with rfl | hp
  · -- `p = ∞`: the bound `(b - a) ‖w‖_∞`
    rw [ENNReal.toReal_top, inv_zero, Real.rpow_zero, div_one]
    refine (eLpNorm_le_of_ae_enorm_bound hmeas (C := ENNReal.ofReal (b - a) * W)
      ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_))).trans ?_
    · refine (hpt x hx).trans ?_
      rw [ENNReal.toReal_top, inv_zero, sub_zero, ENNReal.rpow_one]
      gcongr
      exact hx.2.le
    · rw [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, smul_eq_mul, mul_one]
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    have hpr : 1 ≤ p.toReal := by
      have := ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
      rwa [ENNReal.toReal_one] at this
    have hpr0 : 0 < p.toReal := by linarith
    have hep : 0 ≤ 1 - p.toReal⁻¹ := one_sub_toReal_inv_nonneg Fact.out
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hmeas]
    have hbound : ∫⁻ x in Ioo a b, ‖∫ t in a..x, w t‖ₑ ^ p.toReal
        ≤ ENNReal.ofReal ((b - a) ^ p.toReal / p.toReal) * W ^ p.toReal := by
      calc ∫⁻ x in Ioo a b, ‖∫ t in a..x, w t‖ₑ ^ p.toReal
          ≤ ∫⁻ x in Ioo a b, ENNReal.ofReal ((x - a) ^ (p.toReal - 1)) * W ^ p.toReal := by
            refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
              (Eventually.of_forall fun x hx ↦ ?_))
            calc ‖∫ t in a..x, w t‖ₑ ^ p.toReal
                ≤ (ENNReal.ofReal (x - a) ^ (1 - p.toReal⁻¹) * W) ^ p.toReal := by
                  gcongr
                  exact hpt x hx
              _ = ENNReal.ofReal ((x - a) ^ (p.toReal - 1)) * W ^ p.toReal := by
                  rw [ENNReal.mul_rpow_of_nonneg _ _ hpr0.le, ← ENNReal.rpow_mul,
                    ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.2 hx.1.le) (by positivity)]
                  congr 3
                  field_simp
        _ = (∫⁻ x in Ioo a b, ENNReal.ofReal ((x - a) ^ (p.toReal - 1))) * W ^ p.toReal :=
            lintegral_mul_const _ (by fun_prop)
        _ = ENNReal.ofReal ((b - a) ^ p.toReal / p.toReal) * W ^ p.toReal := by
            rw [lintegral_ofReal_sub_rpow hab hpr]
    calc (∫⁻ x in Ioo a b, ‖∫ t in a..x, w t‖ₑ ^ p.toReal) ^ (1 / p.toReal)
        ≤ (ENNReal.ofReal ((b - a) ^ p.toReal / p.toReal) * W ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
      _ = ENNReal.ofReal ((b - a) / p.toReal ^ p.toReal⁻¹) * W := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hpr0.ne', ENNReal.rpow_one,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
            Real.div_rpow (by positivity) hpr0.le, ← Real.rpow_mul (sub_nonneg.2 hab),
            mul_one_div_cancel hpr0.ne', Real.rpow_one, one_div]

end SobolevIntervalLp

/-! ### The shift $W^{m+1,p}(I) \to W^{m,p}(I)$ and the density of $C^k[a, b]$ -/

namespace SobolevIntervalLp

variable {m : ℕ} {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- **The shift** $u \mapsto Du$, for $1 \le p \le \infty$: the element of $W^{m,p}(I)$ whose
components are $Du, D^2 u, \dots, D^{m+1} u$, for $u \in W^{m+1,p}(I)$. -/
noncomputable def shift (u : SobolevIntervalLp (m + 1) p I) : SobolevIntervalLp m p I :=
  mk (fun j ↦ deriv u j.succ) fun j ↦ by
    have h1 : HasWeakDerivOn (deriv u (0 : Fin (m + 1)).castSucc) (deriv u (0 : Fin (m + 1)).succ)
        I := hasWeakDerivOn_deriv_succ u 0
    have h2 : HasWeakIteratedDerivOn ((j : ℕ) + 1) (deriv u (0 : Fin (m + 1)).castSucc)
        (deriv u j.succ) I := by
      have := hasWeakIteratedDerivOn_deriv u j.succ
      rwa [Fin.val_succ] at this
    exact h1.hasWeakIteratedDerivOn_of_succ h2

omit [Fact (1 ≤ p)] in
/-- The component of order $j$ of the shift of $u$ is $D^{j+1} u$. -/
@[simp]
theorem deriv_shift (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    deriv (shift u) j = deriv u j.succ := rfl

omit [Fact (1 ≤ p)] in
/-- The shift commutes with subtraction: $\operatorname{shift}(u - v) = \operatorname{shift} u -
\operatorname{shift} v$. -/
theorem shift_sub (u v : SobolevIntervalLp (m + 1) p I) : shift (u - v) = shift u - shift v :=
  ext fun j ↦ by rw [deriv_shift, deriv_sub, deriv_sub, deriv_shift, deriv_shift]

variable {a b : ℝ}

/-- Let $1 \le p \le \infty$ and $a < b$. For $u \in W^{m,p}(a, b)$, the primitive
$x \mapsto \int_{(a+b)/2}^x u$ lies in $L^p(a, b)$.

It is continuous on $[a, b]$. The Lean statement writes the primitive as
`0 + ∫ t in (a + b) / 2..x, deriv u 0 t`. -/
theorem memLp_sobolevPrimitive (hlt : a < b) (u : SobolevIntervalLp m p (Opens.Ioo a b)) :
    MemLp (fun x ↦ 0 + ∫ t in (a + b) / 2..x, deriv u 0 t) p
      (volume.restrict (Ioo a b)) := by
  have hint : IntegrableOn (deriv u 0) (Icc a b) :=
    (integrableOn_deriv_Ioo u 0).integrableOn_Icc_of_Ioo
  have hy₀ : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hF : ContinuousOn (fun x ↦ 0 + ∫ t in (a + b) / 2..x, deriv u 0 t)
      (Icc a b) :=
    continuousOn_integral_of_intervalIntegrable hy₀
      (fun x hx y hy ↦ (hint.mono_set (uIcc_subset_Icc hx hy)).intervalIntegrable) 0
  exact hF.memLp_top_restrict_Ioo.mono_exponent le_top

/-- **The primitive** of $u \in W^{m,p}(a, b)$, for $1 \le p \le \infty$ and $a < b$: the element of
$W^{m+1,p}(a, b)$ whose components are the primitive $x \mapsto \int_{(a+b)/2}^x u$ followed by
$u, Du, \dots, D^m u$.

It is a right inverse of the shift (`SobolevIntervalLp.shift_sobolevPrimitive`). -/
def sobolevPrimitive (hlt : a < b) (u : SobolevIntervalLp m p (Opens.Ioo a b)) :
    SobolevIntervalLp (m + 1) p (Opens.Ioo a b) :=
  mk
    (Fin.cons ((memLp_sobolevPrimitive hlt u).toLp _) fun j ↦ deriv u j)
    (by
      have hy₀ : (a + b) / 2 ∈ Opens.Ioo a b := ⟨by linarith, by linarith⟩
      have hw : HasWeakDerivOn (fun x ↦ 0 + ∫ t in (a + b) / 2..x, deriv u 0 t)
          (deriv u 0) (Opens.Ioo a b) :=
        (locallyIntegrableOn_deriv u 0).hasWeakDerivOn_integral
          (ordConnected_coe_Ioo a b) hy₀ 0
      intro j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simp only [Fin.val_zero]
        exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
          ((Lp.memLp _).locallyIntegrableOn Fact.out)
      · simp only [Fin.val_succ]
        refine (hw.hasWeakIteratedDerivOn_succ
          (hasWeakIteratedDerivOn_deriv u i)).congr_ae ?_ (EventuallyEq.refl _ _)
        exact (memLp_sobolevPrimitive hlt u).coeFn_toLp.symm)

/-- Let $1 \le p \le \infty$ and $a < b$. For $u \in W^{m,p}(a, b)$, the shift of the primitive of
$u$ is $u$. -/
theorem shift_sobolevPrimitive (hlt : a < b) (u : SobolevIntervalLp m p (Opens.Ioo a b)) :
    shift (sobolevPrimitive hlt u) = u :=
  ext fun _ ↦ rfl

end SobolevIntervalLp

/-! ### The non-surjectivity of $C^m[a, b] \to W^{m,p}(a, b)$ at every order -/

namespace ContDiffMapIcc

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {m : ℕ}

/-- Let $1 \le p \le \infty$ and $a < b$. For $v \in C^{m+1}[a, b]$, the shift of the image of $v$
in $W^{m+1,p}(a, b)$ is the image of $v'$ in $W^{m,p}(a, b)$. Thus the inclusion commutes with
the two maps $u \mapsto u'$. -/
theorem shift_toSobolevIntervalLp (hlt : a < b) (v : ContDiffMapIcc hlt.le (m + 1)) :
    SobolevIntervalLp.shift (toSobolevIntervalLp p hlt.le hlt (m + 1) v)
      = toSobolevIntervalLp p hlt.le hlt m v.shift :=
  SobolevIntervalLp.ext fun j ↦ by
    rw [SobolevIntervalLp.deriv_shift, deriv_toSobolevIntervalLp,
      deriv_toSobolevIntervalLp]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 (by rw [deriv_shift])

/-- Let $1 \le p \le \infty$ and $a < b$. The inclusion $C[a, b] \to W^{0,p}(a, b)$ is not
surjective.

The step function equal to $1$ for $x > (a + b)/2$ and to $-1$ otherwise has no continuous
representative on $[a, b]$. -/
theorem not_surjective_toSobolevIntervalLp_zero (hlt : a < b) :
    ¬ Function.Surjective (toSobolevIntervalLp p hlt.le hlt 0) := by
  obtain ⟨c, hc⟩ : ∃ c, c = (a + b) / 2 := ⟨_, rfl⟩
  have hac : a < c := by rw [hc]; linarith
  have hcb : c < b := by rw [hc]; linarith
  have hsm : MemLp (fun x : ℝ ↦ if c < x then (1 : ℝ) else -1) p (volume.restrict (Ioo a b)) := by
    refine MemLp.of_bound ?_ 1 (Eventually.of_forall fun x ↦ ?_)
    · exact (Measurable.ite measurableSet_Ioi measurable_const
        measurable_const).aestronglyMeasurable
    · split_ifs <;> simp
  obtain ⟨u, hu⟩ :=
    ((memSobolevIntervalLp_zero_iff (I := Opens.Ioo a b)).2 hsm).exists_sobolevIntervalLp
  rintro hsurj
  obtain ⟨v, hv⟩ := hsurj u
  have h2 : SobolevIntervalLp.fn u =ᵐ[volume.restrict (Ioo a b)] v.extend := by
    rw [← hv]
    exact fn_toSobolevIntervalLp_ae_eq hlt.le hlt v
  have hae : (fun x : ℝ ↦ if c < x then (1 : ℝ) else -1) =ᵐ[volume.restrict (Ioo a b)]
      v.extend := hu.symm.trans h2
  have hpos : EqOn (fun _ ↦ (1 : ℝ)) v.extend (Icc c b) := by
    refine eqOn_Icc_of_ae_eq hcb continuousOn_const v.extend.continuous.continuousOn ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hac.le le_rfl) hae,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [← ht, ite_eq_left htI.1]
  have hneg : EqOn (fun _ ↦ (-1 : ℝ)) v.extend (Icc a c) := by
    refine eqOn_Icc_of_ae_eq hac continuousOn_const v.extend.continuous.continuousOn ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hcb.le) hae,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [← ht, ite_eq_right (not_lt.2 htI.2.le)]
  have h1 := hpos (left_mem_Icc.2 hcb.le)
  have h2 := hneg (right_mem_Icc.2 hac.le)
  simp only at h1 h2
  linarith

/-- Let $1 \le p \le \infty$, $a < b$ and $m \in \mathbb{N}$. The inclusion
$C^m[a, b] \to W^{m,p}(a, b)$ is not surjective.

The proof is by induction on $m$. The primitive `SobolevIntervalLp.sobolevPrimitive` lifts an
element of $W^{m,p}(a, b)$ outside the range of $C^m[a, b]$ to an element of $W^{m+1,p}(a, b)$
outside the range of $C^{m+1}[a, b]$. -/
theorem not_surjective_toSobolevIntervalLp (hlt : a < b) (m : ℕ) :
    ¬ Function.Surjective (toSobolevIntervalLp p hlt.le hlt m) := by
  induction m with
  | zero => exact not_surjective_toSobolevIntervalLp_zero hlt
  | succ m ih =>
    intro hsurj
    refine ih fun u ↦ ?_
    obtain ⟨v, hv⟩ := hsurj (SobolevIntervalLp.sobolevPrimitive hlt u)
    exact ⟨v.shift, by
      rw [← shift_toSobolevIntervalLp, hv, SobolevIntervalLp.shift_sobolevPrimitive]⟩

end ContDiffMapIcc

namespace ContDiffMapIcc

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **$C^k[a, b]$ is dense in $W^{k,p}(a, b)$.** Let $1 \le p < \infty$ and $a < b$. Then the
inclusion $C^k[a, b] \to W^{k,p}(a, b)$ (`ContDiffMapIcc.toSobolevIntervalLp`) has dense range.
This is the statement after Theorem 8.7 of [brezis2011functional], §8.2, for $W^{m,p}$.

The proof is by induction on $k$. For $k = 0$, the test functions are dense in $L^p(a, b)$. For
$k + 1$, approximate the shifted element $Du \in W^{k,p}(a, b)$ by $w \in C^k[a, b]$ and take
the antiderivative $v = \tilde u(a) + \int_a^x w$ (`ContDiffMapIcc.cons`). Poincaré's inequality
`SobolevIntervalLp.eLpNorm_integral_le` controls the function component of $v - u$, and
$\|w - Du\|$ controls the others. -/
theorem denseRange_toSobolevIntervalLp (hab : a ≤ b) (hlt : a < b) (hp : p ≠ ⊤) (k : ℕ) :
    DenseRange (toSobolevIntervalLp p hab hlt k) := by
  rw [Metric.denseRange_iff]
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo a b
  have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by
    rw [SobolevIntervalLp.closure_coe_Ioo hlt]
  induction k with
  | zero =>
    intro u ε hε
    obtain ⟨g, -, hg, -, hgu⟩ := (SobolevIntervalLp.memLp_deriv u 0).exists_contDiff_tsupport_subset
      (Opens.Ioo a b).isOpen Fact.out hp (half_pos hε)
    refine ⟨ofContinuousMap hab ⟨fun t ↦ g t, hg.continuous.comp continuous_subtype_val⟩, ?_⟩
    rw [dist_eq_norm]
    refine (SobolevIntervalLp.norm_le_sum_norm_deriv _).trans_lt ?_
    rw [Fin.sum_univ_one, SobolevIntervalLp.deriv_sub, deriv_toSobolevIntervalLp, Lp.norm_def]
    refine (ENNReal.toReal_le_of_le_ofReal (half_pos hε).le ?_).trans_lt (half_lt_self hε)
    refine le_of_eq_of_le (eLpNorm_congr_ae ?_) hgu
    filter_upwards [Lp.coeFn_sub (SobolevIntervalLp.deriv u 0) (derivLpOf p _ 0),
      coeFn_derivLpOf (p := p) (ofContinuousMap hab
        ⟨fun t ↦ g t, hg.continuous.comp continuous_subtype_val⟩) 0,
      ae_restrict_mem measurableSet_Ioo] with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, Pi.sub_apply]
    congr 1
    refine hx2.trans ?_
    rw [deriv_ofContinuousMap, IccExtend_of_mem hab _ (Ioo_subset_Icc_self hx3)]
    rfl
  | succ k ih =>
    intro u ε hε
    obtain ⟨CP, hCP⟩ : ∃ CP, CP = (b - a) / p.toReal ^ p.toReal⁻¹ := ⟨_, rfl⟩
    have hCP0 : 0 ≤ CP := hCP ▸ SobolevIntervalLp.poincareConst_nonneg hab
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = ε / (CP + k + 2) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := hδ ▸ by positivity
    obtain ⟨w, hw⟩ := ih (SobolevIntervalLp.shift u) δ hδ0
    rw [dist_eq_norm] at hw
    obtain ⟨c, hc⟩ : ∃ c, c = SobolevIntervalLp.rep (SobolevIntervalLp.derivOne u 0) a := ⟨_, rfl⟩
    refine ⟨cons w c, ?_⟩
    rw [dist_eq_norm]
    -- the higher components are those of `Du - w`
    have hsucc : ∀ j : Fin (k + 1),
        SobolevIntervalLp.deriv (u - toSobolevIntervalLp p hab hlt (k + 1) (cons w c)) j.succ
          = SobolevIntervalLp.deriv (SobolevIntervalLp.shift u - toSobolevIntervalLp p hab hlt k w)
            j := by
      intro j
      rw [SobolevIntervalLp.deriv_sub, SobolevIntervalLp.deriv_sub, deriv_toSobolevIntervalLp,
        deriv_toSobolevIntervalLp, SobolevIntervalLp.deriv_shift]
      congr 1
    -- the function component is the primitive of the first one
    have h0 : ⇑(SobolevIntervalLp.deriv (u - toSobolevIntervalLp p hab hlt (k + 1) (cons w c)) 0)
        =ᵐ[volume.restrict (Ioo a b)] fun x ↦ ∫ t in a..x,
          SobolevIntervalLp.deriv (SobolevIntervalLp.shift u - toSobolevIntervalLp p hab hlt k w)
            0 t := by
      have hw0 : ⇑(SobolevIntervalLp.deriv
          (SobolevIntervalLp.shift u - toSobolevIntervalLp p hab hlt k w) 0)
          =ᵐ[volume.restrict (Ioo a b)] fun t ↦ SobolevIntervalLp.deriv u 1 t
            - IccExtend hab (w.deriv 0) t := by
        rw [SobolevIntervalLp.deriv_sub, deriv_toSobolevIntervalLp, SobolevIntervalLp.deriv_shift]
        filter_upwards [Lp.coeFn_sub (SobolevIntervalLp.deriv u (Fin.succ 0)) (derivLpOf p w 0),
          coeFn_derivLpOf (p := p) w 0] with t ht1 ht2
        rw [ht1, Pi.sub_apply]
        exact congrArg₂ (· - ·) rfl ht2
      rw [SobolevIntervalLp.deriv_sub, deriv_toSobolevIntervalLp]
      filter_upwards [Lp.coeFn_sub (SobolevIntervalLp.deriv u 0) (derivLpOf p (cons w c) 0),
        coeFn_derivLpOf (p := p) (cons w c) 0,
        SobolevIntervalLp.fn_ae_eq_rep hI (SobolevIntervalLp.derivOne u 0),
        ae_restrict_mem measurableSet_Ioo] with x hx1 hx2 hx3 hx4
      have hx4' : x ∈ Icc a b := Ioo_subset_Icc_self hx4
      have ha' := hcl (left_mem_Icc.2 hab)
      have e1 : SobolevIntervalLp.deriv u 0 x
          = c + ∫ t in a..x, SobolevIntervalLp.deriv u 1 t := by
        have e2 := SobolevIntervalLp.rep_sub_rep hI (SobolevIntervalLp.derivOne u 0) ha' (hcl hx4')
        rw [SobolevIntervalLp.deriv_derivOne_one, Fin.succ_zero_eq_one] at e2
        rw [← hc] at e2
        rw [← e2, add_sub_cancel]
        exact hx3
      rw [hx1, Pi.sub_apply]
      calc ⇑(SobolevIntervalLp.deriv u 0) x - ⇑(derivLpOf p (cons w c) 0) x
          = (c + ∫ t in a..x, SobolevIntervalLp.deriv u 1 t)
            - (c + ∫ s in a..x, IccExtend hab (w.deriv 0) s) := by
            rw [e1]
            congr 1
            refine hx2.trans ?_
            rw [IccExtend_of_mem hab _ hx4', deriv_cons_zero, ContinuousMap.antideriv_apply]
            rfl
        _ = ∫ t in a..x, (SobolevIntervalLp.deriv u 1 t - IccExtend hab (w.deriv 0) t) := by
            rw [intervalIntegral.integral_sub
              (SobolevIntervalLp.intervalIntegrable_deriv hI u 1 ha' (hcl hx4'))
              ((show Continuous (IccExtend hab (w.deriv 0)) from
                (ContinuousMap.IccExtend hab (w.deriv 0)).continuous).intervalIntegrable _ _)]
            ring
        _ = _ := (intervalIntegral_congr_ae_of_mem_closure hI hw0 ha' (hcl hx4')).symm
    -- assembling
    have hD0 : ‖SobolevIntervalLp.deriv (u - toSobolevIntervalLp p hab hlt (k + 1) (cons w c)) 0‖
        ≤ CP * ‖SobolevIntervalLp.shift u - toSobolevIntervalLp p hab hlt k w‖ := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (SobolevIntervalLp.norm_deriv_le _ 0) hCP0)
      rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal hCP0, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _))
        ?_
      refine (eLpNorm_congr_ae h0).trans_le ?_
      rw [hCP]
      exact SobolevIntervalLp.eLpNorm_integral_le hab
        (SobolevIntervalLp.integrableOn_deriv_Ioo _ 0)
    have hDsucc : ∀ j : Fin (k + 1),
        ‖SobolevIntervalLp.deriv (u - toSobolevIntervalLp p hab hlt (k + 1) (cons w c)) j.succ‖
          ≤ ‖SobolevIntervalLp.shift u - toSobolevIntervalLp p hab hlt k w‖ := fun j ↦ by
      rw [hsucc j]; exact SobolevIntervalLp.norm_deriv_le _ j
    calc ‖u - toSobolevIntervalLp p hab hlt (k + 1) (cons w c)‖
        ≤ ∑ j : Fin (k + 2),
            ‖SobolevIntervalLp.deriv (u - toSobolevIntervalLp p hab hlt (k + 1) (cons w c)) j‖ :=
          SobolevIntervalLp.norm_le_sum_norm_deriv _
      _ = ‖SobolevIntervalLp.deriv (u - toSobolevIntervalLp p hab hlt (k + 1) (cons w c)) 0‖
          + ∑ j : Fin (k + 1), ‖SobolevIntervalLp.deriv
              (u - toSobolevIntervalLp p hab hlt (k + 1) (cons w c)) j.succ‖ :=
          Fin.sum_univ_succ _
      _ ≤ CP * ‖SobolevIntervalLp.shift u - toSobolevIntervalLp p hab hlt k w‖
          + ∑ _j : Fin (k + 1), ‖SobolevIntervalLp.shift u - toSobolevIntervalLp p hab hlt k w‖ :=
          add_le_add hD0 (Finset.sum_le_sum fun j _ ↦ hDsucc j)
      _ = (CP + (k + 1)) * ‖SobolevIntervalLp.shift u - toSobolevIntervalLp p hab hlt k w‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ < (CP + (k + 1)) * δ := by gcongr
      _ ≤ (CP + k + 2) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0.le
      _ = ε := by rw [hδ]; field_simp

end ContDiffMapIcc

/-! ### The interpolation inequality $\|D^j u\|_p \le \varepsilon \|D^m u\|_p + C \|u\|_p$ -/

namespace SobolevIntervalLp

open scoped Convolution

variable {m : ℕ} {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- Let $1 \le p \le \infty$, let $I$ be an open interval, and let $v, w \in W^{1,p}(I)$ with
$v' = w$ in $L^p(I)$, so that $v \in W^{2,p}(I)$ and $w' = v''$. Let $x \le y$ be points of $I$
and $z \in [x, y]$. Then the continuous representatives satisfy
$$(y - x) |\tilde w(z)| \le |\tilde v(y)| + |\tilde v(x)| + (y - x) \int_x^y |w'|.$$
This is the Taylor estimate behind the interpolation inequality.

It follows from $\tilde v(y) - \tilde v(x) = \int_x^y \tilde w = (y - x) \tilde w(z) + \int_x^y
(\tilde w(t) - \tilde w(z)) \, dt$ and $|\tilde w(t) - \tilde w(z)| \le \int_x^y |w'|$ for
$t \in [x, y]$. -/
theorem mul_norm_rep_le_of_deriv_eq (hI : (I : Set ℝ).OrdConnected)
    {v w : SobolevIntervalLp 1 p I} (hvw : deriv v 1 = deriv w 0) {x y z : ℝ}
    (hx : x ∈ (I : Set ℝ)) (hy : y ∈ (I : Set ℝ)) (hxy : x ≤ y) (hz : z ∈ Icc x y) :
    (y - x) * ‖rep w z‖ ≤ ‖rep v y‖ + ‖rep v x‖ + (y - x) * ∫ t in x..y, ‖deriv w 1 t‖ := by
  have hIcc : Icc x y ⊆ (I : Set ℝ) := hI.out hx hy
  have hcl : Icc x y ⊆ closure (I : Set ℝ) := hIcc.trans subset_closure
  have hx' : x ∈ closure (I : Set ℝ) := subset_closure hx
  have hy' : y ∈ closure (I : Set ℝ) := subset_closure hy
  have hz' : z ∈ closure (I : Set ℝ) := hcl hz
  obtain ⟨J, hJ⟩ : ∃ J, J = ∫ t in x..y, ‖deriv w 1 t‖ := ⟨_, rfl⟩
  have hJint : IntervalIntegrable (fun t ↦ ‖deriv w 1 t‖) volume x y :=
    (intervalIntegrable_deriv hI w 1 hx' hy').norm
  have hJ0 : 0 ≤ᵐ[volume.restrict (Ioc x y)] fun t ↦ ‖deriv w 1 t‖ :=
    Eventually.of_forall fun t ↦ norm_nonneg _
  -- `|w̃(t) - w̃(z)| ≤ J` for `t ∈ [x, y]`
  have hosc : ∀ t ∈ Icc x y, ‖rep w t - rep w z‖ ≤ J := by
    intro t ht
    rw [rep_sub_rep hI w hz' (hcl ht), hJ]
    rcases le_total z t with hzt | htz
    · refine (intervalIntegral.norm_integral_le_integral_norm hzt).trans ?_
      exact intervalIntegral.integral_mono_interval hz.1 hzt ht.2 hJ0 hJint
    · rw [intervalIntegral.integral_symm, norm_neg]
      refine (intervalIntegral.norm_integral_le_integral_norm htz).trans ?_
      exact intervalIntegral.integral_mono_interval ht.1 htz hz.2 hJ0 hJint
  -- `ṽ(y) - ṽ(x) = (y - x) w̃(z) + ∫_x^y (w̃(t) - w̃(z))`
  have hrep : IntervalIntegrable (rep w) volume x y := by
    refine ((continuousOn_rep hI w).mono ?_).intervalIntegrable
    rw [uIcc_of_le hxy]; exact hcl
  have e1 : rep v y - rep v x = (y - x) * rep w z + ∫ t in x..y, (rep w t - rep w z) := by
    rw [intervalIntegral.integral_sub hrep intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, rep_sub_rep hI v hx' hy', hvw]
    have : ∫ t in x..y, deriv w 0 t = ∫ t in x..y, rep w t := by
      refine intervalIntegral.integral_congr_ae ?_
      have := (ae_restrict_iff' I.isOpen.measurableSet).1 (fn_ae_eq_rep hI w)
      filter_upwards [this] with t ht htI
      refine ht (hIcc ?_)
      rw [uIoc_of_le hxy] at htI
      exact Ioc_subset_Icc_self htI
    rw [this]; ring
  have e2 : ‖∫ t in x..y, (rep w t - rep w z)‖ ≤ J * (y - x) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := y)
      (f := fun t ↦ rep w t - rep w z) (C := J) fun t ht ↦ by
        rw [uIoc_of_le hxy] at ht
        exact hosc t (Ioc_subset_Icc_self ht)
    rwa [abs_of_nonneg (sub_nonneg.2 hxy)] at this
  have e3 : (y - x) * rep w z = (rep v y - rep v x) - ∫ t in x..y, (rep w t - rep w z) := by
    rw [e1]; ring
  calc (y - x) * ‖rep w z‖ = ‖(y - x) * rep w z‖ := by
        rw [norm_mul, Real.norm_of_nonneg (sub_nonneg.2 hxy)]
    _ ≤ ‖rep v y - rep v x‖ + ‖∫ t in x..y, (rep w t - rep w z)‖ := by
        rw [e3]; exact norm_sub_le _ _
    _ ≤ (‖rep v y‖ + ‖rep v x‖) + J * (y - x) := add_le_add (norm_sub_le _ _) e2
    _ = ‖rep v y‖ + ‖rep v x‖ + (y - x) * ∫ t in x..y, ‖deriv w 1 t‖ := by rw [hJ]; ring

/-- **The interpolation inequality at order two.** Let $1 \le p \le \infty$, let $I$ be an open
interval, and let $v, w \in W^{1,p}(I)$ with $v' = w$ in $L^p(I)$. Let $h > 0$ with $2h < |I|$,
where $|I| \le \infty$ is the length of $I$. Then
$$\|w\|_p \le 2h \|w'\|_p + \frac{3}{h} \|v\|_p.$$
For $v \in W^{2,p}(I)$ this reads $\|v'\|_p \le 2h \|v''\|_p + (3/h) \|v\|_p$.

For $x \in I$, one of $x + h$ and $x - h$ lies in $I$, and the Taylor estimate
`SobolevIntervalLp.mul_norm_rep_le_of_deriv_eq` on $[x, x + h]$ or $[x - h, x]$ gives $h |\tilde
w(x)| \le |\tilde v(x)| + |\tilde v(x \pm h)| + h \int_{x-h}^{x+h} |w'|$. The last term is the
convolution of $|w'|$, extended by zero, with the indicator of $(-h, h)$. Its $L^p$ norm is at
most $2h \|w'\|_p$ by Young's inequality (`MeasureTheory.eLpNorm_convolution_lsmul_le`), and the
translates of $\tilde v$ have the $L^p$ norm of $\tilde v$. No covering of $I$ by small
intervals is needed. -/
theorem norm_deriv_zero_le_of_deriv_eq (hI : (I : Set ℝ).OrdConnected)
    {v w : SobolevIntervalLp 1 p I} (hvw : deriv v 1 = deriv w 0) {h : ℝ} (hh : 0 < h)
    (hvol : ENNReal.ofReal (2 * h) < volume (I : Set ℝ)) :
    ‖deriv w 0‖ ≤ 2 * h * ‖deriv w 1‖ + 3 / h * ‖deriv v 0‖ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hIm : MeasurableSet (I : Set ℝ) := I.isOpen.measurableSet
  -- the extension by zero of `|w'|` and the window kernel
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun t ↦ ‖(I : Set ℝ).indicator (deriv w 1) t‖ := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ → ℝ, κ = (Ioo (-h) h).indicator fun _ ↦ (1 : ℝ) := ⟨_, rfl⟩
  have hindm : AEStronglyMeasurable ((I : Set ℝ).indicator (deriv w 1)) volume :=
    (aestronglyMeasurable_indicator_iff hIm).2 (Lp.aestronglyMeasurable _)
  have hFp : MemLp F p volume := by
    rw [hF]
    exact ((memLp_indicator_iff_restrict hIm.nullMeasurableSet).2 (Lp.memLp (deriv w 1))).norm
  have hFm : AEStronglyMeasurable F volume := hFp.aestronglyMeasurable
  have hF0 : ∀ t, 0 ≤ F t := fun t ↦ by rw [hF]; exact norm_nonneg _
  have hκm : AEStronglyMeasurable κ volume := by
    rw [hκ]; exact aestronglyMeasurable_const.indicator measurableSet_Ioo
  have hFnorm : eLpNorm F p volume = ‖deriv w 1‖ₑ := by
    rw [hF, eLpNorm_norm _ hindm, eLpNorm_indicator_eq_eLpNorm_restrict hIm.nullMeasurableSet,
        Lp.enorm_def]
  have hκnorm : eLpNorm κ 1 volume = ENNReal.ofReal (2 * h) := by
    rw [hκ, eLpNorm_indicator_const measurableSet_Ioo.nullMeasurableSet one_ne_zero
      ENNReal.one_ne_top, Real.volume_Ioo, ENNReal.toReal_one, div_one, ENNReal.rpow_one,
      enorm_one, one_mul, sub_neg_eq_add, two_mul]
  -- the window integral `K x = ∫_{x-h}^{x+h} F` is the convolution `κ ⋆ F`
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ, K = κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F := ⟨_, rfl⟩
  have hKeq : ∀ x, K x = ∫ t in Ioo (x - h) (x + h), F t := by
    intro x
    rw [hK, convolution_lsmul_swap]
    have hind : ∀ t, κ (x - t) • F t = (Ioo (x - h) (x + h)).indicator F t := by
      intro t
      by_cases ht : t ∈ Ioo (x - h) (x + h)
      · have : x - t ∈ Ioo (-h) h := by
          rw [mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2]
        simp only [hκ, indicator_of_mem this, indicator_of_mem ht, one_smul]
      · have : x - t ∉ Ioo (-h) h := by
          rw [mem_Ioo] at ht ⊢; intro h'; exact ht ⟨by linarith [h'.2], by linarith [h'.1]⟩
        simp only [hκ, indicator_of_notMem this, indicator_of_notMem ht, zero_smul]
    simp only [hind]
    exact integral_indicator measurableSet_Ioo
  have hKm : AEStronglyMeasurable K volume := by rw [hK]; exact hκm.convolution _ hFm
  have hKnorm : eLpNorm K p volume ≤ ENNReal.ofReal (2 * h) * ‖deriv w 1‖ₑ := by
    rw [hK, ← hκnorm, ← hFnorm]
    exact eLpNorm_convolution_lsmul_le hp1 hκm hFm
  have hKint : ∀ x, IntegrableOn F (Ioo (x - h) (x + h)) := fun x ↦
    (hFp.restrict _).integrable hp1
  -- the interval integrals of `|w'|` over windows of `I` are bounded by `K`
  have hwin : ∀ a b x, a ∈ (I : Set ℝ) → b ∈ (I : Set ℝ) → a ≤ b →
      Ioo a b ⊆ Ioo (x - h) (x + h) → ∫ t in a..b, ‖deriv w 1 t‖ ≤ K x := by
    intro a b x ha hb hab hsub
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo, hKeq]
    have e : ∫ t in Ioo a b, ‖deriv w 1 t‖ = ∫ t in Ioo a b, F t := by
      refine setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
      simp only [hF]
      rw [indicator_of_mem (hI.out ha hb (Ioo_subset_Icc_self ht))]
    rw [e]
    exact setIntegral_mono_set (hKint x) (Eventually.of_forall hF0) hsub.eventuallySubset
  -- the pointwise bound on `I`
  have hpt : ∀ x ∈ (I : Set ℝ), h * ‖rep w x‖ ≤ ‖rep v x‖
      + ‖(I : Set ℝ).indicator (rep v) (x + h)‖ + ‖(I : Set ℝ).indicator (rep v) (x - h)‖
      + h * K x := by
    intro x hx
    by_cases hxh : x + h ∈ (I : Set ℝ)
    · have h1 := mul_norm_rep_le_of_deriv_eq hI hvw hx hxh (by linarith)
        (left_mem_Icc.2 (by linarith))
      rw [add_sub_cancel_left] at h1
      have h2 := hwin x (x + h) x hx hxh (by linarith) fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩
      have h3 := mul_le_mul_of_nonneg_left h2 hh.le
      have h4 := norm_nonneg ((I : Set ℝ).indicator (rep v) (x - h))
      rw [indicator_of_mem hxh]
      linarith
    by_cases hxh' : x - h ∈ (I : Set ℝ)
    · have h1 := mul_norm_rep_le_of_deriv_eq hI hvw hxh' hx (by linarith)
        (right_mem_Icc.2 (by linarith))
      rw [sub_sub_cancel] at h1
      have h2 := hwin (x - h) x x hxh' hx (by linarith) fun t ht ↦ ⟨ht.1, by linarith [ht.2]⟩
      have h3 := mul_le_mul_of_nonneg_left h2 hh.le
      have h4 := norm_nonneg ((I : Set ℝ).indicator (rep v) (x + h))
      rw [indicator_of_mem hxh']
      linarith
    exfalso
    have hsub : (I : Set ℝ) ⊆ Ioo (x - h) (x + h) := by
      intro y hy
      rw [mem_Ioo]
      constructor
      · by_contra hxy
        exact hxh' (hI.out hy hx ⟨not_lt.1 hxy, by linarith⟩)
      · by_contra hxy
        exact hxh (hI.out hx hy ⟨by linarith, not_lt.1 hxy⟩)
    have := measure_mono (μ := volume) hsub
    rw [Real.volume_Ioo, show x + h - (x - h) = 2 * h by ring] at this
    exact absurd (hvol.trans_le this) (lt_irrefl _)
  -- the `L^p` norms of the four terms
  have hrepv : AEStronglyMeasurable (rep v) (volume.restrict I) :=
    (memLp_rep hI v).aestronglyMeasurable
  have hind : AEStronglyMeasurable ((I : Set ℝ).indicator (rep v)) volume :=
    (aestronglyMeasurable_indicator_iff hIm).2 hrepv
  have hindnorm : eLpNorm ((I : Set ℝ).indicator (rep v)) p volume = ‖deriv v 0‖ₑ := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hIm.nullMeasurableSet, Lp.enorm_def, deriv_zero]
    exact eLpNorm_congr_ae (fn_ae_eq_rep hI v).symm
  obtain ⟨fA, hfA⟩ : ∃ f : ℝ → ℝ, f = fun x ↦ ‖rep v x‖ := ⟨_, rfl⟩
  obtain ⟨fB, hfB⟩ : ∃ f : ℝ → ℝ, f = fun x ↦ ‖(I : Set ℝ).indicator (rep v) (x + h)‖ :=
    ⟨_, rfl⟩
  obtain ⟨fC, hfC⟩ : ∃ f : ℝ → ℝ, f = fun x ↦ ‖(I : Set ℝ).indicator (rep v) (x - h)‖ :=
    ⟨_, rfl⟩
  obtain ⟨fD, hfD⟩ : ∃ f : ℝ → ℝ, f = fun x ↦ h * K x := ⟨_, rfl⟩
  have nA : eLpNorm fA p (volume.restrict I) = ‖deriv v 0‖ₑ := by
    rw [hfA, eLpNorm_norm _ hrepv, Lp.enorm_def, deriv_zero]
    exact eLpNorm_congr_ae (fn_ae_eq_rep hI v).symm
  have nB : eLpNorm fB p (volume.restrict I) ≤ ‖deriv v 0‖ₑ := by
    rw [hfB]
    refine (eLpNorm_restrict_le _ _ _ _).trans (le_of_eq ?_)
    rw [← hindnorm, ← eLpNorm_norm _ hind]
    exact eLpNorm_comp_measurePreserving hind.norm (measurePreserving_add_right volume h)
  have nC : eLpNorm fC p (volume.restrict I) ≤ ‖deriv v 0‖ₑ := by
    rw [hfC]
    refine (eLpNorm_restrict_le _ _ _ _).trans (le_of_eq ?_)
    rw [← hindnorm, ← eLpNorm_norm _ hind]
    exact eLpNorm_comp_measurePreserving hind.norm (measurePreserving_sub_right volume h)
  have nD : eLpNorm fD p (volume.restrict I)
      ≤ ENNReal.ofReal h * (ENNReal.ofReal (2 * h) * ‖deriv w 1‖ₑ) := by
    rw [hfD]
    refine (eLpNorm_restrict_le _ _ _ _).trans ?_
    change eLpNorm (h • K) p volume ≤ _
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg hh.le]
    gcongr
  have e0 : eLpNorm (fun x ↦ h * rep w x) p (volume.restrict I)
      = ENNReal.ofReal h * ‖deriv w 0‖ₑ := by
    change eLpNorm (h • rep w) p (volume.restrict I) = _
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg hh.le, Lp.enorm_def, deriv_zero]
    congr 1
    exact eLpNorm_congr_ae (fn_ae_eq_rep hI w).symm
  have hpt' : ∀ᵐ x ∂(volume.restrict I), ‖h * rep w x‖ ≤ (fA + fB + fC + fD) x := by
    filter_upwards [ae_restrict_mem hIm] with x hx
    simp only [Pi.add_apply, hfA, hfB, hfC, hfD]
    rw [norm_mul, Real.norm_of_nonneg hh.le]
    exact hpt x hx
  have hmain : ENNReal.ofReal h * ‖deriv w 0‖ₑ
      ≤ 3 * ‖deriv v 0‖ₑ + ENNReal.ofReal h * (ENNReal.ofReal (2 * h) * ‖deriv w 1‖ₑ) := by
    have s1 : eLpNorm (fun x ↦ h * rep w x) p (volume.restrict I)
        ≤ eLpNorm (fA + fB + fC + fD) p (volume.restrict I) :=
      eLpNorm_mono_ae_real ((memLp_rep hI w).aestronglyMeasurable.const_mul h) hpt'
    have s2 : eLpNorm (fA + fB + fC + fD) p (volume.restrict I)
        ≤ eLpNorm (fA + fB + fC) p (volume.restrict I) + eLpNorm fD p (volume.restrict I) :=
      eLpNorm_add_le hp1
    have s3 : eLpNorm (fA + fB + fC) p (volume.restrict I)
        ≤ eLpNorm (fA + fB) p (volume.restrict I) + eLpNorm fC p (volume.restrict I) :=
      eLpNorm_add_le hp1
    have s4 : eLpNorm (fA + fB) p (volume.restrict I)
        ≤ eLpNorm fA p (volume.restrict I) + eLpNorm fB p (volume.restrict I) :=
      eLpNorm_add_le hp1
    have e3 : (3 : ℝ≥0∞) * ‖deriv v 0‖ₑ = (‖deriv v 0‖ₑ + ‖deriv v 0‖ₑ) + ‖deriv v 0‖ₑ := by
      ring
    rw [← e0, e3]
    refine s1.trans (s2.trans ?_)
    refine add_le_add (s3.trans ?_) nD
    refine add_le_add (s4.trans ?_) nC
    exact add_le_add nA.le nB
  -- back to real numbers
  have hfin : h * ‖deriv w 0‖ ≤ 3 * ‖deriv v 0‖ + h * (2 * h * ‖deriv w 1‖) := by
    have := ENNReal.toReal_mono (by finiteness) hmain
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hh.le, toReal_enorm,
      ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hh.le, ENNReal.toReal_ofReal (by positivity),
      toReal_enorm, toReal_enorm, ENNReal.toReal_ofNat] at this
    linarith
  have hh' : h ≠ 0 := hh.ne'
  calc ‖deriv w 0‖ = h * ‖deriv w 0‖ / h := by field_simp
    _ ≤ (3 * ‖deriv v 0‖ + h * (2 * h * ‖deriv w 1‖)) / h :=
        div_le_div_of_nonneg_right hfin hh.le
    _ = 2 * h * ‖deriv w 1‖ + 3 / h * ‖deriv v 0‖ := by field_simp; ring

/-- Let $N_i \colon \mathbb{N} \to \mathbb{R}$, for $i$ in an index set, be nonnegative sequences,
let $h_0 > 0$, $A \ge 0$ and $M \in \mathbb{N}$. Suppose that for every $0 < h \le h_0$, every
$k$ with $k + 2 \le M$ and every $i$,
$$N_i(k + 1) \le h \, N_i(k + 2) + \frac{A}{h} N_i(k).$$
Then for all $1 \le j < m \le M$ and $\varepsilon > 0$ there is $C \ge 0$ with
$N_i(j) \le \varepsilon N_i(m) + C N_i(0)$ for every $i$. This is the combinatorial core of the
interpolation inequality, with $N_i(k)$ the norms $\|D^k u\|_p$.

The proof is by induction on $m$. The term $N_i(m - 1)$ of the hypothesis at $k = m - 1$ is
absorbed through the induction hypothesis with $\varepsilon = h / (2 (A + 1))$, so that the term
$N_i(m)$ on the right is at most half of the one on the left. -/
theorem exists_forall_le_mul_add_of_forall_le_mul_add_div {ι : Type*} (N : ι → ℕ → ℝ)
    (hN : ∀ i k, 0 ≤ N i k) {h₀ A : ℝ} (hh₀ : 0 < h₀) (hA : 0 ≤ A) {M : ℕ}
    (hB : ∀ h, 0 < h → h ≤ h₀ → ∀ k, k + 2 ≤ M → ∀ i,
      N i (k + 1) ≤ h * N i (k + 2) + A / h * N i k) :
    ∀ m ≤ M, ∀ j, 1 ≤ j → j < m → ∀ ε > 0, ∃ C, 0 ≤ C ∧ ∀ i, N i j ≤ ε * N i m + C * N i 0 := by
  intro m
  induction m with
  | zero => intro _ j _ hj; exact absurd hj (Nat.not_lt_zero j)
  | succ m ih =>
    intro hmM j hj1 hjm ε hε
    have hm1 : 1 ≤ m := by omega
    -- the top step: `N m ≤ ε N (m + 1) + C N 0`
    have htop : ∀ ε > 0, ∃ C, 0 ≤ C ∧ ∀ i, N i m ≤ ε * N i (m + 1) + C * N i 0 := by
      intro ε hε
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · obtain rfl : m = 1 := by omega
        obtain ⟨h, hh⟩ : ∃ h, h = min ε h₀ := ⟨_, rfl⟩
        have hh0 : 0 < h := hh ▸ lt_min hε hh₀
        refine ⟨A / h, by positivity, fun i ↦ ?_⟩
        have h1 := hB h hh0 (hh ▸ min_le_right _ _) 0 (by omega) i
        have h2 : h * N i 2 ≤ ε * N i 2 :=
          mul_le_mul_of_nonneg_right (hh ▸ min_le_left _ _) (hN i 2)
        linarith
      · obtain ⟨h, hh⟩ : ∃ h, h = min (ε / 2) h₀ := ⟨_, rfl⟩
        have hh0 : 0 < h := hh ▸ lt_min (half_pos hε) hh₀
        have hh' : h ≤ ε / 2 := hh ▸ min_le_left _ _
        obtain ⟨C'', hC''0, hC''⟩ := ih (by omega) (m - 1) (by omega) (by omega)
          (h / (2 * (A + 1))) (by positivity)
        refine ⟨2 * A * C'' / h, by positivity, fun i ↦ ?_⟩
        have h1 := hB h hh0 (hh ▸ min_le_right _ _) (m - 1) (by omega) i
        have h2 := hC'' i
        rw [show m - 1 + 1 = m by omega, show m - 1 + 2 = m + 1 by omega] at h1
        have hAh : A / h * (h / (2 * (A + 1))) ≤ 1 / 2 := by
          rw [div_mul_div_comm, mul_comm A h, ← div_mul_div_comm, div_self hh0.ne', one_mul,
            div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
        have hNm := hN i m
        have hN1 := hN i (m + 1)
        have key : N i m ≤ h * N i (m + 1)
            + (A / h * (h / (2 * (A + 1))) * N i m + A / h * C'' * N i 0) := by
          refine h1.trans ?_
          have : A / h * N i (m - 1) ≤ A / h * (h / (2 * (A + 1)) * N i m + C'' * N i 0) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          linarith
        have h3 : A / h * (h / (2 * (A + 1))) * N i m ≤ 1 / 2 * N i m :=
          mul_le_mul_of_nonneg_right hAh hNm
        have h4 : 2 * h * N i (m + 1) ≤ ε * N i (m + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) hN1
        have e2 : 2 * A * C'' / h * N i 0 = 2 * (A / h * C'' * N i 0) := by ring
        rw [e2]
        linarith
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hjm) with rfl | hjm'
    · exact htop ε hε
    · obtain ⟨C, hC0, hC⟩ := htop ε hε
      obtain ⟨C', hC'0, hC'⟩ := ih (by omega) j hj1 hjm' 1 one_pos
      refine ⟨C + C', by positivity, fun i ↦ ?_⟩
      have h1 := hC i
      have h2 := hC' i
      nlinarith

/-- **The interpolation inequality.** Let $1 \le p \le \infty$, let $I$ be an open interval, and let
$0 < j < m$ and $\varepsilon > 0$. Then there is a constant $C \ge 0$ such that
$$\|D^j u\|_p \le \varepsilon \|D^m u\|_p + C \|u\|_p$$
for every $u \in W^{m,p}(I)$. This is the inequality of [brezis2011functional], §8.2, paragraph
"The Sobolev spaces $W^{m,p}$". The source states it for a bounded interval with a reference to
Adams, and as Exercise 8.6 through the compact embedding.

The constant depends on $\varepsilon$, $m$, $p$ and $|I|$. The estimate at order two
`SobolevIntervalLp.norm_deriv_zero_le_of_deriv_eq`, applied to the pairs
`SobolevIntervalLp.derivOne u k` and `derivOne u (k + 1)`, gives $\|D^{k+1} u\|_p \le h
\|D^{k+2} u\|_p + (6/h) \|D^k u\|_p$ for every $0 < h < |I|$. The induction
`SobolevIntervalLp.exists_forall_le_mul_add_of_forall_le_mul_add_div` on $m$ carries it to all
intermediate orders. The orders $j$ and $m$ are `j : Fin (m + 1)` with `j ≠ 0` and
`j ≠ Fin.last m`. -/
theorem eLpNorm_deriv_le_mul_add (hI : (I : Set ℝ).OrdConnected) (j : Fin (m + 1)) (hj0 : j ≠ 0)
    (hjm : j ≠ Fin.last m) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevIntervalLp m p I,
      ‖deriv u j‖ ≤ ε * ‖deriv u (Fin.last m)‖ + C * ‖deriv u 0‖ := by
  have hIm : MeasurableSet (I : Set ℝ) := I.isOpen.measurableSet
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · -- on the empty set every norm vanishes
    refine ⟨0, le_rfl, fun u ↦ ?_⟩
    have hz : ∀ k, ‖deriv u k‖ = 0 := fun k ↦ by
      rw [Lp.norm_def, eLpNorm_congr_ae (g := 0) ((ae_restrict_iff' hIm).2
        (Eventually.of_forall fun x hx ↦ by rw [hI0] at hx; exact hx.elim)), eLpNorm_zero,
        ENNReal.toReal_zero]
    rw [hz, hz, hz]; simp
  -- the admissible window lengths
  obtain ⟨h₀, hh₀, hvol⟩ : ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h, 0 < h → h ≤ h₀ →
      ENNReal.ofReal (2 * h) < volume (I : Set ℝ) := by
    have hpos : 0 < volume (I : Set ℝ) := I.isOpen.measure_pos volume hne
    rcases eq_or_ne (volume (I : Set ℝ)) ⊤ with htop | hfin
    · exact ⟨1, one_pos, fun h _ _ ↦ htop ▸ ENNReal.ofReal_lt_top⟩
    · have hpos' : 0 < (volume (I : Set ℝ)).toReal := ENNReal.toReal_pos hpos.ne' hfin
      refine ⟨(volume (I : Set ℝ)).toReal / 4, by positivity, fun h hh hh₀ ↦ ?_⟩
      calc ENNReal.ofReal (2 * h) ≤ ENNReal.ofReal ((volume (I : Set ℝ)).toReal / 2) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ < ENNReal.ofReal (volume (I : Set ℝ)).toReal :=
            (ENNReal.ofReal_lt_ofReal_iff hpos').2 (by linarith)
        _ = volume (I : Set ℝ) := ENNReal.ofReal_toReal hfin
  -- the order is at least two
  have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.2 fun h ↦ hj0 (Fin.ext h)
  have hjm' : (j : ℕ) < m := Fin.val_lt_last hjm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- the family of norms
  obtain ⟨N, hN⟩ : ∃ N : SobolevIntervalLp (m' + 1) p I → ℕ → ℝ,
      N = fun u k ↦ if hk : k ≤ m' + 1 then ‖deriv u ⟨k, Nat.lt_succ_of_le hk⟩‖ else 0 :=
    ⟨_, rfl⟩
  have hNk : ∀ u k (hk : k ≤ m' + 1), N u k = ‖deriv u ⟨k, Nat.lt_succ_of_le hk⟩‖ :=
    fun u k hk ↦ by subst hN; exact dite_eq_left hk
  have hN0 : ∀ u k, 0 ≤ N u k := fun u k ↦ by
    subst hN
    dsimp only
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  -- the window estimate, for the pairs `(D^k u, D^{k+1} u)` and `(D^{k+1} u, D^{k+2} u)`
  have hB : ∀ h, 0 < h → h ≤ h₀ → ∀ k, k + 2 ≤ m' + 1 → ∀ u,
      N u (k + 1) ≤ h * N u (k + 2) + 6 / h * N u k := by
    intro h hh hhh₀ k hk u
    have hvol' : ENNReal.ofReal (2 * (h / 2)) < volume (I : Set ℝ) :=
      (ENNReal.ofReal_le_ofReal (by linarith)).trans_lt (hvol h hh hhh₀)
    have key := norm_deriv_zero_le_of_deriv_eq hI (v := derivOne u ⟨k, by omega⟩)
      (w := derivOne u ⟨k + 1, by omega⟩) rfl (half_pos hh) hvol'
    simp only [deriv_derivOne_zero, deriv_derivOne_one, Fin.castSucc_mk, Fin.succ_mk] at key
    rw [hNk u (k + 1) (by omega), hNk u (k + 2) (by omega), hNk u k (by omega)]
    have e1 : (2 : ℝ) * (h / 2) = h := by ring
    have e2 : (3 : ℝ) / (h / 2) = 6 / h := by
      have := hh.ne'
      field_simp
      norm_num
    rw [e1, e2] at key
    exact key
  obtain ⟨C, hC0, hC⟩ := exists_forall_le_mul_add_of_forall_le_mul_add_div N hN0 hh₀
    (by norm_num : (0 : ℝ) ≤ 6) hB (m' + 1) le_rfl j hj1 hjm' ε hε
  refine ⟨C, hC0, fun u ↦ ?_⟩
  have := hC u
  rwa [hNk u j hjm'.le, hNk u (m' + 1) le_rfl, hNk u 0 (Nat.zero_le _)] at this

/-- **Equivalent norm.** Let $1 \le p \le \infty$, let $I$ be an open interval, and let
$m \in \mathbb{N}$. Then there is a constant $C \ge 0$ with
$$\|u\|_{W^{m,p}(I)} \le C \bigl(\|u\|_p + \|D^m u\|_p\bigr)$$
for every $u \in W^{m,p}(I)$. Thus $\|u\|_p + \|D^m u\|_p$ is a norm equivalent to the norm of
$W^{m,p}(I)$. This is the corollary of the interpolation inequality in [brezis2011functional],
§8.2, paragraph "The Sobolev spaces $W^{m,p}$".

The reverse comparison is `SobolevIntervalLp.norm_deriv_le`. Each intermediate $\|D^j u\|_p$ is
bounded by `SobolevIntervalLp.eLpNorm_deriv_le_mul_add` with $\varepsilon = 1$. -/
theorem exists_norm_le_mul_norm_deriv_add (hI : (I : Set ℝ).OrdConnected) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevIntervalLp m p I,
      ‖u‖ ≤ C * (‖deriv u 0‖ + ‖deriv u (Fin.last m)‖) := by
  have key : ∀ j : Fin (m + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevIntervalLp m p I,
      ‖deriv u j‖ ≤ ‖deriv u (Fin.last m)‖ + C * ‖deriv u 0‖ := by
    intro j
    by_cases hj0 : j = 0
    · exact ⟨1, zero_le_one, fun u ↦ by
        rw [hj0, one_mul]; exact le_add_of_nonneg_left (norm_nonneg _)⟩
    by_cases hjm : j = Fin.last m
    · exact ⟨0, le_rfl, fun u ↦ by simp [hjm]⟩
    obtain ⟨C, hC0, hC⟩ := eLpNorm_deriv_le_mul_add (p := p) hI j hj0 hjm one_pos
    exact ⟨C, hC0, fun u ↦ by simpa using hC u⟩
  choose C hC0 hC using key
  refine ⟨∑ j, (1 + C j), Finset.sum_nonneg fun j _ ↦ by linarith [hC0 j], fun u ↦ ?_⟩
  calc ‖u‖ ≤ ∑ j, ‖deriv u j‖ := norm_le_sum_norm_deriv u
    _ ≤ ∑ j, (1 + C j) * (‖deriv u 0‖ + ‖deriv u (Fin.last m)‖) := by
        refine Finset.sum_le_sum fun j _ ↦ (hC j u).trans ?_
        have h1 := norm_nonneg (deriv u 0)
        have h2 := mul_nonneg (hC0 j) (norm_nonneg (deriv u (Fin.last m)))
        nlinarith
    _ = (∑ j, (1 + C j)) * (‖deriv u 0‖ + ‖deriv u (Fin.last m)‖) := by rw [Finset.sum_mul]

end SobolevIntervalLp

/-! ### The Leibniz formula for the weak derivatives of a product by a smooth function -/

section LeibnizLine

variable {I : Opens ℝ} {f v w : ℝ → ℝ} {k : ℕ}

/-- Let $I \subseteq \mathbb{R}$ be open. If $v$ is the weak derivative of order $k$ of $f$ on $I$
and $w$ is the weak derivative of $v$ on $I$, then $w$ is the weak derivative of order $k + 1$
of $f$ on $I$. -/
theorem HasWeakIteratedDerivOn.succ_of_hasWeakDerivOn (h : HasWeakIteratedDerivOn k f v I)
    (h' : HasWeakDerivOn v w I) : HasWeakIteratedDerivOn (k + 1) f w I := by
  have h'' : HasWeakIteratedLineDerivOn ![(1 : ℝ)] v w I volume :=
    (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn (fun j ↦ by fin_cases j; rfl) rfl).2 h'
  exact (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn (y := Fin.cons 1 fun _ ↦ 1)
    (fun j ↦ by refine Fin.cases rfl (fun j ↦ rfl) j) rfl).1 (h.cons h'')

/-- **The Leibniz rule for a smooth factor on the line.** Let $I \subseteq \mathbb{R}$ be open, let
$w$ be the weak derivative of $f$ on $I$, and let $g$ be smooth on $\mathbb{R}$. Then the weak
derivative of $g f$ on $I$ is $g w + g' f$.

This is the one-dimensional case of `HasWeakIteratedLineDerivOn.contDiff_mul`. -/
theorem HasWeakDerivOn.contDiff_mul (h : HasWeakDerivOn f w I) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    HasWeakDerivOn (fun x ↦ g x * f x) (fun x ↦ g x * w x + deriv g x * f x) I := by
  have h1 : HasWeakIteratedLineDerivOn ![(1 : ℝ)] f w I volume :=
    (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn (fun j ↦ by fin_cases j; rfl) rfl).2 h
  exact (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn
    (fun j ↦ by fin_cases j; rfl) rfl).1 (h1.contDiff_mul hg)

/-- **The Leibniz formula** for the weak derivatives of a product with a smooth function. Let
$I \subseteq \mathbb{R}$ be open and $m \in \mathbb{N}$. Let $D_0, D_1, \dots$ be functions with
$D_0$ locally integrable on $I$ and $D_{i+1}$ the weak derivative of $D_i$ on $I$ for every
$i < m$. Let $G_0, G_1, \dots$ be smooth functions with $G_n' = G_{n+1}$ for every $n$. Then for
every $j \le m$, the weak derivative of order $j$ of $G_0 D_0$ on $I$ is
$$\sum_{i=0}^{j} \binom{j}{i} G_{j-i} D_i.$$

The proof is by induction on $j$, from the rule at order one `HasWeakDerivOn.contDiff_mul` and
Pascal's rule (`Finset.sum_choose_succ_mul`). -/
theorem hasWeakIteratedDerivOn_sum_choose_mul {D G : ℕ → ℝ → ℝ} {m : ℕ}
    (hD : ∀ i < m, HasWeakDerivOn (D i) (D (i + 1)) I) (hD0 : LocallyIntegrableOn (D 0) I)
    (hG : ∀ n, ContDiff ℝ ∞ (G n)) (hGd : ∀ n, deriv (G n) = G (n + 1)) {j : ℕ} (hj : j ≤ m) :
    HasWeakIteratedDerivOn j (fun x ↦ G 0 x * D 0 x)
      (fun x ↦ ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * G (j - i) x * D i x) I := by
  induction j with
  | zero =>
    refine (HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _ ?_).congr_ae
      (EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ by simp)
    exact hD0.continuousOn_smul I.isOpen.isLocallyClosed (hG 0).continuous.continuousOn
  | succ j ih =>
    refine (ih (Nat.le_of_succ_le hj)).succ_of_hasWeakDerivOn ?_
    have hterm : ∀ i ∈ Finset.range (j + 1), HasWeakDerivOn
        (fun x ↦ ((j.choose i : ℕ) : ℝ) * G (j - i) x * D i x)
        (fun x ↦ ((j.choose i : ℕ) : ℝ) * (G (j - i) x * D (i + 1) x + G (j - i + 1) x * D i x))
        I := fun i hi ↦ by
      have hi' : i < m := by have := Finset.mem_range.1 hi; omega
      have := ((hD i hi').contDiff_mul (hG (j - i))).const_smul ((j.choose i : ℕ) : ℝ)
      refine this.congr_ae (Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
      · simp only [Pi.smul_apply, smul_eq_mul]; ring
      · simp only [Pi.smul_apply, smul_eq_mul, hGd]
    refine (HasWeakIteratedLineDerivOn.finset_sum hterm).congr_ae (EventuallyEq.refl _ _)
      (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    have key := Finset.sum_choose_succ_mul (fun i k ↦ G k x * D i x) j
    calc ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℕ) : ℝ) * (G (j - i) x * D (i + 1) x + G (j - i + 1) x * D i x)
        = (∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * (G (j + 1 - i) x * D i x))
          + ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * (G (j - i) x * D (i + 1) x) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          have : j + 1 - i = j - i + 1 := by have := Finset.mem_range.1 hi; omega
          rw [this]; ring
      _ = ∑ i ∈ Finset.range (j + 2), (((j + 1).choose i : ℕ) : ℝ) * (G (j + 1 - i) x * D i x) :=
          key.symm
      _ = _ := Finset.sum_congr rfl fun i _ ↦ by ring

end LeibnizLine

section ContDiffMul

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)] {m : ℕ}

/-- **Multiplication by a smooth function preserves $W^{m,p}(I)$.** Let $1 \le p \le \infty$, let
$I \subseteq \mathbb{R}$ be open, and let $g$ be smooth on $\mathbb{R}$ with
$|g^{(k)}(x)| \le B$ for all $k \le m$ and $x \in \mathbb{R}$. Then for every $u \in W^{m,p}(I)$
there is $v \in W^{m,p}(I)$ with
$$D^j v = \sum_{i=0}^{j} \binom{j}{i} g^{(j-i)} D^i u$$
almost everywhere on $I$, for every $j \le m$. In particular $v = g u$.

The element $v$ is built from `hasWeakIteratedDerivOn_sum_choose_mul` with
`SobolevIntervalLp.mk`. -/
theorem exists_contDiff_mul {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {B : ℝ}
    (hB : ∀ k ≤ m, ∀ x, |iteratedDeriv k g x| ≤ B) (u : SobolevIntervalLp m p I) :
    ∃ v : SobolevIntervalLp m p I, ∀ j : Fin (m + 1), ⇑(deriv v j) =ᵐ[volume.restrict I]
      fun x ↦ ∑ i : Fin (j + 1), ((j : ℕ).choose i : ℝ) * iteratedDeriv (j - i) g x
        * deriv u ⟨i, by omega⟩ x := by
  classical
  -- the chain of weak derivatives, indexed by `ℕ`
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℝ → ℝ,
      D = fun i ↦ if h : i < m + 1 then ⇑(deriv u ⟨i, h⟩) else 0 := ⟨_, rfl⟩
  have hDi : ∀ i (h : i < m + 1), D i = ⇑(deriv u ⟨i, h⟩) := fun i h ↦ by
    rw [hDdef]; exact dite_eq_left h
  have hD : ∀ i < m, HasWeakDerivOn (D i) (D (i + 1)) I := fun i hi ↦ by
    rw [hDi i (by omega), hDi (i + 1) (by omega)]
    exact hasWeakDerivOn_deriv_succ u ⟨i, hi⟩
  have hD0 : LocallyIntegrableOn (D 0) I := by
    rw [hDi 0 (by omega)]; exact locallyIntegrableOn_deriv u _
  have hDp : ∀ i (h : i < m + 1), MemLp (D i) p (volume.restrict I) := fun i h ↦ by
    rw [hDi i h]; exact memLp_deriv u _
  -- the chain of derivatives of `g`
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℝ → ℝ, G = fun k ↦ iteratedDeriv k g := ⟨_, rfl⟩
  have hG : ∀ k, ContDiff ℝ ∞ (G k) := fun k ↦ by
    rw [hGdef]; dsimp only; rw [iteratedDeriv_eq_iterate]; exact hg.iterate_deriv k
  have hGd : ∀ k, _root_.deriv (G k) = G (k + 1) := fun k ↦ by
    rw [hGdef]; exact iteratedDeriv_succ.symm
  have hGB : ∀ k ≤ m, ∀ x, |G k x| ≤ B := fun k hk x ↦ by rw [hGdef]; exact hB k hk x
  -- the Leibniz sums lie in `L^p(I)`
  have hL : ∀ j : Fin (m + 1), MemLp (fun x ↦ ∑ i ∈ Finset.range (j + 1),
      (((j : ℕ).choose i : ℕ) : ℝ) * G (j - i) x * D i x) p (volume.restrict I) := fun j ↦ by
    refine memLp_finsetSum _ fun i hi ↦ ?_
    have hi' : i < m + 1 := by have := Finset.mem_range.1 hi; omega
    refine (hDp i hi').of_ae_norm_le_mul
      ((continuous_const.mul (hG (j - i)).continuous).aestronglyMeasurable.mul
        (hDp i hi').aestronglyMeasurable) (c := (((j : ℕ).choose i : ℕ) : ℝ) * B)
      (Eventually.of_forall fun x ↦ ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
    have := hGB (j - i) (by omega) x
    gcongr
  have hw : ∀ j : Fin (m + 1), HasWeakIteratedDerivOn j ⇑((hL 0).toLp _) ⇑((hL j).toLp _) I :=
    fun j ↦ by
    refine (hasWeakIteratedDerivOn_sum_choose_mul hD hD0 hG hGd (j := j) (by omega)).congr_ae
      ?_ (hL j).coeFn_toLp.symm
    refine EventuallyEq.trans ?_ (hL 0).coeFn_toLp.symm
    exact Eventually.of_forall fun x ↦ by simp
  refine ⟨mk (fun j ↦ (hL j).toLp _) hw, fun j ↦ ?_⟩
  rw [deriv_mk]
  refine (hL j).coeFn_toLp.trans (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [Finset.sum_range (fun i ↦ (((j : ℕ).choose i : ℕ) : ℝ) * G (j - i) x * D i x)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hDi i (by omega), hGdef]

end SobolevIntervalLp

end ContDiffMul

end
