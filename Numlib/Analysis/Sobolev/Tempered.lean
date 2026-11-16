/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside Mathlib's Bessel potential spaces.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.Sobolev
import Numlib.Analysis.Sobolev.MultiIndex

/-!
# Weak derivatives and tempered distributions on the whole space

There are two ways to differentiate a locally integrable function on a finite-dimensional real space
$E$ in the sense of distributions, and they use different classes of test functions. Definition
7.1.3 of [han2009theoretical] tests against $C_0^\infty$, the compactly supported smooth functions;
this is `HasWeakIteratedLineDerivOn` of `Numlib.Analysis.Sobolev.WeakDeriv`, and it makes sense on
any open set. Mathlib's `TemperedDistribution` tests against the Schwartz class, which needs the
whole space but supports the Fourier transform. This module shows that on the whole space the two
derivatives agree for $L^p$ functions. It concludes that the Sobolev space of integer order $k$
defined by the weak derivatives is Mathlib's Bessel potential space $H^k$.

Below, $\partial^m = \partial_{m_0} \cdots \partial_{m_{n-1}}$ is the iterated directional
derivative along a tuple $m \in E^n$, with $\partial_{m_0}$ outermost. For $u \in L^p(\mu)$, $T_u$
is the tempered distribution $g \mapsto \int g u \, d\mu$. For $s \in \mathbb{R}$ and $p \ge 1$,
$H^{s,p}$ is the Bessel potential space of the tempered distributions $f$ for which
$\mathcal{F}^{-1} (1 + |\xi|^2)^{s/2} \mathcal{F} f$ is an $L^p$ function
(`TemperedDistribution.MemSobolev s p`), and $H^s = H^{s,2}$. The module also computes the Fourier
transform of a weak derivative and gives the continuous representative of an $L^2$ function with
integrable Fourier transform.

## Main definitions

* `LineDeriv.listLineDerivOp`: the iterated line derivative along a list of directions, the head of
  the list outermost.
* `lineSymbol`: the symbol $\sigma_m(\xi) = \prod_j \langle \xi, m_j \rangle$ of $\partial^m$.

## Main results

* `SchwartzMap.iteratedLineDerivOp_congr_perm` and
  `TemperedDistribution.iteratedLineDerivOp_congr_perm`: the iterated directional derivative of a
  Schwartz function or a tempered distribution does not change when its directions are permuted.
* `HasWeakIteratedLineDerivOn.integral_smul_eq_schwartz`: if $f$ and its weak derivative $w$ along
  $m$ lie in $L^p$, then $\int (\partial^m g) f = (-1)^n \int g w$ for every Schwartz function $g$.
* `MeasureTheory.Lp.iteratedLineDerivOp_eq_iff_hasWeakIteratedLineDerivOn`: for $u, v \in L^p$,
  $\partial^m T_u = T_v$ if and only if $v$ is a weak derivative of $u$ along $m$ in the sense of
  integration by parts against $C_0^\infty(E)$.
* `TemperedDistribution.MemSobolev.of_iteratedLineDerivOp`: if every iterated directional derivative
  of order at most $k$ of a tempered distribution is an $L^2$ function, then the distribution lies
  in $H^k$.
* `TemperedDistribution.memSobolev_iff_memSobolevMultiIndex`, with its two halves
  `TemperedDistribution.MemSobolev.memSobolevMultiIndex` and
  `TemperedDistribution.MemSobolev.of_memSobolevMultiIndex`: an $L^2$ function lies in the Sobolev
  space $W^{k,2}(\mathbb{R}^d)$ of `Numlib.Analysis.Sobolev.MultiIndex`, defined by the weak
  derivatives $\partial^\alpha$ with $|\alpha| \le k$, if and only if it lies in Mathlib's Bessel
  potential space $H^k(\mathbb{R}^d)$.
* `memSobolevMultiIndex_ofReal_iff`: a real function lies in $W^{k,p}(\Omega)$ if and only if its
  complexification does.
* `fourier_weakDeriv_aeEq`: the Fourier transform of a weak derivative $\partial^m v$ of an $L^2$
  function $v$ is $(2\pi i)^n \sigma_m \mathcal{F} v$.
* `exists_continuous_ae_eq_of_integrable_fourier`: an $L^2$ function $v$ with integrable Fourier
  transform has a continuous representative bounded by $\int |\mathcal{F} v|$.

## Proof outline

One direction of the equivalence of the two derivatives is immediate, because a test function is a
Schwartz function. For the other, `HasWeakIteratedLineDerivOn.integral_smul_eq_schwartz` multiplies
a Schwartz function $g$ by the cut-offs $\chi(\cdot/(N+1))$, so that $\chi(\cdot/(N+1)) g$ is a test
function, and passes to the limit by dominated convergence. The derivatives of the cut-offs are
bounded uniformly in $N$, because rescaling by a factor at most $1$ does not increase them. The
resulting bound is integrable against an $L^p$ function, because the derivatives of a Schwartz
function are bounded and integrable and hence lie in every $L^q$.

The converse `TemperedDistribution.MemSobolev.of_iteratedLineDerivOp` of Mathlib's
`TemperedDistribution.MemSobolev.lineDerivOp` goes by induction on $k$. It rests on the multiplier
identity
$$(1 + |\xi|^2)^{1/2} = (1 + |\xi|^2)^{-1/2} + |\xi|^2 (1 + |\xi|^2)^{-1/2},$$
in which the second summand is, up to the constant that Mathlib's convention for the Fourier
transform contributes, the symbol of the Laplacian (`TemperedDistribution.besselPotential_one_eq`).

## Implementation notes

* The two descriptions of $H^k$ are indexed differently, and matching them needs the derivatives to
  commute. `MemSobolevMultiIndex` names a derivative by a multi-index $\alpha$, which
  `multiIndexDirections` reads as the list of basis vectors $b_i$, each repeated $\alpha_i$ times,
  in increasing order of $i$. The induction that builds $H^k$ out of $H^0$ takes one derivative off
  the front, and so produces the basis vectors in an arbitrary order. Matching the two needs the
  invariance of $\partial_{m_1} \cdots \partial_{m_n}$ under permutations of the directions, which
  is proved here from scratch. `SchwartzMap.lineDerivOp_comm` is the symmetry of the second
  derivative of a smooth function, Mathlib's `second_derivative_symmetric`, and
  `LineDeriv.listLineDerivOp_congr_perm` propagates it along a `List.Perm`, whose `swap` constructor
  is exactly a transposition of two adjacent directions. Mathlib has the symmetry of
  `iteratedFDeriv` only at order two, or at every order for analytic functions, so the route through
  lists is what makes the general order available for Schwartz functions and hence for tempered
  distributions.
* Everything here is on the whole space and for the measures that support the Schwartz theory
  (`MeasureTheory.Measure.HasTemperateGrowth`). Nothing is claimed on a proper open subset, where
  the Schwartz class is not available and the comparison has no meaning.
* The Bessel potential `TemperedDistribution.besselPotential E F s` is the Fourier multiplier with
  symbol $(1 + |\xi|^2)^{s/2}$. With Mathlib's convention for the Fourier transform, the symbol of
  the Laplacian is $-(2\pi)^2 |\xi|^2$, not $-|\xi|^2$.
* The equivalence of $W^{k,2}(\mathbb{R}^d)$ and $H^k(\mathbb{R}^d)$ is proved for membership only;
  the norms are not compared.
-/

open Filter FourierTransform LineDeriv Metric MeasureTheory Set TemperedDistribution
  TopologicalSpace

open scoped ContDiff Distributions ENNReal Laplacian Real SchwartzMap Topology


/-! ### Preliminaries on $L^p$ spaces -/

namespace MeasureTheory

variable {α G : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup G]

/-- Let $f$ be integrable with $\|f(x)\| \le C$ for almost every $x$. Then $f \in L^q$ for every $q$
with $1 \le q \le \infty$, because the pointwise bound makes $\|f\|^q$ at most a constant
multiple of $\|f\|$. -/
theorem Integrable.memLp_of_bound {f : α → G} (hf : Integrable f μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) {q : ℝ≥0∞} (hq : 1 ≤ q) : MemLp f q μ := by
  rcases eq_or_ne q ∞ with rfl | hq'
  · exact memLp_top_of_bound hf.1 C hC
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hr : (1 : ℝ) ≤ q.toReal := by
    rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact ENNReal.toReal_mono hq' hq
  set C' : ℝ := max C 0 with hC'
  have hbd : ∀ᵐ x ∂μ, ‖f x‖ ≤ C' := hC.mono fun x hx ↦ hx.trans (le_max_left _ _)
  rw [← integrable_norm_rpow_iff hf.1 hq0 hq']
  have hmeas : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ q.toReal) μ :=
    (Real.continuous_rpow_const (by linarith)).comp_aestronglyMeasurable hf.1.norm
  refine Integrable.mono (hf.norm.const_mul (C' ^ (q.toReal - 1))) hmeas ?_
  filter_upwards [hbd] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  rcases eq_or_lt_of_le (norm_nonneg (f x)) with h0 | h0
  · rw [← h0, Real.zero_rpow (by linarith), mul_zero]
  · have key : ‖f x‖ ^ (q.toReal - 1) * ‖f x‖ = ‖f x‖ ^ q.toReal := by
      conv_rhs => rw [show q.toReal = q.toReal - 1 + 1 by ring]
      rw [Real.rpow_add h0, Real.rpow_one]
    rw [← key]
    gcongr

end MeasureTheory

/-! ### Commuting line derivatives -/

namespace LineDeriv

variable {V X : Type*} [LineDeriv V X X]

/-- Let $X$ carry line derivatives $\partial_v$ along the directions $v \in V$. The **iterated line
derivative along a list** $l = [v_1, \dots, v_n]$ of directions is
$$\partial_l x = \partial_{v_1} \cdots \partial_{v_n} x,$$
in which the head of the list is the outermost derivative.

This is the operation `LineDeriv.iteratedLineDerivOp` indexed by a list instead of a tuple (see
`LineDeriv.iteratedLineDerivOp_eq_listLineDerivOp`). The list makes `List.Perm` available as an
induction principle. -/
def listLineDerivOp (l : List V) (x : X) : X := l.foldr (fun v y ↦ ∂_{v} y) x

/-- The iterated line derivative along the empty list is the identity. -/
@[simp] theorem listLineDerivOp_nil (x : X) : listLineDerivOp ([] : List V) x = x := rfl

/-- The head of the list is the outermost derivative: $\partial_{v :: l} x = \partial_v (\partial_l
x)$. -/
@[simp] theorem listLineDerivOp_cons (v : V) (l : List V) (x : X) :
    listLineDerivOp (v :: l) x = ∂_{v} (listLineDerivOp l x) := rfl

/-- For a tuple $m \in V^n$, the iterated line derivative $\partial^m x$ is the iterated line
derivative along the list $[m_0, \dots, m_{n-1}]$ of its entries. -/
theorem iteratedLineDerivOp_eq_listLineDerivOp {n : ℕ} (m : Fin n → V) (x : X) :
    ∂^{m} x = listLineDerivOp (List.ofFn m) x := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedLineDerivOp_succ_left, List.ofFn_succ, listLineDerivOp_cons, ih]; rfl

variable (hcomm : ∀ (a b : V) (x : X), ∂_{a} (∂_{b} x) = ∂_{b} (∂_{a} x))

include hcomm

/-- Assume that any two line derivatives commute: $\partial_a \partial_b x = \partial_b \partial_a
x$ for all $a, b \in V$ and $x \in X$. If the list $l_1$ is a permutation of the list $l_2$,
then $\partial_{l_1} x = \partial_{l_2} x$ for every $x \in X$.

The proof is an induction on `List.Perm`, whose `swap` constructor is exactly the transposition
of the two outermost derivatives. -/
theorem listLineDerivOp_congr_perm {l₁ l₂ : List V} (h : l₁.Perm l₂) (x : X) :
    listLineDerivOp l₁ x = listLineDerivOp l₂ x := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [listLineDerivOp_cons, listLineDerivOp_cons, ih]
  | swap a b l => rw [listLineDerivOp_cons, listLineDerivOp_cons, listLineDerivOp_cons,
      listLineDerivOp_cons, hcomm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- Assume that any two line derivatives commute. If $m_1 \in V^{n_1}$ and $m_2 \in V^{n_2}$ are
tuples whose lists of entries are permutations of each other, then
$\partial^{m_1} x = \partial^{m_2} x$ for every $x \in X$. -/
theorem iteratedLineDerivOp_congr_perm {n₁ n₂ : ℕ} {m₁ : Fin n₁ → V} {m₂ : Fin n₂ → V}
    (h : (List.ofFn m₁).Perm (List.ofFn m₂)) (x : X) : ∂^{m₁} x = ∂^{m₂} x := by
  rw [iteratedLineDerivOp_eq_listLineDerivOp, iteratedLineDerivOp_eq_listLineDerivOp,
    listLineDerivOp_congr_perm hcomm h]

/-- Assume that any two line derivatives commute. Then $\partial_a (\partial^m x) = \partial^m
(\partial_a x)$ for every tuple $m \in V^n$, every $a \in V$ and every $x \in X$. -/
theorem lineDerivOp_iteratedLineDerivOp {n : ℕ} (m : Fin n → V) (a : V) (x : X) :
    ∂_{a} (∂^{m} x) = ∂^{m} (∂_{a} x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, hcomm, ih]

end LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

/-- Line derivatives of a Schwartz function commute: for a Schwartz function $f : E \to F$ and
$a, b \in E$, $\partial_a \partial_b f = \partial_b \partial_a f$. This is the symmetry of the
second derivative of a smooth function, `second_derivative_symmetric`. -/
theorem lineDerivOp_comm (a b : E) (f : 𝓢(E, F)) : ∂_{a} (∂_{b} f) = ∂_{b} (∂_{a} f) := by
  ext x
  have hd : ∀ y : E, HasFDerivAt (f : E → F) (fderiv ℝ (f : E → F) y) y := fun y ↦ f.hasFDerivAt y
  have hdiff : Differentiable ℝ (fderiv ℝ (f : E → F)) :=
    ((f.smooth ⊤).fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have hd2 : HasFDerivAt (fderiv ℝ (f : E → F)) (fderiv ℝ (fderiv ℝ (f : E → F)) x) x :=
    (hdiff x).hasFDerivAt
  have e : ∀ u v : E, (∂_{u} (∂_{v} f)) x = fderiv ℝ (fderiv ℝ (f : E → F)) x u v := by
    intro u v
    rw [lineDerivOp_apply_eq_fderiv]
    have h : HasFDerivAt (fun y ↦ fderiv ℝ (f : E → F) y v)
        ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ (f : E → F)) x)) x :=
      (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hd2
    have h2 : ((∂_{v} f : 𝓢(E, F)) : E → F) = fun y ↦ fderiv ℝ (f : E → F) y v := rfl
    rw [h2, h.fderiv]
    rfl
  rw [e, e, second_derivative_symmetric hd hd2 a b]

/-- The iterated line derivative of a Schwartz function is symmetric in its directions: if
$f : E \to F$ is a Schwartz function and $m_1 \in E^{n_1}$ and $m_2 \in E^{n_2}$ are tuples
whose lists of entries are permutations of each other, then
$\partial^{m_1} f = \partial^{m_2} f$.

Through `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`, this says that the $n$-th
derivative of a Schwartz function at a point is a symmetric multilinear map. Mathlib has this
only at order two (`ContDiffAt.isSymmSndFDerivAt`) or for analytic functions. -/
theorem iteratedLineDerivOp_congr_perm {n₁ n₂ : ℕ} {m₁ : Fin n₁ → E} {m₂ : Fin n₂ → E}
    (h : (List.ofFn m₁).Perm (List.ofFn m₂)) (f : 𝓢(E, F)) : ∂^{m₁} f = ∂^{m₂} f :=
  LineDeriv.iteratedLineDerivOp_congr_perm (fun a b x ↦ lineDerivOp_comm a b x) h f

end SchwartzMap

namespace TemperedDistribution

variable [NormedSpace ℂ F]

omit [NormedSpace ℝ F] in
/-- Line derivatives of a tempered distribution commute: for a tempered distribution $T$ with values
in a complex normed space and $a, b \in E$, $\partial_a \partial_b T = \partial_b \partial_a T$.
The line derivatives of $T$ are defined by composition with the line derivatives of the Schwartz
functions that $T$ is tested against, and those commute. -/
theorem lineDerivOp_comm (a b : E) (T : 𝓢'(E, F)) : ∂_{a} (∂_{b} T) = ∂_{b} (∂_{a} T) := by
  ext g
  simp only [lineDerivOp_apply_apply, map_neg, neg_neg, SchwartzMap.lineDerivOp_comm]

omit [NormedSpace ℝ F] in
/-- The iterated line derivative of a tempered distribution is symmetric in its directions: if
$m_1 \in E^{n_1}$ and $m_2 \in E^{n_2}$ are tuples whose lists of entries are permutations of
each other, then $\partial^{m_1} T = \partial^{m_2} T$ for every tempered distribution $T$. -/
theorem iteratedLineDerivOp_congr_perm {n₁ n₂ : ℕ} {m₁ : Fin n₁ → E} {m₂ : Fin n₂ → E}
    (h : (List.ofFn m₁).Perm (List.ofFn m₂)) (T : 𝓢'(E, F)) : ∂^{m₁} T = ∂^{m₂} T :=
  LineDeriv.iteratedLineDerivOp_congr_perm (fun a b x ↦ lineDerivOp_comm a b x) h T

omit [NormedSpace ℝ F] in
/-- **Integration by parts for a tempered distribution.** For a tempered distribution $T$, a tuple
$m \in E^n$ and a complex Schwartz function $g$,
$$(\partial^m T)(g) = (-1)^n \, T(\partial^m g).$$
-/
theorem iteratedLineDerivOp_apply {n : ℕ} (m : Fin n → E) (T : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) :
    (∂^{m} T) g = (-1 : ℂ) ^ n • T (∂^{m} g) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, lineDerivOp_apply_apply, ih,
      LineDeriv.iteratedLineDerivOp_neg, map_neg,
      ← LineDeriv.lineDerivOp_iteratedLineDerivOp
        (fun a b x ↦ SchwartzMap.lineDerivOp_comm a b x),
      ← LineDeriv.iteratedLineDerivOp_succ_left]
    rw [pow_succ]
    module

end TemperedDistribution

/-! ### A family of cut-offs -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A fixed smooth cut-off $\chi$ on $E$, equal to $1$ on the closed unit ball and $0$ outside the
ball of radius $2$. -/
private noncomputable def bump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The rescaled cut-off $x \mapsto \chi(x/(N + 1))$, equal to $1$ on the ball of radius $N + 1$ and
$0$ outside the ball of radius $2(N + 1)$. -/
private noncomputable def bumpScaled (N : ℕ) (x : E) : ℝ := bump E (((N : ℝ) + 1)⁻¹ • x)

/-- The cut-off $\chi$ as a Schwartz function, used only to name a bound for its derivatives. -/
private noncomputable def bumpSchwartz (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : 𝓢(E, ℝ) :=
  (bump E).hasCompactSupport.toSchwartzMap (bump E).contDiff

/-- The rescaled cut-offs are smooth. -/
private theorem contDiff_bumpScaled (N : ℕ) : ContDiff ℝ ∞ (bumpScaled (E := E) N) :=
  (bump E).contDiff.comp (contDiff_const_smul _)

/-- The rescaled cut-offs have compact support. -/
private theorem hasCompactSupport_bumpScaled (N : ℕ) :
    HasCompactSupport (bumpScaled (E := E) N) := by
  have hne : (((N : ℝ) + 1)⁻¹) ≠ 0 := by positivity
  exact (bump E).hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero _ hne)

/-- The rescaled cut-offs are at most $1$. -/
private theorem bumpScaled_le_one (N : ℕ) (x : E) : bumpScaled N x ≤ 1 := (bump E).le_one
/-- The rescaled cut-offs are nonnegative. -/
private theorem bumpScaled_nonneg (N : ℕ) (x : E) : 0 ≤ bumpScaled N x := (bump E).nonneg

/-- Near any fixed point, all but finitely many of the rescaled cut-offs are identically $1$. -/
private theorem bumpScaled_eventuallyEq_one (x : E) :
    ∀ᶠ N : ℕ in atTop, bumpScaled (E := E) N =ᶠ[𝓝 x] 1 := by
  filter_upwards [Filter.eventually_gt_atTop ⌈‖x‖⌉₊] with N hN
  have hx : ‖(((N : ℝ) + 1)⁻¹ • x)‖ < 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity),
      inv_mul_lt_one₀ (by positivity)]
    calc ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
      _ < (N : ℝ) := by exact_mod_cast hN
      _ < (N : ℝ) + 1 := by linarith
  have hcont : Continuous fun y : E ↦ ‖(((N : ℝ) + 1)⁻¹ • y)‖ := by fun_prop
  filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const hx] with y hy
  simp only [bumpScaled, Pi.one_apply]
  exact (bump E).one_of_mem_closedBall
    (by simpa [mem_closedBall, dist_zero_right, bump] using hy.le)

/-- The derivatives of the rescaled cut-offs are bounded uniformly in $N$ by the Schwartz seminorms
of $\chi$, because rescaling by a factor at most $1$ does not increase the norm of a derivative. -/
private theorem norm_iteratedFDeriv_bumpScaled_le (i N : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (bumpScaled (E := E) N) x‖
      ≤ SchwartzMap.seminorm ℝ 0 i (bumpSchwartz E) := by
  set c : ℝ := ((N : ℝ) + 1)⁻¹ with hc
  set L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hL
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc c * ‖ContinuousLinearMap.id ℝ E‖ ≤ c * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)
      _ ≤ 1 := by
          rw [mul_one, hc, inv_le_one₀ (by positivity)]
          linarith [Nat.cast_nonneg (α := ℝ) N]
  have heq : bumpScaled (E := E) N = (bump E : E → ℝ) ∘ L := rfl
  rw [heq, L.iteratedFDeriv_comp_right ((bump E).contDiff (n := (⊤ : ℕ∞))) x (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _j : Fin i, ‖L‖ ≤ 1 :=
    (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hLnorm)).trans (by simp)
  refine (mul_le_mul (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (bumpSchwartz E) i (L x))
    hprod (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (apply_nonneg _ _)).trans_eq (mul_one _)


end Cutoff

/-! ### Pairing Schwartz derivatives with $L^p$ functions -/

section Pairing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] {μ : Measure E} [μ.HasTemperateGrowth]
  {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

/-- Let $E$ be finite-dimensional with its Borel σ-algebra, let $\mu$ be a measure with temperate
growth, and let $p \ge 1$. For a Schwartz function $g : E \to V$, an order $j \in \mathbb{N}$
and $f \in L^p(\mu)$, the function $x \mapsto \|D^j g(x)\| \, \|f(x)\|$ is integrable.

The norm of the $j$-th derivative of a Schwartz function is bounded and integrable, hence in
every $L^q$, and Hölder's inequality applies. -/
theorem SchwartzMap.integrable_norm_iteratedFDeriv_mul_norm {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (g : 𝓢(E, V)) (j : ℕ) {f : E → F} (hf : MemLp f p μ) :
    Integrable (fun x ↦ ‖iteratedFDeriv ℝ j (g : E → V) x‖ * ‖f x‖) μ := by
  have := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  have hint : Integrable (fun x ↦ ‖iteratedFDeriv ℝ j (g : E → V) x‖) μ := by
    simpa using g.integrable_pow_mul_iteratedFDeriv μ 0 j
  have hmem : MemLp (fun x ↦ ‖iteratedFDeriv ℝ j (g : E → V) x‖) (1 - p⁻¹)⁻¹ μ :=
    Integrable.memLp_of_bound hint (C := SchwartzMap.seminorm ℝ 0 j g)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact g.norm_iteratedFDeriv_le_seminorm ℝ j x)
      (by simp)
  exact hmem.integrable_mul hf.norm

end Pairing

/-! ### Complex test functions -/

section ComplexTest

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [T2Space E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {n : ℕ} {m : Fin n → E} {f w : E → F} {μ : Measure E}


omit [MeasurableSpace E] [T2Space E] in
/-- For a smooth real function $\varphi$ and $c \in \mathbb{C}$, the $n$-th derivative of
$c \varphi$ is $c$ times the $n$-th derivative of $\varphi$. -/
private theorem iteratedFDeriv_const_mul_ofReal {φ : E → ℝ} (hs : ContDiff ℝ ∞ φ) (c : ℂ)
    (x : E) (y : Fin n → E) :
    iteratedFDeriv ℝ n (fun z ↦ c * ((φ z : ℝ) : ℂ)) x y
      = c * ((iteratedFDeriv ℝ n φ x y : ℝ) : ℂ) := by
  have h1 : (fun z ↦ c * ((φ z : ℝ) : ℂ)) = c • (Complex.ofRealCLM ∘ φ) := by
    funext z; simp [smul_eq_mul]
  have hs' : ContDiff ℝ (n : ℕ∞ω) φ := hs.of_le (by simp)
  have h2 : ContDiffAt ℝ n (Complex.ofRealCLM ∘ φ) x :=
    (Complex.ofRealCLM.contDiff.comp hs').contDiffAt
  rw [h1, iteratedFDeriv_const_smul_apply h2,
    Complex.ofRealCLM.iteratedFDeriv_comp_left hs'.contDiffAt le_rfl]
  simp

omit [OpensMeasurableSpace E] [T2Space E] [CompleteSpace F] in
/-- If $w$ is a weak derivative of $f$ along $m$ on the whole space, then the integration by parts
formula holds against $c \varphi$ for every smooth compactly supported real function $\varphi$
and every $c \in \mathbb{C}$. -/
private theorem HasWeakIteratedLineDerivOn.integral_smul_eq_const_mul
    (h : HasWeakIteratedLineDerivOn m f w ⊤ μ) {φ : E → ℝ} (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (c : ℂ) :
    ∫ x, iteratedFDeriv ℝ n (fun z ↦ c * ((φ z : ℝ) : ℂ)) x m • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x, (c * ((φ x : ℝ) : ℂ)) • w x ∂μ := by
  have key : ∫ x, iteratedFDeriv ℝ n φ x m • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x, φ x • w x ∂μ :=
    h.integral_smul_eq' ⟨φ, hs, hc, by simp⟩
  have e1 : ∀ (r : ℝ) (v : F), ((c * (r : ℂ)) • v) = c • (r • v) := by
    intro r v
    rw [mul_smul, ← Complex.coe_smul r v]
  calc ∫ x, iteratedFDeriv ℝ n (fun z ↦ c * ((φ z : ℝ) : ℂ)) x m • f x ∂μ
      = ∫ x, c • (iteratedFDeriv ℝ n φ x m • f x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        change iteratedFDeriv ℝ n (fun z ↦ c * ((φ z : ℝ) : ℂ)) x m • f x
          = c • (iteratedFDeriv ℝ n φ x m • f x)
        rw [iteratedFDeriv_const_mul_ofReal hs c x m, e1]
    _ = c • ∫ x, iteratedFDeriv ℝ n (φ : E → ℝ) x m • f x ∂μ := integral_smul _ _
    _ = c • ((-1 : ℝ) ^ n • ∫ x, φ x • w x ∂μ) := by rw [key]
    _ = (-1 : ℝ) ^ n • (c • ∫ x, (φ : E → ℝ) x • w x ∂μ) := smul_comm _ _ _
    _ = (-1 : ℝ) ^ n • ∫ x, (c * ((φ x : ℝ) : ℂ)) • w x ∂μ := by
        rw [← integral_smul]
        exact congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (e1 _ _).symm))

omit [T2Space E] [CompleteSpace F] in
/-- **The integration by parts formula of the weak derivative against complex test functions.** Let
$E$ be a real normed space whose open sets are measurable, and let $F$ be a complex normed
space. If $w$ is a weak derivative of $f : E \to F$ along the tuple $m \in E^n$ of directions on
the whole space $E$, then
$$\int D^n \psi(x)(m) \, f(x) \, d\mu(x) = (-1)^n \int \psi(x) \, w(x) \, d\mu(x)$$
for every smooth compactly supported $\psi : E \to \mathbb{C}$, not only for the real test
functions of the definition.

The proof splits $\psi$ into its real and imaginary parts. -/
theorem HasWeakIteratedLineDerivOn.integral_smul_eq_complex
    (h : HasWeakIteratedLineDerivOn m f w ⊤ μ) {ψ : E → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) :
    ∫ x, iteratedFDeriv ℝ n ψ x m • f x ∂μ = (-1 : ℝ) ^ n • ∫ x, ψ x • w x ∂μ := by
  set u : E → ℝ := fun z ↦ (ψ z).re with hu
  set v : E → ℝ := fun z ↦ (ψ z).im with hv
  have hsu : ContDiff ℝ ∞ u := Complex.reCLM.contDiff.comp hs
  have hsv : ContDiff ℝ ∞ v := Complex.imCLM.contDiff.comp hs
  have hcu : HasCompactSupport u := hc.comp_left (g := Complex.re) (by simp)
  have hcv : HasCompactSupport v := hc.comp_left (g := Complex.im) (by simp)
  set ψ₁ : E → ℂ := fun z ↦ (1 : ℂ) * ((u z : ℝ) : ℂ) with hψ₁
  set ψ₂ : E → ℂ := fun z ↦ Complex.I * ((v z : ℝ) : ℂ) with hψ₂
  have hsplit : ψ = ψ₁ + ψ₂ := by
    funext z
    simp only [hψ₁, hψ₂, hu, hv, Pi.add_apply, one_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (ψ z)).symm
  have hs₁ : ContDiff ℝ ∞ ψ₁ := by
    simpa [hψ₁] using (Complex.ofRealCLM.contDiff.comp hsu).const_smul (1 : ℂ)
  have hs₂ : ContDiff ℝ ∞ ψ₂ := by
    simpa [hψ₂, smul_eq_mul] using (Complex.ofRealCLM.contDiff.comp hsv).const_smul Complex.I
  -- integrability of the four pieces
  have iF : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Integrable (fun x ↦ iteratedFDeriv ℝ n φ x m • f x) μ := by
    intro φ hsφ hcφ
    have := h.integrable_smul
      ((⟨φ, hsφ, hcφ, by simp⟩ : 𝓓((⊤ : Opens E), ℝ)).iteratedFDerivApply n m)
    simpa [TestFunction.iteratedFDerivApply_apply] using this
  have iW : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Integrable (fun x ↦ φ x • w x) μ := fun φ hsφ hcφ ↦
    h.integrable_smul_weakDeriv ⟨φ, hsφ, hcφ, by simp⟩
  have e1 : ∀ (c : ℂ) (r : ℝ) (y : F), ((c * (r : ℂ)) • y) = c • (r • y) := by
    intro c r y; rw [mul_smul, ← Complex.coe_smul r y]
  have key₁ : ∀ x, iteratedFDeriv ℝ n ψ₁ x m • f x
      = (1 : ℂ) • (iteratedFDeriv ℝ n u x m • f x) := by
    intro x
    simp only [hψ₁]
    rw [iteratedFDeriv_const_mul_ofReal hsu 1 x m, e1]
  have key₂ : ∀ x, iteratedFDeriv ℝ n ψ₂ x m • f x
      = Complex.I • (iteratedFDeriv ℝ n v x m • f x) := by
    intro x
    simp only [hψ₂]
    rw [iteratedFDeriv_const_mul_ofReal hsv Complex.I x m, e1]
  have iF₁ : Integrable (fun x ↦ iteratedFDeriv ℝ n ψ₁ x m • f x) μ :=
    ((iF u hsu hcu).smul (1 : ℂ)).congr (Filter.Eventually.of_forall fun x ↦ (key₁ x).symm)
  have iF₂ : Integrable (fun x ↦ iteratedFDeriv ℝ n ψ₂ x m • f x) μ :=
    ((iF v hsv hcv).smul Complex.I).congr (Filter.Eventually.of_forall fun x ↦ (key₂ x).symm)
  have iW₁ : Integrable (fun x ↦ ψ₁ x • w x) μ :=
    ((iW u hsu hcu).smul (1 : ℂ)).congr (Filter.Eventually.of_forall fun x ↦ by
      simp only [hψ₁, Pi.smul_apply]; exact (e1 1 (u x) (w x)).symm)
  have iW₂ : Integrable (fun x ↦ ψ₂ x • w x) μ :=
    ((iW v hsv hcv).smul Complex.I).congr (Filter.Eventually.of_forall fun x ↦ by
      simp only [hψ₂, Pi.smul_apply]; exact (e1 Complex.I (v x) (w x)).symm)
  have hs₁' : ContDiff ℝ (n : ℕ∞ω) ψ₁ := hs₁.of_le (by simp)
  have hs₂' : ContDiff ℝ (n : ℕ∞ω) ψ₂ := hs₂.of_le (by simp)
  have hadd : ∀ x, iteratedFDeriv ℝ n ψ x m
      = iteratedFDeriv ℝ n ψ₁ x m + iteratedFDeriv ℝ n ψ₂ x m := fun x ↦ by
    rw [hsplit]
    exact congrFun (congrArg _ (iteratedFDeriv_add_apply (i := n)
      hs₁'.contDiffAt hs₂'.contDiffAt)) m
  calc ∫ x, iteratedFDeriv ℝ n ψ x m • f x ∂μ
      = ∫ x, (iteratedFDeriv ℝ n ψ₁ x m • f x + iteratedFDeriv ℝ n ψ₂ x m • f x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        change iteratedFDeriv ℝ n ψ x m • f x
          = iteratedFDeriv ℝ n ψ₁ x m • f x + iteratedFDeriv ℝ n ψ₂ x m • f x
        rw [hadd x, add_smul]
    _ = (∫ x, iteratedFDeriv ℝ n ψ₁ x m • f x ∂μ) + ∫ x, iteratedFDeriv ℝ n ψ₂ x m • f x ∂μ :=
        integral_add iF₁ iF₂
    _ = ((-1 : ℝ) ^ n • ∫ x, ψ₁ x • w x ∂μ) + (-1 : ℝ) ^ n • ∫ x, ψ₂ x • w x ∂μ := by
        rw [h.integral_smul_eq_const_mul hsu hcu 1, h.integral_smul_eq_const_mul hsv hcv Complex.I]
    _ = (-1 : ℝ) ^ n • ∫ x, ψ x • w x ∂μ := by
        rw [← smul_add, ← integral_add iW₁ iW₂]
        exact congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
          rw [hsplit]; exact (add_smul _ _ _).symm))

end ComplexTest

/-! ### The truncation argument -/

section Truncation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure E} [μ.HasTemperateGrowth] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {n : ℕ} {m : Fin n → E} {f w : E → F}

set_option maxHeartbeats 1000000 in
-- the proof carries a dominating function through two applications of dominated convergence, and
-- elaborating the bound needs more than the default budget
omit [CompleteSpace F] in
/-- **The integration by parts formula of the weak derivative holds against Schwartz functions.**
Let $E$ be finite-dimensional with its Borel σ-algebra, let $\mu$ be a measure with temperate
growth, let $p \ge 1$, and let $F$ be a complex normed space. If $w$ is a weak derivative of
$f : E \to F$ along the tuple $m \in E^n$ of directions on the whole space and
$f, w \in L^p(\mu)$, then
$$\int D^n g(x)(m) \, f(x) \, d\mu(x) = (-1)^n \int g(x) \, w(x) \, d\mu(x)$$
for every complex Schwartz function $g$, not only for the compactly supported test functions of
the definition.

The proof multiplies $g$ by the cut-offs $\chi(\cdot/(N+1))$, so that $\chi(\cdot/(N+1)) g$ is a
test function, and passes to the limit by dominated convergence. The derivatives of the cut-offs
are bounded uniformly in $N$, because rescaling by a factor at most $1$ does not increase them. -/
theorem HasWeakIteratedLineDerivOn.integral_smul_eq_schwartz
    (h : HasWeakIteratedLineDerivOn m f w ⊤ μ) (hf : MemLp f p μ) (hw : MemLp w p μ)
    (g : 𝓢(E, ℂ)) :
    ∫ x, iteratedFDeriv ℝ n (g : E → ℂ) x m • f x ∂μ = (-1 : ℝ) ^ n • ∫ x, g x • w x ∂μ := by
  set A : ℕ → ℝ := fun i ↦ SchwartzMap.seminorm ℝ 0 i (bumpSchwartz E) with hA
  set ψ : ℕ → E → ℂ := fun N x ↦ ((bumpScaled N x : ℝ) : ℂ) • (g x : ℂ) with hψ
  have hcofR : ∀ N, ContDiff ℝ ∞ fun x ↦ ((bumpScaled (E := E) N x : ℝ) : ℂ) := fun N ↦
    Complex.ofRealCLM.contDiff.comp (contDiff_bumpScaled N)
  have hgs : ContDiff ℝ ∞ (g : E → ℂ) := g.smooth'
  have hsψ : ∀ N, ContDiff ℝ ∞ (ψ N) := fun N ↦ (hcofR N).smul hgs
  have hcψ : ∀ N, HasCompactSupport (ψ N) := fun N ↦
    HasCompactSupport.smul_right
      ((hasCompactSupport_bumpScaled (E := E) N).comp_left (g := Complex.ofReal) (by simp))
  have key : ∀ N, ∫ x, iteratedFDeriv ℝ n (ψ N) x m • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x, ψ N x • w x ∂μ :=
    fun N ↦ h.integral_smul_eq_complex (hsψ N) (hcψ N)
  -- the dominating function
  set Φ : E → ℝ := fun x ↦ ∑ i ∈ Finset.range (n + 1),
      ((∏ j, ‖m j‖) * (n.choose i : ℝ) * A i) * ‖iteratedFDeriv ℝ (n - i) (g : E → ℂ) x‖ with hΦ
  have hbdd : ∀ N x, ‖iteratedFDeriv ℝ n (ψ N) x m • f x‖ ≤ Φ x * ‖f x‖ := by
    intro N x
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : ‖iteratedFDeriv ℝ n (ψ N) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i *
            ‖iteratedFDeriv ℝ (n - i) (g : E → ℂ) x‖ := by
      refine (norm_iteratedFDeriv_smul_le (hcofR N) hgs x (by simp)).trans ?_
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have : ‖iteratedFDeriv ℝ i (fun y ↦ ((bumpScaled (E := E) N y : ℝ) : ℂ)) x‖ ≤ A i := by
        rw [show (fun y ↦ ((bumpScaled (E := E) N y : ℝ) : ℂ))
            = Complex.ofRealLI ∘ bumpScaled N from rfl,
          Complex.ofRealLI.norm_iteratedFDeriv_comp_left
            ((contDiff_bumpScaled (E := E) N).contDiffAt) (by simp)]
        exact norm_iteratedFDeriv_bumpScaled_le i N x
      gcongr
    calc ‖iteratedFDeriv ℝ n (ψ N) x m‖ ≤ ‖iteratedFDeriv ℝ n (ψ N) x‖ * ∏ j, ‖m j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i *
            ‖iteratedFDeriv ℝ (n - i) (g : E → ℂ) x‖) * ∏ j, ‖m j‖ := by
          gcongr
      _ = Φ x := by
          rw [hΦ, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hΦint : Integrable (fun x ↦ Φ x * ‖f x‖) μ := by
    rw [hΦ]
    simp only [Finset.sum_mul]
    refine integrable_finsetSum _ fun i _ ↦ ?_
    simpa only [mul_assoc] using
      ((g.integrable_norm_iteratedFDeriv_mul_norm (n - i) hf).const_mul
        ((∏ j, ‖m j‖) * (n.choose i : ℝ) * A i))
  -- measurability of the truncated integrands
  have hmeasL : ∀ N, AEStronglyMeasurable (fun x ↦ iteratedFDeriv ℝ n (ψ N) x m • f x) μ :=
    fun N ↦ (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) ℂ m).continuous.comp
      ((hsψ N).continuous_iteratedFDeriv (by simp))).aestronglyMeasurable).smul
        hf.aestronglyMeasurable
  have hmeasR : ∀ N, AEStronglyMeasurable (fun x ↦ ψ N x • w x) μ :=
    fun N ↦ ((hsψ N).continuous.aestronglyMeasurable).smul hw.aestronglyMeasurable
  -- pointwise convergence: the cut-offs are eventually `1` near each point
  have hone : ∀ x : E, ∀ᶠ N in atTop, ψ N x = (g : E → ℂ) x := by
    intro x
    filter_upwards [bumpScaled_eventuallyEq_one (E := E) x] with N hN
    simp only [hψ, hN.eq_of_nhds, Pi.one_apply, Complex.ofReal_one, one_smul]
  have hlimL : ∀ x : E, ∀ᶠ N in atTop,
      iteratedFDeriv ℝ n (ψ N) x m • f x = iteratedFDeriv ℝ n (g : E → ℂ) x m • f x := by
    intro x
    filter_upwards [bumpScaled_eventuallyEq_one (E := E) x] with N hN
    have hEq : ψ N =ᶠ[𝓝 x] (g : E → ℂ) := by
      filter_upwards [hN] with y hy
      simp only [hψ, hy, Pi.one_apply, Complex.ofReal_one, one_smul]
    rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds]
  have hL : Tendsto (fun N ↦ ∫ x, iteratedFDeriv ℝ n (ψ N) x m • f x ∂μ) atTop
      (𝓝 (∫ x, iteratedFDeriv ℝ n (g : E → ℂ) x m • f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x ↦ Φ x * ‖f x‖) hmeasL hΦint
      (fun N ↦ Filter.Eventually.of_forall (hbdd N))
      (Filter.Eventually.of_forall fun x ↦ by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [hlimL x] with N hN
        exact hN.symm)
  have hRint : Integrable (fun x ↦ ‖(g : E → ℂ) x‖ * ‖w x‖) μ := by
    simpa using g.integrable_norm_iteratedFDeriv_mul_norm 0 hw
  have hR : Tendsto (fun N ↦ ∫ x, ψ N x • w x ∂μ) atTop (𝓝 (∫ x, (g : E → ℂ) x • w x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖(g : E → ℂ) x‖ * ‖w x‖) hmeasR
      hRint (fun N ↦ Filter.Eventually.of_forall fun x ↦ ?_)
      (Filter.Eventually.of_forall fun x ↦ by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [hone x] with N hN
        rw [hN])
    rw [norm_smul, norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpScaled_nonneg N x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (bumpScaled_le_one N x)
  refine tendsto_nhds_unique hL ?_
  simp only [key]
  exact hR.const_smul ((-1 : ℝ) ^ n)

end Truncation

/-! ### The bridge -/

section Bridge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure E} [μ.HasTemperateGrowth] [IsLocallyFiniteMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {n : ℕ} {m : Fin n → E}

/-- For $y$ in a complex normed space, $(-1)^n \big((-1)^n y\big) = y$, where the first sign is a
complex scalar and the second a real one. -/
private theorem neg_one_pow_smul_neg_one_pow_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] (n : ℕ) (y : G) : ((-1 : ℂ) ^ n) • (((-1 : ℝ) ^ n) • y) = y := by
  rw [← Complex.coe_smul, smul_smul]
  push_cast
  rw [← mul_pow]
  norm_num

omit [FiniteDimensional ℝ E] in
/-- **A distributional derivative of an $L^p$ function is a weak derivative.** Let $E$ have its
Borel σ-algebra, let $\mu$ be a locally finite measure with temperate growth, let $p \ge 1$, and
let $F$ be a complex Banach space. For $u, v \in L^p(\mu; F)$ and a tuple $m \in E^n$, if
$\partial^m T_u = T_v$, then $v$ is a weak derivative of $u$ along $m$ on the whole space.

This direction is immediate, because a test function is a Schwartz function. The distribution
$T_u$ is the coercion of $u$ to `𝓢'(E, F)`. -/
theorem MeasureTheory.Lp.hasWeakIteratedLineDerivOn_of_iteratedLineDerivOp_eq
    {u v : Lp F p μ} (h : ∂^{m} (u : 𝓢'(E, F)) = (v : 𝓢'(E, F))) :
    HasWeakIteratedLineDerivOn m (u : E → F) (v : E → F) ⊤ μ where
  locallyIntegrableOn := ((Lp.memLp u).locallyIntegrable Fact.out).locallyIntegrableOn _
  locallyIntegrableOn_weakDeriv := ((Lp.memLp v).locallyIntegrable Fact.out).locallyIntegrableOn _
  integral_smul_eq φ := by
    have hcs : HasCompactSupport (fun x ↦ ((φ x : ℝ) : ℂ)) :=
      φ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
    have hsm : ContDiff ℝ ∞ (fun x ↦ ((φ x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp φ.contDiff
    set g : 𝓢(E, ℂ) := hcs.toSchwartzMap hsm with hg
    have hgv : (g : E → ℂ) = fun x ↦ ((φ x : ℝ) : ℂ) := rfl
    have happ := congrArg (fun T : 𝓢'(E, F) ↦ T g) h
    simp only [TemperedDistribution.iteratedLineDerivOp_apply,
      Lp.toTemperedDistribution_apply] at happ
    have hder : ∀ x, (∂^{m} g : 𝓢(E, ℂ)) x = ((iteratedFDeriv ℝ n (φ : E → ℝ) x m : ℝ) : ℂ) := by
      intro x
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, hgv,
        show (fun y ↦ ((φ y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ (φ : E → ℝ) from rfl,
        Complex.ofRealCLM.iteratedFDeriv_comp_left (φ.contDiff.of_le (by simp)).contDiffAt le_rfl]
      simp
    have e1 : ∫ x, (∂^{m} g : 𝓢(E, ℂ)) x • (u : E → F) x ∂μ
        = ∫ x, iteratedFDeriv ℝ n (φ : E → ℝ) x m • (u : E → F) x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
        change (∂^{m} g : 𝓢(E, ℂ)) x • (u : E → F) x
          = iteratedFDeriv ℝ n (φ : E → ℝ) x m • (u : E → F) x
        rw [hder x, Complex.coe_smul])
    have e2 : ∫ x, (g : E → ℂ) x • (v : E → F) x ∂μ = ∫ x, (φ : E → ℝ) x • (v : E → F) x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
        change (g : E → ℂ) x • (v : E → F) x = (φ : E → ℝ) x • (v : E → F) x
        rw [hgv, Complex.coe_smul])
    rw [e1] at happ
    rw [e2] at happ
    have hres : ∀ (F' : E → F), ∫ x in ((⊤ : Opens E) : Set E), F' x ∂μ = ∫ x, F' x ∂μ := by
      intro F'
      rw [show ((⊤ : Opens E) : Set E) = Set.univ from rfl, Measure.restrict_univ]
    rw [hres, hres, ← happ, smul_comm, neg_one_pow_smul_neg_one_pow_smul]

omit [IsLocallyFiniteMeasure μ] in
/-- **A weak derivative of an $L^p$ function is a distributional derivative.** Let $E$ be
finite-dimensional with its Borel σ-algebra, let $\mu$ be a measure with temperate growth, let
$p \ge 1$, and let $F$ be a complex Banach space. For $u, v \in L^p(\mu; F)$ and a tuple
$m \in E^n$, if $v$ is a weak derivative of $u$ along $m$ on the whole space, then
$\partial^m T_u = T_v$.

This is the direction that needs the truncation argument of
`HasWeakIteratedLineDerivOn.integral_smul_eq_schwartz`. -/
theorem MeasureTheory.Lp.iteratedLineDerivOp_eq_of_hasWeakIteratedLineDerivOn
    {u v : Lp F p μ} (h : HasWeakIteratedLineDerivOn m (u : E → F) (v : E → F) ⊤ μ) :
    ∂^{m} (u : 𝓢'(E, F)) = (v : 𝓢'(E, F)) := by
  ext g
  rw [TemperedDistribution.iteratedLineDerivOp_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hsch := h.integral_smul_eq_schwartz (Lp.memLp u) (Lp.memLp v) g
  have e1 : ∫ x, (∂^{m} g : 𝓢(E, ℂ)) x • (u : E → F) x ∂μ
      = ∫ x, iteratedFDeriv ℝ n (g : E → ℂ) x m • (u : E → F) x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      change (∂^{m} g : 𝓢(E, ℂ)) x • (u : E → F) x
        = iteratedFDeriv ℝ n (g : E → ℂ) x m • (u : E → F) x
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv])
  rw [e1, hsch, neg_one_pow_smul_neg_one_pow_smul]

/-- **The weak and the distributional derivative agree on the whole space.** Let $E$ be
finite-dimensional with its Borel σ-algebra, let $\mu$ be a locally finite measure with
temperate growth, let $p \ge 1$, and let $F$ be a complex Banach space. For
$u, v \in L^p(\mu; F)$ and a tuple $m \in E^n$,
$$\partial^m T_u = T_v
  \iff v \text{ is a weak derivative of } u \text{ along } m \text{ on } E.$$
The left side is the derivative of the tempered distribution $T_u$, tested against Schwartz
functions. The right side is the weak derivative of Definition 7.1.3 of [han2009theoretical],
defined by integration by parts against $C_0^\infty(E)$.

The weak derivative is `HasWeakIteratedLineDerivOn` with $\Omega = E$. -/
theorem MeasureTheory.Lp.iteratedLineDerivOp_eq_iff_hasWeakIteratedLineDerivOn
    (u v : Lp F p μ) (m : Fin n → E) :
    ∂^{m} (u : 𝓢'(E, F)) = (v : 𝓢'(E, F)) ↔
      HasWeakIteratedLineDerivOn m (u : E → F) (v : E → F) ⊤ μ :=
  ⟨fun h ↦ Lp.hasWeakIteratedLineDerivOn_of_iteratedLineDerivOp_eq h,
   fun h ↦ Lp.iteratedLineDerivOp_eq_of_hasWeakIteratedLineDerivOn h⟩

end Bridge


/-! ### Bessel potential spaces of integer order -/

section Bessel

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

section normed

variable [NormedSpace ℂ F]

/-- For $r \ge 0$,
$$(1 + r)^{1/2} = (1 + r)^{-1/2} + r (1 + r)^{-1/2}.$$
This is the scalar identity behind the splitting of the Bessel potential of order $1$. After
factoring out $(1 + r)^{-1/2}$ on the right, it says $(1 + r)^{1/2} = (1 + r)^{-1/2} (1 + r)$. -/
theorem one_add_rpow_half_eq_add {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ (1 / 2 : ℝ) = (1 + r) ^ (-1 / 2 : ℝ) + r * (1 + r) ^ (-1 / 2 : ℝ) := by
  have hp : (0 : ℝ) < 1 + r := by linarith
  have h : (1 + r) ^ (-1 / 2 : ℝ) + r * (1 + r) ^ (-1 / 2 : ℝ)
      = (1 + r) ^ (1 : ℝ) * (1 + r) ^ (-1 / 2 : ℝ) := by
    rw [Real.rpow_one]; ring
  rw [h, ← Real.rpow_add hp]
  norm_num

/-- The Fourier multiplier operator on tempered distributions is additive in its symbol: for
functions $g_1, g_2 : E \to \mathbb{C}$ of temperate growth, the multiplier with symbol
$g_1 + g_2$ is the sum of the multipliers with symbols $g_1$ and $g_2$. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F (g₁ + g₂) f =
      fourierMultiplierCLM F g₁ f + fourierMultiplierCLM F g₂ f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_add hg₁ hg₂]

/-- For a tempered distribution $f$, the Bessel potential of order $-1$ of the Laplacian of $f$ is
$$\mathcal{B}_{-1}(\Delta f) = -(2\pi)^2 \, M_\sigma f,
  \qquad \sigma(\xi) = |\xi|^2 (1 + |\xi|^2)^{-1/2},$$
where $\mathcal{B}_s$ is `TemperedDistribution.besselPotential E F s` and $M_\sigma$ is the
Fourier multiplier with symbol $\sigma$.

The factor $-(2\pi)^2$ is the one in `TemperedDistribution.laplacian_eq_fourierMultiplierCLM`.
It reflects the convention that Mathlib uses for the Fourier transform, for which the symbol of
the Laplacian is $-(2\pi)^2 |\xi|^2$ and not $-|\xi|^2$. -/
theorem besselPotential_neg_one_laplacian_eq (f : 𝓢'(E, F)) :
    besselPotential E F (-1) (Δ f) = (-(2 * π) ^ 2 : ℂ) •
      fourierMultiplierCLM F
        (fun x ↦ Complex.ofReal (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))) f := by
  rw [laplacian_eq_fourierMultiplierCLM, besselPotential,
    ContinuousLinearMap.map_smul_of_tower,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop),
    ← Complex.coe_smul (-(2 * π) ^ 2)]
  push_cast
  congr

/-- For a tempered distribution $f$, the Bessel potential of order $1$ splits as
$$\mathcal{B}_1 f = \mathcal{B}_{-1} f - (2\pi)^{-2} \, \mathcal{B}_{-1}(\Delta f).$$
The minus sign is there because the symbol of $\Delta$ is $-(2\pi)^2 |\xi|^2$, so that
subtracting the second term adds $|\xi|^2$ to the symbol.

On the Fourier side this is the identity $(1 + |\xi|^2)^{1/2} = (1 + |\xi|^2)^{-1/2} + |\xi|^2
(1 + |\xi|^2)^{-1/2}$ of `TemperedDistribution.one_add_rpow_half_eq_add`. -/
theorem besselPotential_one_eq (f : 𝓢'(E, F)) :
    besselPotential E F 1 f =
      besselPotential E F (-1) f - (((2 * π) ^ 2 : ℝ)⁻¹ : ℂ) • besselPotential E F (-1) (Δ f) := by
  have h₁ : (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))).HasTemperateGrowth := by
    fun_prop
  have h₂ : (fun x : E ↦
      Complex.ofReal (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))).HasTemperateGrowth := by
    fun_prop
  have hsym : (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2)))
      = (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
        + (fun x : E ↦ Complex.ofReal (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))) := by
    funext x
    simp only [Pi.add_apply, ← Complex.ofReal_add, Complex.ofReal_inj]
    exact one_add_rpow_half_eq_add (r := ‖x‖ ^ 2) (by positivity)
  rw [besselPotential_neg_one_laplacian_eq, smul_smul,
    show ((((2 * π) ^ 2 : ℝ)⁻¹ : ℂ)) * (-(2 * π) ^ 2 : ℂ) = -1 by
      push_cast; field_simp,
    neg_one_smul, sub_neg_eq_add, besselPotential, besselPotential,
    ← fourierMultiplierCLM_add h₁ h₂, hsym]

variable [CompleteSpace F]

/-- Let $F$ be a complex Banach space, $s \in \mathbb{R}$ and $p \ge 1$. A finite sum of tempered
distributions in $H^{s,p}$ lies in $H^{s,p}$. -/
theorem MemSobolev.sum {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {t : Finset ι} {g : ι → 𝓢'(E, F)}
    (h : ∀ i ∈ t, MemSobolev s p (g i)) : MemSobolev s p (∑ i ∈ t, g i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi ↦ h i (by simp [hi]))

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Let $F$ be a complex Hilbert space, let $b$ be an orthonormal basis of $E$ indexed by a finite
type, and let $s \in \mathbb{R}$. If $f$ is a tempered distribution with
$\partial_{b_i} f \in H^s$ for every $i$, then $\Delta f \in H^{s-1}$.

This refines `TemperedDistribution.MemSobolev.laplacian`, which concludes only
$\Delta f \in H^{s-2}$ from $f \in H^s$; here the hypothesis is one derivative stronger. -/
theorem MemSobolev.laplacian_of_lineDerivOp [Fintype ι] (b : OrthonormalBasis ι ℝ E) {s : ℝ}
    {f : 𝓢'(E, F)} (hd : ∀ i, MemSobolev s 2 (∂_{b i} f)) : MemSobolev (s - 1) 2 (Δ f) := by
  rw [laplacian_eq_sum b]
  exact MemSobolev.sum fun i _ ↦ (hd i).lineDerivOp

/-- Let $F$ be a complex Hilbert space, let $b$ be an orthonormal basis of $E$ indexed by a finite
type, and let $s \in \mathbb{R}$. If a tempered distribution $f$ lies in $H^s$ and
$\partial_{b_i} f \in H^s$ for every $i$, then $f \in H^{s+1}$.

This is the converse of `TemperedDistribution.MemSobolev.lineDerivOp`. It is the inductive step
in the identification of $H^k$ with the space of tempered distributions whose derivatives of
order at most $k$ are square integrable; see W. McLean, *Strongly Elliptic Systems and Boundary
Integral Equations*, Cambridge University Press, 2000, Chapter 3. -/
theorem MemSobolev.of_lineDerivOp [Fintype ι] (b : OrthonormalBasis ι ℝ E) {s : ℝ} {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) (hd : ∀ i, MemSobolev s 2 (∂_{b i} f)) : MemSobolev (s + 1) 2 f := by
  have h₁ : MemSobolev s 2 (besselPotential E F (-1) f) := by
    rw [memSobolev_besselPotential_iff]
    exact hf.mono (by linarith)
  have h₂ : MemSobolev s 2 (besselPotential E F (-1) (Δ f)) := by
    rw [memSobolev_besselPotential_iff, show (-1 : ℝ) + s = s - 1 by ring]
    exact MemSobolev.laplacian_of_lineDerivOp b hd
  have h : MemSobolev s 2 (besselPotential E F 1 f) := by
    rw [besselPotential_one_eq]
    exact h₁.sub (h₂.smul _)
  rwa [memSobolev_besselPotential_iff, add_comm] at h

/-- **The iterated directional derivative lowers the Sobolev order by the number of derivatives.**
Let $F$ be a complex Hilbert space and $s \in \mathbb{R}$. If a tempered distribution $f$ lies
in $H^s$, then $\partial^m f \in H^{s-n}$ for every $n \in \mathbb{N}$ and every tuple
$m \in E^n$.

This is `TemperedDistribution.MemSobolev.lineDerivOp`, iterated. -/
theorem MemSobolev.iteratedLineDerivOp {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    ∀ (n : ℕ) (m : Fin n → E), MemSobolev (s - n) 2 (∂^{m} f) := by
  intro n
  induction n with
  | zero => intro m; simpa using hf
  | succ n ih =>
    intro m
    rw [LineDeriv.iteratedLineDerivOp_succ_left,
      show s - ((n + 1 : ℕ) : ℝ) = s - (n : ℝ) - 1 by push_cast; ring]
    exact (ih (Fin.tail m)).lineDerivOp

/-- Let $F$ be a complex Hilbert space and $k \in \mathbb{N}$. If $f$ is a tempered distribution
such that, for every $n \le k$ and every tuple $m \in E^n$ of directions, $\partial^m f$ is an
$L^2$ function (that is, lies in $H^0$), then $f \in H^k$.

Together with `TemperedDistribution.MemSobolev.lineDerivOp`, which gives the converse, this
identifies the Bessel potential space of integer order $k$ with the Sobolev space defined by the
square integrability of the weak derivatives of order at most $k$; see W. McLean, *Strongly
Elliptic Systems and Boundary Integral Equations*, Cambridge University Press, 2000, Chapter 3. -/
theorem MemSobolev.of_iteratedLineDerivOp {k : ℕ} {f : 𝓢'(E, F)}
    (h : ∀ n ≤ k, ∀ m : Fin n → E, MemSobolev 0 2 (∂^{m} f)) :
    MemSobolev (k : ℝ) 2 f := by
  induction k generalizing f with
  | zero => simpa using h 0 le_rfl (fun i ↦ i.elim0)
  | succ k ih =>
    set b := stdOrthonormalBasis ℝ E with hb
    have hf : MemSobolev (k : ℝ) 2 f := ih fun n hn m ↦ h n (by omega) m
    have hd : ∀ i, MemSobolev (k : ℝ) 2 (∂_{b i} f) := by
      intro i
      refine ih fun n hn m ↦ ?_
      have hm := h (n + 1) (by omega) (Fin.snoc m (b i))
      rwa [LineDeriv.iteratedLineDerivOp_succ_right, Fin.init_snoc, Fin.snoc_last] at hm
    have hk := MemSobolev.of_lineDerivOp b hf hd
    rwa [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring] at hk

end inner

end TemperedDistribution

end Bessel

/-! ### The complexification of an $L^p$ function -/

/-- Let $f$ be a real function on a measurable space. Then $x \mapsto f(x) \in \mathbb{C}$ lies in
$L^p$ if and only if $f$ does. The embedding $\mathbb{R} \to \mathbb{C}$ is a continuous linear
map, and so is the real part, which inverts it on real scalars. -/
theorem MeasureTheory.memLp_ofReal_iff {X : Type*} [MeasurableSpace X] {f : X → ℝ} {p : ℝ≥0∞}
    {μ : Measure X} : MemLp (fun x ↦ ((f x : ℝ) : ℂ)) p μ ↔ MemLp f p μ :=
  ⟨fun h ↦ by simpa [Function.comp_def] using Complex.reCLM.comp_memLp' h, fun h ↦ h.ofReal⟩

/-! ### From multi-index weak derivatives to the Bessel potential space -/

section Transfer

variable {ι E : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open TemperedDistribution in
omit [LinearOrder ι] in
/-- Let $F$ be a complex Hilbert space, let $b$ be an orthonormal basis of $E$ indexed by a finite
type $\iota$, and let $k \in \mathbb{N}$. If $f$ is a tempered distribution such that, for every
$n \le k$ and every $m : \{0, \dots, n-1\} \to \iota$, the derivative $\partial_{b_{m_0}} \cdots
\partial_{b_{m_{n-1}}} f$ along basis vectors, in any order, is an $L^2$ function, then
$f \in H^k$.

This is the basis-indexed form of `TemperedDistribution.MemSobolev.of_iteratedLineDerivOp`. -/
theorem TemperedDistribution.MemSobolev.of_iteratedLineDerivOp_basis (b : OrthonormalBasis ι ℝ E)
    {k : ℕ} {f : 𝓢'(E, F)}
    (h : ∀ n ≤ k, ∀ m : Fin n → ι, MemSobolev 0 2 (∂^{fun j ↦ b (m j)} f)) :
    MemSobolev (k : ℝ) 2 f := by
  induction k generalizing f with
  | zero => simpa using h 0 le_rfl (fun i ↦ i.elim0)
  | succ k ih =>
    have hf : MemSobolev (k : ℝ) 2 f := ih fun n hn m ↦ h n (by omega) m
    have hd : ∀ i, MemSobolev (k : ℝ) 2 (∂_{b i} f) := by
      intro i
      refine ih fun n hn m ↦ ?_
      set m' : Fin (n + 1) → ι := Fin.snoc m i with hm'
      have hsn : (fun j ↦ b (m' j)) = Fin.snoc (fun j ↦ b (m j)) (b i) := by
        funext j
        refine Fin.lastCases ?_ ?_ j <;> simp [hm']
      have hm := h (n + 1) (by omega) m'
      rw [hsn, LineDeriv.iteratedLineDerivOp_succ_right, Fin.init_snoc, Fin.snoc_last] at hm
      exact hm
    have hk := MemSobolev.of_lineDerivOp b hf hd
    rwa [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring] at hk

end Transfer

/-! ### The two descriptions of $H^k(\mathbb{R}^d)$ agree -/

section Agree

variable {ι E : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open TemperedDistribution

/-- Let $E$ be a finite-dimensional real inner product space with its Borel σ-algebra and Lebesgue
measure, let $b$ be an orthonormal basis of $E$ indexed by a finite linearly ordered type, let
$k \in \mathbb{N}$, and let $u \in L^2(E; \mathbb{C})$. If $u$ has weak derivatives
$\partial^\alpha u \in L^2(E)$ on $E$ for all multi-indices $\alpha$ with $|\alpha| \le k$,
taken with respect to $b$, then $T_u \in H^k$. -/
theorem TemperedDistribution.MemSobolev.of_memSobolevMultiIndex (b : OrthonormalBasis ι ℝ E)
    {k : ℕ} {u : Lp ℂ 2 (volume : Measure E)}
    (h : MemSobolevMultiIndex b.toBasis (u : E → ℂ) k 2 ⊤ volume) :
    MemSobolev (k : ℝ) 2 (u : 𝓢'(E, ℂ)) := by
  refine MemSobolev.of_iteratedLineDerivOp_basis b fun n hn m ↦ ?_
  obtain ⟨α, hα, hperm⟩ : ∃ α : ι → ℕ, ∑ i, α i = n ∧
      (List.ofFn fun j ↦ (b : ι → E) (m j)).Perm (multiIndexDirections (b : ι → E) α) :=
    ⟨multiIndexCount m, sum_multiIndexCount m,
      multiIndexDirections_multiIndexCount_perm (b : ι → E) m⟩
  obtain ⟨w, hw, hwL⟩ := h.exists_hasWeakIteratedLineDerivOn (α := α) (by omega)
  simp only [OrthonormalBasis.coe_toBasis] at hw
  rw [show ((⊤ : Opens E) : Set E) = Set.univ from rfl, Measure.restrict_univ] at hwL
  have hw' : HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α) (u : E → ℂ)
      ((hwL.toLp w : Lp ℂ 2 (volume : Measure E)) : E → ℂ) ⊤ volume :=
    hw.congr_ae (Filter.EventuallyEq.refl _ _) (by
      rw [show ((⊤ : Opens E) : Set E) = Set.univ from rfl, Measure.restrict_univ]
      exact hwL.coeFn_toLp.symm)
  have hperm' : (List.ofFn fun j ↦ (b : ι → E) (m j)).Perm
      (List.ofFn (multiIndexTuple (b : ι → E) α)) := by
    rw [← multiIndexDirections_eq_ofFn]; exact hperm
  rw [TemperedDistribution.iteratedLineDerivOp_congr_perm hperm',
    MeasureTheory.Lp.iteratedLineDerivOp_eq_of_hasWeakIteratedLineDerivOn hw']
  exact memSobolev_zero_iff.2 ⟨_, rfl⟩

/-- Let $E$ be a finite-dimensional real inner product space with its Borel σ-algebra and Lebesgue
measure, let $b$ be an orthonormal basis of $E$ indexed by a finite linearly ordered type, let
$k \in \mathbb{N}$, and let $u \in L^2(E; \mathbb{C})$. If $T_u \in H^k$, then $u$ has weak
derivatives $\partial^\alpha u \in L^2(E)$ on $E$ for all multi-indices $\alpha$ with
$|\alpha| \le k$, taken with respect to $b$. -/
theorem TemperedDistribution.MemSobolev.memSobolevMultiIndex (b : OrthonormalBasis ι ℝ E) {k : ℕ}
    {u : Lp ℂ 2 (volume : Measure E)} (h : MemSobolev (k : ℝ) 2 (u : 𝓢'(E, ℂ))) :
    MemSobolevMultiIndex b.toBasis (u : E → ℂ) k 2 ⊤ volume := by
  have huniv : ((⊤ : Opens E) : Set E) = Set.univ := rfl
  refine ⟨by rw [huniv, Measure.restrict_univ]; exact Lp.memLp u, fun α hα ↦ ?_⟩
  have hmem : MemSobolev 0 2 (∂^{multiIndexTuple (b : ι → E) α} (u : 𝓢'(E, ℂ))) := by
    refine (h.iteratedLineDerivOp _ (multiIndexTuple (b : ι → E) α)).mono ?_
    have : ((∑ i, α i : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hα
    linarith
  obtain ⟨wL, hwL⟩ := memSobolev_zero_iff.1 hmem
  refine ⟨(wL : E → ℂ), ?_, by rw [huniv, Measure.restrict_univ]; exact Lp.memLp wL⟩
  simpa only [OrthonormalBasis.coe_toBasis] using
    MeasureTheory.Lp.hasWeakIteratedLineDerivOn_of_iteratedLineDerivOp_eq hwL

/-- **The Sobolev space of integer order on the whole space, defined by the weak derivatives, is
Mathlib's Bessel potential space.** Let $E$ be a finite-dimensional real inner product space
with its Borel σ-algebra and Lebesgue measure, let $b$ be an orthonormal basis of $E$ indexed by
a finite linearly ordered type, let $k \in \mathbb{N}$, and let $u \in L^2(E; \mathbb{C})$. Then
$T_u \in H^k(E)$ if and only if $u$ has weak derivatives $\partial^\alpha u \in L^2(E)$ for all
multi-indices $\alpha$ with $|\alpha| \le k$, taken with respect to $b$. This is the statement
of Theorem 7.4.1 of [han2009theoretical] when its $H^k(\mathbb{R}^d)$ is unfolded on both sides;
the norms are not compared here.

The weak-derivative side is `MemSobolevMultiIndex b.toBasis u k 2 ⊤ volume`, with $\Omega = E$
and the Lebesgue measure `volume`. -/
theorem TemperedDistribution.memSobolev_iff_memSobolevMultiIndex (b : OrthonormalBasis ι ℝ E)
    {k : ℕ} {u : Lp ℂ 2 (volume : Measure E)} :
    MemSobolev (k : ℝ) 2 (u : 𝓢'(E, ℂ)) ↔
      MemSobolevMultiIndex b.toBasis (u : E → ℂ) k 2 ⊤ volume :=
  ⟨TemperedDistribution.MemSobolev.memSobolevMultiIndex b,
    TemperedDistribution.MemSobolev.of_memSobolevMultiIndex b⟩

end Agree

/-! ### Complexification -/

section Complexify

variable {ι E : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **A real function lies in $W^{k,p}(\Omega)$ if and only if its complexification does.** Let $E$
be a real normed space whose open sets are measurable, with a basis $b$ indexed by a finite
linearly ordered type, and let $f : E \to \mathbb{R}$. Then $x \mapsto f(x) \in \mathbb{C}$
satisfies `MemSobolevMultiIndex` for $b$, $k$, $p$, $\Omega$ and $\mu$ if and only if $f$ does.

The embedding $\mathbb{R} \to \mathbb{C}$ and the real part are continuous $\mathbb{R}$-linear
maps, and composing with them takes each statement to the other. -/
theorem memSobolevMultiIndex_ofReal_iff {b : Module.Basis ι ℝ E} {f : E → ℝ} {k : ℕ} {p : ℝ≥0∞}
    {Ω : Opens E} {μ : Measure E} :
    MemSobolevMultiIndex b (fun x ↦ ((f x : ℝ) : ℂ)) k p Ω μ ↔
      MemSobolevMultiIndex b f k p Ω μ := by
  constructor
  · rintro ⟨hL, hd⟩
    refine ⟨by simpa [Function.comp_def] using (Complex.reCLM.comp_memLp' hL), fun α hα ↦ ?_⟩
    obtain ⟨w, hw, hwL⟩ := hd α hα
    refine ⟨fun x ↦ (w x).re, ?_,
      by simpa [Function.comp_def] using Complex.reCLM.comp_memLp' hwL⟩
    simpa using hw.comp_continuousLinearMap Complex.reCLM
  · rintro ⟨hL, hd⟩
    refine ⟨hL.ofReal, fun α hα ↦ ?_⟩
    obtain ⟨w, hw, hwL⟩ := hd α hα
    exact ⟨fun x ↦ ((w x : ℝ) : ℂ), hw.comp_continuousLinearMap Complex.ofRealCLM, hwL.ofReal⟩

end Complexify

/-! ### Multiplying an $L^2$ function by a symbol -/

section SmulLeft

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Let $g : E \to \mathbb{C}$ have temperate growth, and let $u, w \in L^2(E; \mathbb{C})$. If
$w = g u$ almost everywhere, then $T_w$ is the product of the tempered distribution $T_u$ with
$g$, `TemperedDistribution.smulLeftCLM ℂ g`. -/
theorem toTemperedDistribution_eq_smulLeftCLM {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {u w : Lp ℂ 2 (volume : Measure E)}
    (h : (w : E → ℂ) =ᵐ[volume] fun ξ ↦ g ξ * (u : E → ℂ) ξ) :
    (w : 𝓢'(E, ℂ)) = smulLeftCLM ℂ g (u : 𝓢'(E, ℂ)) := by
  ext f
  rw [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [h] with ξ hξ
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply hg]
  simp only [smul_eq_mul]
  ring

end SmulLeft

/-! ### The symbol of an iterated directional derivative -/

section Symbol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **symbol** of the iterated directional derivative $\partial^m$ along the tuple $m \in E^n$:
the function
$$\sigma_m(\xi) = \prod_{j} \langle \xi, m_j \rangle,$$
with values in $\mathbb{C}$. The Fourier transform of $\partial^m f$ is $(2\pi i)^n \sigma_m$
times the Fourier transform of $f$ (`fourier_iteratedLineDerivOp_eq`). -/
def lineSymbol {n : ℕ} (m : Fin n → E) : E → ℂ := fun ξ ↦ ∏ j, ((inner ℝ ξ (m j) : ℝ) : ℂ)

/-- The symbol of $\partial^m$ at $\xi$ is $\sigma_m(\xi) = \prod_j \langle \xi, m_j \rangle$. -/
@[simp]
theorem lineSymbol_apply {n : ℕ} (m : Fin n → E) (ξ : E) :
    lineSymbol m ξ = ∏ j, ((inner ℝ ξ (m j) : ℝ) : ℂ) := rfl

/-- The symbol of $\partial^m$ for $m \in E^{n+1}$ splits off its first factor: $\sigma_m(\xi) =
\langle \xi, m_0 \rangle \, \sigma_{m'}(\xi)$, where $m' = (m_1, \dots, m_n)$. -/
theorem lineSymbol_succ {n : ℕ} (m : Fin (n + 1) → E) :
    lineSymbol m = (fun ξ : E ↦ ((inner ℝ ξ (m 0) : ℝ) : ℂ)) * lineSymbol (Fin.tail m) := by
  funext ξ
  rw [lineSymbol_apply, Pi.mul_apply, lineSymbol_apply, Fin.prod_univ_succ]
  rfl

/-- The symbol of the empty tuple of directions is the constant $1$. -/
theorem lineSymbol_zero (m : Fin 0 → E) : lineSymbol m = fun _ : E ↦ (1 : ℂ) := by
  funext ξ
  simp

/-- The symbol $\sigma_m$ of $\partial^m$ has temperate growth, because it is a product of linear
forms. -/
theorem hasTemperateGrowth_lineSymbol {n : ℕ} (m : Fin n → E) :
    (lineSymbol m).HasTemperateGrowth := by
  induction n with
  | zero => rw [lineSymbol_zero]; exact Function.HasTemperateGrowth.const (1 : ℂ)
  | succ n ih =>
    rw [lineSymbol_succ]
    exact Function.HasTemperateGrowth.mul (by fun_prop) (ih (Fin.tail m))

end Symbol

section FourierDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The Fourier transform of an iterated directional derivative of a tempered distribution.** Let
$E$ be a finite-dimensional real inner product space with its Borel σ-algebra, and let $F$ be a
complex normed space. For a tempered distribution $f$ and a tuple $m \in E^n$,
$$\mathcal{F}(\partial^m f) = (2\pi i)^n \, \sigma_m \, \mathcal{F} f,$$
where the product with $\sigma_m$ is `TemperedDistribution.smulLeftCLM`. This is Mathlib's
`TemperedDistribution.fourier_lineDerivOp_eq`, iterated. -/
theorem fourier_iteratedLineDerivOp_eq {n : ℕ} (m : Fin n → E) (f : 𝓢'(E, F)) :
    𝓕 (∂^{m} f) = ((2 * (Real.pi : ℂ) * Complex.I) ^ n) •
      smulLeftCLM F (lineSymbol m) (𝓕 f) := by
  induction n with
  | zero =>
    rw [iteratedLineDerivOp_fin_zero, pow_zero, one_smul, lineSymbol_zero, smulLeftCLM_const,
      one_smul]
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, fourier_lineDerivOp_eq, ih (Fin.tail m), map_smul,
      smulLeftCLM_smulLeftCLM_apply (hasTemperateGrowth_lineSymbol _) (by fun_prop),
      smul_smul, show lineSymbol (Fin.tail m) * (fun x : E ↦ ((inner ℝ x (m 0) : ℝ) : ℂ))
        = lineSymbol m by rw [lineSymbol_succ]; ring]
    congr 1
    ring

/-- **The Fourier transform of a weak derivative on the whole space.** Let $E$ be a
finite-dimensional real inner product space with its Borel σ-algebra and Lebesgue measure, let
$m \in E^n$, and let $v, w \in L^2(E; \mathbb{C})$ with $\partial^m T_v = T_w$. By
`MeasureTheory.Lp.iteratedLineDerivOp_eq_iff_hasWeakIteratedLineDerivOn`, this says that $w$ is
the weak derivative $\partial^m v$ of Definition 7.1.3 of [han2009theoretical]. If the function
$\xi \mapsto \sigma_m(\xi) \, \mathcal{F} v(\xi)$ lies in $L^2$, then
$$\mathcal{F} w(\xi) = (2\pi i)^n \, \sigma_m(\xi) \, \mathcal{F} v(\xi)$$
for almost every $\xi$.

Here $\mathcal{F}$ is the Fourier transform on $L^2$. -/
theorem fourier_weakDeriv_aeEq {n : ℕ} (m : Fin n → E)
    {v w : Lp ℂ 2 (volume : Measure E)}
    (hvw : ∂^{m} (v : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ)))
    (hmem : MemLp (fun ξ ↦ lineSymbol m ξ * (𝓕 v) ξ) 2 (volume : Measure E)) :
    ((𝓕 w : Lp ℂ 2 (volume : Measure E)) : E → ℂ) =ᵐ[volume]
      fun ξ ↦ (2 * (Real.pi : ℂ) * Complex.I) ^ n * (lineSymbol m ξ * (𝓕 v) ξ) := by
  have h1 : ((hmem.toLp _ : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ))
      = smulLeftCLM ℂ (lineSymbol m) ((𝓕 v : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) :=
    toTemperedDistribution_eq_smulLeftCLM (hasTemperateGrowth_lineSymbol m) hmem.coeFn_toLp
  have h2 : ((𝓕 w : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ))
      = (((2 * (Real.pi : ℂ) * Complex.I) ^ n • hmem.toLp _ : Lp ℂ 2 (volume : Measure E))
          : 𝓢'(E, ℂ)) := by
    rw [← Lp.fourier_toTemperedDistribution_eq, ← hvw, fourier_iteratedLineDerivOp_eq,
      Lp.fourier_toTemperedDistribution_eq, ← h1]
    exact ((Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).map_smul _ _).symm
  have hinj : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2) :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot
  have h4 : (𝓕 w : Lp ℂ 2 (volume : Measure E))
      = (2 * (Real.pi : ℂ) * Complex.I) ^ n • hmem.toLp _ := hinj h2
  rw [h4]
  filter_upwards [Lp.coeFn_smul ((2 * (Real.pi : ℂ) * Complex.I) ^ n) (hmem.toLp _),
    hmem.coeFn_toLp] with ξ h h'
  rw [h, Pi.smul_apply, h', smul_eq_mul]

end FourierDeriv

/-! ### The inverse Fourier integral of an `L²` function with integrable Fourier transform -/

section FourierRepresentation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Let $p, q \ge 1$, and let $f \in L^p(E; \mathbb{C})$ and $g \in L^q(E; \mathbb{C})$ for the
Lebesgue measure. If $T_f = T_g$, then $f = g$ almost everywhere. The two functions have the
same integrals against every compactly supported smooth function. -/
theorem ae_eq_of_toTemperedDistribution_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp ℂ p (volume : Measure E)) (g : Lp ℂ q (volume : Measure E))
    (h : (f : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ))) : (f : E → ℂ) =ᵐ[volume] g := by
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp f).locallyIntegrable Fact.out)
    ((Lp.memLp g).locallyIntegrable Fact.out) fun φ hφ hφc ↦ ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hg₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofRealCLM ∘ φ) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have := congrArg (fun T : 𝓢'(E, ℂ) ↦ T (hg₁.toSchwartzMap hg₂)) h
  simp only [Lp.toTemperedDistribution_apply] at this
  have hΦφ : ∀ x, (hg₁.toSchwartzMap hg₂) x = (φ x : ℂ) := fun x ↦ rfl
  simp only [hΦφ, smul_eq_mul] at this
  simp only [Complex.real_smul]
  exact this

/-- Let $v \in L^2(E; \mathbb{C})$ and $g \in L^1(E; \mathbb{C})$, and assume that the $L^2$ Fourier
transform $\mathcal{F} v$ and $g$ are the same tempered distribution. Then the pointwise inverse
Fourier integral $\mathcal{F}^{-1} g$ equals $v$ almost everywhere.

Against a Schwartz function $\Phi$, Fubini's theorem gives $\int \Phi \, \mathcal{F}^{-1} g =
\int (\mathcal{F}^{-1} \Phi) \, g$, which is $(\mathcal{F} v)(\mathcal{F}^{-1} \Phi) =
(\mathcal{F}^{-1} \mathcal{F} v)(\Phi) = v(\Phi)$ in the sense of distributions. -/
theorem fourierInv_ae_eq_of_toTemperedDistribution_eq (v : Lp ℂ 2 (volume : Measure E))
    (g : Lp ℂ 1 (volume : Measure E))
    (h : ((𝓕 v : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ))) :
    𝓕⁻ (g : E → ℂ) =ᵐ[volume] v := by
  have hgint : Integrable (g : E → ℂ) := L1.integrable_coeFn g
  have hcont : Continuous (𝓕⁻ (g : E → ℂ)) :=
    (Real.Lp.fourierTransformInv g).continuous.congr fun x ↦ by simp
  refine ae_eq_of_integral_contDiff_smul_eq (hcont.locallyIntegrable)
    ((Lp.memLp v).locallyIntegrable one_le_two) fun φ hφ hφc ↦ ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hg₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofRealCLM ∘ φ) :=
    Complex.ofRealCLM.contDiff.comp hφ
  set Φ : 𝓢(E, ℂ) := hg₁.toSchwartzMap hg₂ with hΦ
  have hΦφ : ∀ x, Φ x = (φ x : ℂ) := fun x ↦ rfl
  -- the distribution identity
  have hdist : (g : 𝓢'(E, ℂ)) (𝓕⁻ Φ) = (v : 𝓢'(E, ℂ)) Φ := by
    rw [← h, ← Lp.fourier_toTemperedDistribution_eq, ← fourierInv_apply,
      FourierTransform.fourierInv_fourier_eq]
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at hdist
  -- Fubini: `∫ (𝓕⁻ Φ) g = ∫ Φ 𝓕⁻ g`
  have hflip : ∫ ξ, (𝓕⁻ Φ) ξ • (g : E → ℂ) ξ = ∫ x, Φ x • 𝓕⁻ (g : E → ℂ) x := by
    have hL : Continuous fun p : E × E ↦ (-innerₗ E) p.1 p.2 := by
      change Continuous fun p : E × E ↦ -(inner ℝ p.1 p.2)
      exact continuous_inner.neg
    have hflipL : (-innerₗ E).flip = -innerₗ E := by
      ext x y
      simp [real_inner_comm]
    have := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
      (L := -innerₗ E) (μ := volume) (ν := volume) Real.continuous_fourierChar hL
      Φ.integrable hgint
    rw [hflipL] at this
    rw [SchwartzMap.fourierInv_coe]
    exact this
  calc ∫ x, φ x • 𝓕⁻ (g : E → ℂ) x = ∫ x, Φ x • 𝓕⁻ (g : E → ℂ) x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        change φ x • 𝓕⁻ (g : E → ℂ) x = Φ x • 𝓕⁻ (g : E → ℂ) x
        rw [hΦφ, Complex.real_smul, smul_eq_mul]
    _ = ∫ ξ, (𝓕⁻ Φ) ξ • (g : E → ℂ) ξ := hflip.symm
    _ = ∫ x, Φ x • (v : E → ℂ) x := hdist
    _ = ∫ x, φ x • (v : E → ℂ) x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        change Φ x • (v : E → ℂ) x = φ x • (v : E → ℂ) x
        rw [hΦφ, Complex.real_smul, smul_eq_mul]

/-- **The continuous representative of an $L^2$ function with integrable Fourier transform.** Let
$v \in L^2(E; \mathbb{C})$, and assume that its $L^2$ Fourier transform $\mathcal{F} v$ is
integrable. Then there is a continuous function $v'$ with $v = v'$ almost everywhere and
$$|v'(x)| \le \int |\mathcal{F} v(\xi)| \, d\xi \quad \text{for every } x \in E.$$

The function $v'$ is the pointwise inverse Fourier integral of $\mathcal{F} v$. This is Step 1
of Examples 7.4.2 and 7.4.3 of [han2009theoretical],
$|v(x)| \le c \int |\mathcal{F} v(\xi)| \, d\xi$, with $c = 1$ for Mathlib's normalization of
the Fourier transform. -/
theorem exists_continuous_ae_eq_of_integrable_fourier (v : Lp ℂ 2 (volume : Measure E))
    (hF : Integrable ((𝓕 v : Lp ℂ 2 (volume : Measure E)) : E → ℂ)) :
    ∃ v' : E → ℂ, Continuous v' ∧ (v : E → ℂ) =ᵐ[volume] v' ∧
      ∀ x, ‖v' x‖ ≤ ∫ ξ, ‖(𝓕 v : Lp ℂ 2 (volume : Measure E)) ξ‖ := by
  have hg₀ : MemLp ((𝓕 v : Lp ℂ 2 (volume : Measure E)) : E → ℂ) 1 volume :=
    memLp_one_iff_integrable.2 hF
  obtain ⟨g, hg⟩ : ∃ g : Lp ℂ 1 (volume : Measure E), g = hg₀.toLp _ := ⟨_, rfl⟩
  have hgae : (g : E → ℂ) =ᵐ[volume] (𝓕 v : Lp ℂ 2 (volume : Measure E)) := by
    rw [hg]
    exact hg₀.coeFn_toLp
  have hdist : ((𝓕 v : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)) := by
    ext φ
    simp only [Lp.toTemperedDistribution_apply]
    exact integral_congr_ae (hgae.symm.mono fun x hx ↦ by simp only [hx])
  refine ⟨𝓕⁻ (g : E → ℂ), (Real.Lp.fourierTransformInv g).continuous.congr (fun x ↦ by simp),
    (fourierInv_ae_eq_of_toTemperedDistribution_eq v g hdist).symm, fun x ↦ ?_⟩
  calc ‖𝓕⁻ (g : E → ℂ) x‖ ≤ ∫ ξ, ‖(g : E → ℂ) ξ‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ = ∫ ξ, ‖(𝓕 v : Lp ℂ 2 (volume : Measure E)) ξ‖ :=
        integral_congr_ae (hgae.mono fun x hx ↦ by simp only [hx])

end FourierRepresentation
