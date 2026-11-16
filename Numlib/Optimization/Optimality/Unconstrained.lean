/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.DerivativeTest
import Numlib.Analysis.Calculus.MultivariateTaylor.Peano
import Numlib.Analysis.InnerProductSpace.MinCurvature
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Unconstrained optimality conditions

Let $E$ be a real normed space and $f : E \to \mathbb{R}$. This file proves the necessary and
sufficient optimality conditions of Theorem 1.1.1 of [cartis2022evaluation] for the unconstrained
minimization of $f$. A derivative applied on the diagonal is written $\nabla^j f(x)[d]^j$. The key
tool is the ray lemma: if $x$ minimizes $f$ along the ray $t \mapsto x + t d$, $t \ge 0$, then the
first nonvanishing directional derivative $\nabla^m f(x)[d]^m$ is nonnegative. At an unconstrained
local minimizer this gives $\nabla^2 f(x)[d]^2 \ge 0$, and $\nabla^3 f(x)[d]^3 = 0$ when
$\nabla^2 f(x)[d]^2 = 0$. Conversely, in finite dimension, $\nabla f(x) = 0$ and a positive definite
$\nabla^2 f(x)$ make $x$ a strict local minimizer.

## Main definitions

* `Optimization.IsStrictLocalMinOn`: $x$ is a strict (strong) local minimizer of $f$ on $S$, that
  is, $f(x) < f(y)$ for all $y \in S \setminus \{x\}$ near $x$; `Optimization.IsStrictLocalMin` is
  the case $S = E$.

## Main results

* `Optimization.iteratedFDeriv_apply_nonneg_of_ray`: along a ray on which $x$ is a local minimizer,
  the first nonvanishing directional derivative $\nabla^m f(x)[d]^m$ is nonnegative.
* `Optimization.IsLocalMinOn.iteratedDeriv_nonneg_of_ray`: the one-dimensional form of the ray
  lemma.
* `Optimization.IsLocalMin.iteratedFDeriv_apply_eq_zero_of_odd`: at an unconstrained local
  minimizer, a first nonvanishing directional derivative of odd order vanishes.
* `Optimization.IsLocalMin.minCurvature_iteratedFDeriv_two_nonneg`: the second-order necessary
  condition $\lambda_{\min}[\nabla^2 f(x)] \ge 0$ of Theorem 1.1.1.
* `Optimization.IsLocalMin.iteratedFDeriv_three_eq_zero`: the third-order necessary condition of
  Theorem 1.1.1.
* `Optimization.isStrictLocalMin_of_fderiv_eq_zero_of_posDef`: the second-order sufficient condition
  of Theorem 1.1.1.

## Proof outline

The ray lemma follows from Taylor's theorem with Peano remainder: $(f(x + t d) - f(x)) / t^m \to
\nabla^m f(x)[d]^m / m!$ as $t \to 0^+$. The sufficient conditions in this file, in
`Numlib.Optimization.Optimality.ConvexSet` and in `Numlib.Optimization.Constrained.SecondOrder`
share one argument. If $x$ is not a strict local minimizer, there is a sequence $y_n \to x$ with
$f(y_n) \le f(x)$ whose unit directions converge
(`Optimization.exists_seq_of_not_isStrictLocalMinOn`). The first- and second-order expansions along
such a sequence (`Optimization.tendsto_sub_div_of_hasFDerivAt`,
`Optimization.tendsto_sub_div_sq_of_contDiffAt`) then contradict the hypotheses.

## Implementation notes

* The derivative $\nabla^j f(x)[d]^j$ is `iteratedFDeriv ℝ j f x (fun _ => d)`.
* The first-order necessary condition $\nabla f(x) = 0$ is Mathlib's `IsLocalMin.fderiv_eq_zero`.
  The second-order condition in the form $\nabla^2 f(x)[d]^2 \ge 0$ for all $d$ is
  `IsLocalMin.iteratedFDeriv_two_apply_self_nonneg` of `Numlib.Analysis.Calculus.DerivativeTest`.
-/

open Filter Set Topology Asymptotics Metric
open scoped Nat

namespace Optimization

/-! ### Strict local minimizers -/

section Strict

variable {α β : Type*} [TopologicalSpace α] [Preorder β]

/-- The point $x$ is a **strict** (or **strong**) **local minimizer** of $f$ on $S$ if $f(x) < f(y)$
for every $y \in S$ with $y \neq x$ close enough to $x$. See Section 1.1.2.2 of
[cartis2022evaluation].

The case $S = E$ is the unconstrained case `Optimization.IsStrictLocalMin`. The definition does
not require $x \in S$. It is stated with the filter `𝓝[S \ {x}] x`, for a function from a
topological space to a preorder. -/
def IsStrictLocalMinOn (f : α → β) (S : Set α) (x : α) : Prop :=
  ∀ᶠ y in 𝓝[S \ {x}] x, f x < f y

/-- The point $x$ is a strict local minimizer of $f$ on $S$ if and only if, for all $y$ in a
neighborhood of $x$, $y \in S$ and $y \neq x$ imply $f(x) < f(y)$. -/
theorem isStrictLocalMinOn_iff_eventually {f : α → β} {S : Set α} {x : α} :
    IsStrictLocalMinOn f S x ↔ ∀ᶠ y in 𝓝 x, y ∈ S → y ≠ x → f x < f y := by
  simp only [IsStrictLocalMinOn, eventually_nhdsWithin_iff, Set.mem_sdiff, mem_singleton_iff]
  exact eventually_congr (Eventually.of_forall fun y => ⟨fun h hS hne => h ⟨hS, hne⟩,
    fun h hy => h hy.1 hy.2⟩)

/-- The point $x$ is a **strict local minimizer** of $f$ if $f(x) < f(y)$ for every $y \neq x$ close
enough to $x$. This is `Optimization.IsStrictLocalMinOn` on the whole space; see Section 1.1.2.2
of [cartis2022evaluation]. -/
abbrev IsStrictLocalMin (f : α → β) (x : α) : Prop := IsStrictLocalMinOn f univ x

/-- A strict local minimizer of $f$ on $S$ is a local minimizer of $f$ on $S$. -/
theorem IsStrictLocalMinOn.isLocalMinOn {f : α → β} {S : Set α} {x : α}
    (h : IsStrictLocalMinOn f S x) : IsLocalMinOn f S x := by
  rw [isStrictLocalMinOn_iff_eventually] at h
  change ∀ᶠ y in 𝓝[S] x, f x ≤ f y
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h] with y hy hyS
  by_cases hyx : y = x
  · rw [hyx]
  · exact (hy hyS hyx).le

/-- If $S \subseteq T$ and $x$ is a strict local minimizer of $f$ on $T$, then $x$ is a strict local
minimizer of $f$ on $S$. -/
theorem IsStrictLocalMinOn.mono {f : α → β} {S T : Set α} {x : α} (h : IsStrictLocalMinOn f T x)
    (hST : S ⊆ T) : IsStrictLocalMinOn f S x :=
  h.filter_mono (nhdsWithin_mono _ (sdiff_subset_sdiff_left hST))

end Strict

/-- In a pseudometric space, $x$ is a strict local minimizer of $f$ on $S$ if and only if there is
$\varepsilon > 0$ with $f(x) < f(y)$ for every $y \in S$ with $y \neq x$ and
$\operatorname{dist}(y, x) < \varepsilon$. -/
theorem isStrictLocalMinOn_iff {α β : Type*} [PseudoMetricSpace α] [Preorder β] {f : α → β}
    {S : Set α} {x : α} :
    IsStrictLocalMinOn f S x ↔ ∃ ε > 0, ∀ y ∈ S, dist y x < ε → y ≠ x → f x < f y := by
  rw [isStrictLocalMinOn_iff_eventually, Metric.eventually_nhds_iff]
  exact exists_congr fun ε => and_congr_right fun _ =>
    ⟨fun h y hS hd hne => h hd hS hne, fun h y hd hS hne => h y hS hd hne⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Diagonal values of multilinear maps and low-order Taylor polynomials -/

/-- The second-order Taylor polynomial of $f$ at $x$ is
$$T_{f,2}(x, h) = f(x) + \nabla f(x)[h] + \tfrac{1}{2} \nabla^2 f(x)[h]^2.$$
-/
theorem taylorPolynomial_two_apply (f : E → ℝ) (x h : E) :
    taylorPolynomial f 2 x h =
      f x + fderiv ℝ f x h + iteratedFDeriv ℝ 2 f x (fun _ => h) / 2 := by
  rw [taylorPolynomial_apply]
  simp [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
    smul_eq_mul, Nat.factorial]
  ring

/-- Let $m \ge 1$, and suppose that $\nabla^i f(x)[d]^i = 0$ for $0 < i < m$. Then for every
$t \in \mathbb{R}$, the Taylor polynomial of order $m$ is
$$T_{f,m}(x, t d) = f(x) + \frac{t^m}{m!} \nabla^m f(x)[d]^m.$$
-/
theorem taylorPolynomial_smul_of_forall_eq_zero {f : E → ℝ} {x d : E} {m : ℕ} (hm : m ≠ 0)
    (hzero : ∀ i, 0 < i → i < m → iteratedFDeriv ℝ i f x (fun _ => d) = 0) (t : ℝ) :
    taylorPolynomial f m x (t • d) =
      f x + (m ! : ℝ)⁻¹ * (t ^ m * iteratedFDeriv ℝ m f x (fun _ => d)) := by
  rw [taylorPolynomial_apply, Finset.sum_range_succ]
  congr 1
  · rw [Finset.sum_eq_single 0]
    · simp [iteratedFDeriv_zero_apply]
    · intro i hi hi0
      rw [smul_eq_mul, ContinuousMultilinearMap.apply_smul_diag, smul_eq_mul,
        hzero i (Nat.pos_of_ne_zero hi0) (Finset.mem_range.1 hi), mul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.pos_of_ne_zero hm)) h
  · rw [smul_eq_mul, ContinuousMultilinearMap.apply_smul_diag, smul_eq_mul]

/-! ### The ray lemma -/

/-- **First nonvanishing derivative along a ray.** Let $m \ge 1$, let $f$ be $m$ times continuously
differentiable at $x$, and suppose that $f(x) \le f(x + t d)$ for all sufficiently small $t > 0$
and that $\nabla^i f(x)[d]^i = 0$ for $0 < i < m$. Then
$$\nabla^m f(x)[d]^m \ge 0.$$
This underlies Theorems 1.1.1 and 1.1.2 of [cartis2022evaluation].

By Taylor's theorem with Peano remainder, $(f(x + t d) - f(x)) / t^m \to \nabla^m f(x)[d]^m /
m!$ as $t \to 0^+$. -/
theorem iteratedFDeriv_apply_nonneg_of_ray {f : E → ℝ} {x d : E} {m : ℕ} (hm : m ≠ 0)
    (hf : ContDiffAt ℝ m f x) (hmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), f x ≤ f (x + t • d))
    (hzero : ∀ i, 0 < i → i < m → iteratedFDeriv ℝ i f x (fun _ => d) = 0) :
    0 ≤ iteratedFDeriv ℝ m f x (fun _ => d) := by
  set a := iteratedFDeriv ℝ m f x (fun _ => d)
  have hd : Tendsto (fun t : ℝ => t • d) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 ((0 : ℝ) • d)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hR := (sub_taylorPolynomial_isLittleO hf).comp_tendsto hd
  have hO : (fun t : ℝ => ‖t • d‖ ^ m) =O[𝓝[>] (0 : ℝ)] fun t => t ^ m := by
    refine IsBigO.of_bound (‖d‖ ^ m) (Eventually.of_forall fun t => ?_)
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, norm_pow]
    rw [abs_of_nonneg (by positivity), mul_comm]
  have hlim := (hR.trans_isBigO hO).tendsto_div_nhds_zero
  have hlim' : Tendsto (fun t : ℝ => (f (x + t • d) - f x) / t ^ m) (𝓝[>] 0)
      (𝓝 ((m ! : ℝ)⁻¹ * a)) := by
    have := hlim.const_add ((m ! : ℝ)⁻¹ * a)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ^ m ≠ 0 := pow_ne_zero _ (ne_of_gt ht)
    simp only [Function.comp_apply, taylorPolynomial_smul_of_forall_eq_zero hm hzero]
    field_simp
    ring
  have hnn : 0 ≤ (m ! : ℝ)⁻¹ * a := by
    refine ge_of_tendsto hlim' ?_
    filter_upwards [hmin, self_mem_nhdsWithin] with t ht htpos
    exact div_nonneg (sub_nonneg.2 ht) (pow_nonneg (le_of_lt htpos) _)
  have hfac : (0 : ℝ) < (m ! : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast Nat.factorial_pos m)
  exact (mul_nonneg_iff_of_pos_left hfac).1 hnn

/-- **One-dimensional ray lemma.** Let $m \ge 1$, let $\psi : \mathbb{R} \to \mathbb{R}$ be $m$
times continuously differentiable at $a$, let $a$ be a local minimizer of $\psi$ on
$[a, \infty)$, and let $\psi^{(i)}(a) = 0$ for $0 < i < m$. Then $\psi^{(m)}(a) \ge 0$. -/
theorem IsLocalMinOn.iteratedDeriv_nonneg_of_ray {ψ : ℝ → ℝ} {a : ℝ} {m : ℕ} (hm : m ≠ 0)
    (hψ : ContDiffAt ℝ m ψ a) (hmin : IsLocalMinOn ψ (Ici a) a)
    (hzero : ∀ i, 0 < i → i < m → iteratedDeriv i ψ a = 0) :
    0 ≤ iteratedDeriv m ψ a := by
  refine iteratedFDeriv_apply_nonneg_of_ray (d := (1 : ℝ)) hm hψ ?_ hzero
  have ht : Tendsto (fun t : ℝ => a + t • (1 : ℝ)) (𝓝[>] 0) (𝓝[Ici a] a) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => a + t • (1 : ℝ)) (𝓝 0) (𝓝 (a + (0 : ℝ) • 1)) :=
        ((continuous_const.add (continuous_id.smul continuous_const))).tendsto 0
      rw [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [smul_eq_mul, mul_one, mem_Ici]
      exact le_add_of_nonneg_right (le_of_lt ht)
  exact ht.eventually hmin

/-- If $x$ is a local minimizer of $f$, then for every direction $d$, $f(x) \le f(x + t d)$ for all
sufficiently small $t > 0$. -/
theorem IsLocalMin.eventually_le_add_smul {f : E → ℝ} {x : E} (hmin : IsLocalMin f x) (d : E) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f x ≤ f (x + t • d) := by
  have : Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 (x + (0 : ℝ) • d)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
  rw [zero_smul, add_zero] at this
  exact (this.mono_left nhdsWithin_le_nhds).eventually hmin

/-- Let $x$ be a local minimizer of $f$, let $m$ be odd, let $f$ be $m$ times continuously
differentiable at $x$, and suppose that $\nabla^i f(x)[d]^i = 0$ for $0 < i < m$. Then
$\nabla^m f(x)[d]^m = 0$. This is the odd-order case of Theorem 1.1.1 of [cartis2022evaluation].

The proof applies the ray lemma `Optimization.iteratedFDeriv_apply_nonneg_of_ray` to $d$ and to
$-d$. -/
theorem IsLocalMin.iteratedFDeriv_apply_eq_zero_of_odd {f : E → ℝ} {x d : E} {m : ℕ}
    (hmin : IsLocalMin f x) (hm : Odd m) (hf : ContDiffAt ℝ m f x)
    (hzero : ∀ i, 0 < i → i < m → iteratedFDeriv ℝ i f x (fun _ => d) = 0) :
    iteratedFDeriv ℝ m f x (fun _ => d) = 0 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hm
  have hray := IsLocalMin.eventually_le_add_smul hmin
  have hneg : ∀ i, iteratedFDeriv ℝ i f x (fun _ => -d) =
      (-1) ^ i * iteratedFDeriv ℝ i f x (fun _ => d) := by
    intro i
    rw [← neg_one_smul ℝ d, ContinuousMultilinearMap.apply_smul_diag, smul_eq_mul]
  have h1 := iteratedFDeriv_apply_nonneg_of_ray hm0 hf (hray d) hzero
  have h2 := iteratedFDeriv_apply_nonneg_of_ray hm0 hf (hray (-d))
    fun i hi him => by rw [hneg, hzero i hi him, mul_zero]
  rw [hneg, hm.neg_one_pow, neg_one_mul, neg_nonneg] at h2
  exact le_antisymm h2 h1

/-! ### Theorem 1.1.1: necessary conditions -/

/-- **Second-order necessary condition**, (1.1.5) of Theorem 1.1.1 of [cartis2022evaluation]. Let
$x$ be a local minimizer of $f$ and let $f$ be twice continuously differentiable at $x$. Then
$$\lambda_{\min}[\nabla^2 f(x)] \ge 0.$$

Here $\lambda_{\min}[A] = \inf_{\|d\| = 1} A[d]^2$ is `Optimization.minCurvature`. The statement
follows from the Hessian test `IsLocalMin.iteratedFDeriv_two_apply_self_nonneg` of
`Numlib.Analysis.Calculus.DerivativeTest`, which gives $\nabla^2 f(x)[d]^2 \ge 0$ for every $d$. -/
theorem IsLocalMin.minCurvature_iteratedFDeriv_two_nonneg {f : E → ℝ} {x : E}
    (hmin : IsLocalMin f x) (hf : ContDiffAt ℝ 2 f x) :
    0 ≤ minCurvature (iteratedFDeriv ℝ 2 f x) :=
  minCurvature_nonneg_iff.2 (_root_.IsLocalMin.iteratedFDeriv_two_apply_self_nonneg hmin hf)

/-- **Third-order necessary condition** of Theorem 1.1.1 of [cartis2022evaluation]. Let $x$ be a
local minimizer of $f$ and let $f$ be three times continuously differentiable at $x$. If
$\nabla^2 f(x)[d]^2 = 0$, then
$$\nabla^3 f(x)[d]^3 = 0.$$

At a local minimizer the Hessian is positive semidefinite, so the hypothesis
$\nabla^2 f(x)[d]^2 = 0$ is equivalent to $\nabla^2 f(x) d = 0$. -/
theorem IsLocalMin.iteratedFDeriv_three_eq_zero {f : E → ℝ} {x d : E} (hmin : IsLocalMin f x)
    (hf : ContDiffAt ℝ 3 f x) (hd : iteratedFDeriv ℝ 2 f x (fun _ => d) = 0) :
    iteratedFDeriv ℝ 3 f x (fun _ => d) = 0 := by
  refine IsLocalMin.iteratedFDeriv_apply_eq_zero_of_odd hmin ⟨1, rfl⟩ hf fun i hi hi3 => ?_
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
  · rw [iteratedFDeriv_one_apply, hmin.fderiv_eq_zero, zero_apply]
  · exact hd

/-! ### Directional limits along converging directions -/

/-- Let $l$ be a filter, and let $r$ and $w$ be functions with $r(a) > 0$ eventually and
$w(a) / r(a) \to z$ along $l$. Then $w = O(r)$ along $l$. -/
theorem isBigO_of_tendsto_inv_smul {α : Type*} {l : Filter α} {r : α → ℝ} {w : α → E} {z : E}
    (hr : ∀ᶠ a in l, 0 < r a) (hwz : Tendsto (fun a => (r a)⁻¹ • w a) l (𝓝 z)) :
    w =O[l] r := by
  have hb : ∀ᶠ a in l, ‖(r a)⁻¹ • w a‖ < ‖z‖ + 1 :=
    hwz.norm.eventually (gt_mem_nhds (lt_add_one _))
  refine IsBigO.of_bound (‖z‖ + 1) ?_
  filter_upwards [hr, hb] with a ha hb
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha] at hb
  rw [Real.norm_eq_abs, abs_of_pos ha]
  rw [inv_mul_lt_iff₀ ha] at hb
  linarith

/-- **First-order directional limit.** Let $L : E \to \mathbb{R}$ have the derivative $L'$ at $x$,
and let $r$ and $w$ be functions on a filter $l$ with $r(a) > 0$ eventually, $w(a) \to 0$ and
$w(a) / r(a) \to z$. Then
$$\frac{L(x + w(a)) - L(x)}{r(a)} \to L' z.$$
-/
theorem tendsto_sub_div_of_hasFDerivAt {L : E → ℝ} {L' : E →L[ℝ] ℝ} {x z : E}
    (hL : HasFDerivAt L L' x) {α : Type*} {l : Filter α} {r : α → ℝ} {w : α → E}
    (hr : ∀ᶠ a in l, 0 < r a) (hw : Tendsto w l (𝓝 0))
    (hwz : Tendsto (fun a => (r a)⁻¹ • w a) l (𝓝 z)) :
    Tendsto (fun a => (L (x + w a) - L x) / r a) l (𝓝 (L' z)) := by
  have hxw : Tendsto (fun a => x + w a) l (𝓝 x) := by
    simpa using hw.const_add x
  have ho := (hL.isLittleO.comp_tendsto hxw).trans_isBigO
    ((isBigO_of_tendsto_inv_smul hr hwz).congr_left fun a => by simp)
  have h1 := ho.tendsto_div_nhds_zero
  have h2 : Tendsto (fun a => L' ((r a)⁻¹ • w a)) l (𝓝 (L' z)) :=
    (L'.continuous.tendsto z).comp hwz
  have := h2.add h1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hr] with a ha
  simp only [Function.comp_apply, add_sub_cancel_left, map_smul, smul_eq_mul]
  field_simp
  ring

/-- **Second-order directional limit.** Let $L : E \to \mathbb{R}$ be twice continuously
differentiable at $x$, and let $r$ and $w$ be functions on a filter $l$ with $r(a) > 0$
eventually, $w(a) \to 0$ and $w(a) / r(a) \to z$. Then
$$\frac{L(x + w(a)) - L(x) - \nabla L(x)[w(a)]}{r(a)^2} \to \tfrac{1}{2} \nabla^2 L(x)[z]^2.$$

The proof uses Taylor's theorem with Peano remainder. -/
theorem tendsto_sub_div_sq_of_contDiffAt {L : E → ℝ} {x z : E} (hL : ContDiffAt ℝ 2 L x)
    {α : Type*} {l : Filter α} {r : α → ℝ} {w : α → E} (hr : ∀ᶠ a in l, 0 < r a)
    (hw : Tendsto w l (𝓝 0)) (hwz : Tendsto (fun a => (r a)⁻¹ • w a) l (𝓝 z)) :
    Tendsto (fun a => (L (x + w a) - L x - fderiv ℝ L x (w a)) / r a ^ 2) l
      (𝓝 (iteratedFDeriv ℝ 2 L x (fun _ => z) / 2)) := by
  have hO : (fun a => ‖w a‖ ^ 2) =O[l] fun a => r a ^ 2 := by
    have := (isBigO_of_tendsto_inv_smul hr hwz).norm_left.pow 2
    simpa using this
  have ho := ((sub_taylorPolynomial_isLittleO hL).comp_tendsto hw).trans_isBigO hO
  have h1 := ho.tendsto_div_nhds_zero
  have hcont : Continuous fun v : E => iteratedFDeriv ℝ 2 L x (fun _ => v) / 2 :=
    ((iteratedFDeriv ℝ 2 L x).coe_continuous.comp (continuous_pi fun _ => continuous_id)).div_const
      2
  have h2 := (hcont.tendsto z).comp hwz
  have := h2.add h1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hr] with a ha
  have ha2 : r a ^ 2 ≠ 0 := pow_ne_zero _ ha.ne'
  simp only [Function.comp_apply, taylorPolynomial_two_apply,
    ContinuousMultilinearMap.apply_smul_diag, smul_eq_mul]
  field_simp
  ring

/-- Let $E$ be finite-dimensional. If $x$ is not a strict local minimizer of $f$ on $S$, then there
are a sequence $(y_n)$ and a unit vector $z$ such that, for every $n$, $y_n \in S$, $y_n \neq x$
and $f(y_n) \le f(x)$, and
$$y_n \to x, \qquad \frac{y_n - x}{\|y_n - x\|} \to z.$$
-/
theorem exists_seq_of_not_isStrictLocalMinOn [FiniteDimensional ℝ E] {f : E → ℝ} {S : Set E}
    {x : E} (h : ¬ IsStrictLocalMinOn f S x) :
    ∃ (y : ℕ → E) (z : E), (∀ n, y n ∈ S ∧ y n ≠ x ∧ f (y n) ≤ f x) ∧
      Tendsto y atTop (𝓝 x) ∧ ‖z‖ = 1 ∧
      Tendsto (fun n => ‖y n - x‖⁻¹ • (y n - x)) atTop (𝓝 z) := by
  rw [isStrictLocalMinOn_iff] at h
  push Not at h
  have hseq : ∀ n : ℕ, ∃ y, y ∈ S ∧ dist y x < 1 / ((n : ℝ) + 1) ∧ y ≠ x ∧ f y ≤ f x :=
    fun n => h _ (by positivity)
  choose y hyS hyd hyne hyf using hseq
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hyd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hunorm : ∀ n, ‖‖y n - x‖⁻¹ • (y n - x)‖ = 1 := fun n => by
    rw [norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (sub_ne_zero.2 (hyne n)))]
  obtain ⟨z, hz, k, hk, hulim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    fun n => mem_sphere_zero_iff_norm.2 (hunorm n)
  exact ⟨y ∘ k, z, fun n => ⟨hyS _, hyne _, hyf _⟩, hylim.comp hk.tendsto_atTop,
    mem_sphere_zero_iff_norm.1 hz, hulim⟩

/-! ### Theorem 1.1.1: sufficient condition -/

/-- **Second-order sufficient condition**, the converse part of Theorem 1.1.1 of
[cartis2022evaluation]. Let $E$ be finite-dimensional, and let $f$ be twice continuously
differentiable at $x$. If $\nabla f(x) = 0$ and $\nabla^2 f(x)$ is positive definite, that is,
$\nabla^2 f(x)[d]^2 > 0$ for every $d \neq 0$, then $x$ is a strict local minimizer of $f$. -/
theorem isStrictLocalMin_of_fderiv_eq_zero_of_posDef [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hcrit : fderiv ℝ f x = 0)
    (hpos : ∀ d, d ≠ 0 → 0 < iteratedFDeriv ℝ 2 f x (fun _ => d)) :
    IsStrictLocalMin f x := by
  by_contra hcon
  obtain ⟨y, z, hy, hylim, hz, hyz⟩ := exists_seq_of_not_isStrictLocalMinOn hcon
  have hw : Tendsto (fun n => y n - x) atTop (𝓝 0) := by simpa using hylim.sub_const x
  have hlim := tendsto_sub_div_sq_of_contDiffAt hf
    (Eventually.of_forall fun n => norm_pos_iff.2 (sub_ne_zero.2 (hy n).2.1)) hw hyz
  simp only [add_sub_cancel, hcrit, zero_apply, sub_zero] at hlim
  have hle : iteratedFDeriv ℝ 2 f x (fun _ => z) / 2 ≤ 0 :=
    le_of_tendsto' hlim fun n => div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hy n).2.2)
      (sq_nonneg _)
  have := hpos z (by rintro rfl; simp at hz)
  linarith

end Optimization
