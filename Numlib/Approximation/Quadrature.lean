/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.TietzeExtension
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import Numlib.MeasureTheory.Integral.MeanValue
import Numlib.Approximation.Hermite
import Numlib.Approximation.Interpolation
import Numlib.Approximation.OrthogonalPolynomial
import Numlib.Topology.TietzeExtension

/-!
# Numerical quadrature

A quadrature rule with nodes $x_i$ in a compact space $X$ and weights $w_i \in \mathbb{R}$ is the
bounded linear functional $f \mapsto \sum_i w_i f(x_i)$ on $C(X)$, an approximation of an integral.
This module computes the norm of a rule, proves the criterion of Szegő and Pólya for the convergence
of a sequence of rules at every continuous integrand, and proves Peano's kernel representation of
the error of one rule. It then develops the Gauss theory for a weight $\mu$ on $\mathbb{R}$: Gauss
quadrature, Jacobi's characterization of the degree of exactness, the discrete inner product of a
rule, and the remainder of a rule through Hermite interpolation, with the Gauss remainder and the
Gauss and Gauss–Radau bounds as special cases. The material is from [han2009theoretical], §2.4,
[kress1998numerical], §9.1–§9.3, [quarteroni2000numerical], §10.2, and [golub2013matrix], §10.2.

## Main definitions

* `Quadrature.functional`: the rule $f \mapsto \sum_i w_i f(x_i)$, as an element of the dual of
  $C(X)$.
* `Quadrature.IsExactOn`: the rule agrees with a target functional $L$ on the polynomials of degree
  at most $d$. `Quadrature.degreeOfExactness` is the largest such $d$.
* `Quadrature.IsInterpolatory`: the weights are the values of $L$ at the Lagrange basis functions of
  the nodes.
* `Quadrature.IsExactOnMeasure`, `Quadrature.IsInterpolatoryMeasure`: the same two notions for a
  measure $\mu$ on $\mathbb{R}$ and real polynomials, the form in which the Gauss theory is stated.
* `Quadrature.discreteInner`: the discrete inner product $(f, g)_n = \sum_i w_i f(x_i) g(x_i)$ of a
  rule.
* `Quadrature.truncPow`: the truncated power $(y - t)_+^m$.
* `Quadrature.peanoKernel`: the Peano kernel of a rule, which is the error functional applied to
  $x \mapsto (x - t)_+^m$ and divided by $m!$.

## Main results

* `Quadrature.norm_functional`: for distinct nodes, the norm of the rule is $\sum_i |w_i|$.
* `Quadrature.isInterpolatory_iff_isExactOn`: a rule with $n + 1$ distinct nodes is interpolatory if
  and only if it is exact to degree $n$.
* `Quadrature.tendsto_iff_bddAbove_sum_abs`: the **Szegő–Pólya criterion**: rules that are exact to
  degrees tending to infinity converge at every continuous integrand if and only if the sums
  $\sum_i |w_i|$ are bounded. `Quadrature.tendsto_of_nonneg` is the corollary for nonnegative
  weights.
* `Quadrature.exists_gauss`: **Gauss quadrature**: the $n$ roots of the $n$-th orthogonal polynomial
  of a weight carry positive weights for which the rule is exact on the polynomials of degree less
  than $2n$. By `Quadrature.not_forall_eq_integral_of_degree_le`, no $n$-point rule is exact to
  degree $2n$.
* `Quadrature.isExactOnMeasure_add_iff`: **Jacobi's theorem**: a rule with $n + 1$ distinct nodes is
  exact to degree $n + m$ if and only if it is interpolatory and its nodal polynomial is orthogonal
  to the polynomials of degree at most $m - 1$. `Quadrature.isExactOnMeasure_two_mul_add_one_iff` is
  the case $m = n + 1$, which characterizes the Gauss nodes as the roots of the orthogonal
  polynomial, and `Quadrature.not_isExactOnMeasure_two_mul_add_two` excludes the degree $2n + 2$.
* `Quadrature.isExactOnMeasure_iff_isExactOn`: for a measure carried by $[a, b]$, exactness for the
  measure is exactness for the integral functional on $C([a, b])$.
* `Quadrature.isExactOnMeasure_map_affine`, `Quadrature.isExactOnMeasure_volume_Icc_of_affine`: an
  affine change of the interval preserves exactness.
* `Quadrature.tendsto_of_isExactOnMeasure`: for a finite measure carried by $[a, b]$, rules with
  nonnegative weights and degrees of exactness tending to infinity converge at every continuous
  integrand.
* `Quadrature.mem_Icc_of_isExactOnMeasure`: a node with positive weight of a rule exact to a high
  enough degree lies in the interval that carries the measure.
* `Quadrature.interpolate_eq_sum_discreteInner_smul`: for a rule with $n + 1$ nodes exact to degree
  $2n - 1$, the interpolant at the nodes is the discrete truncation $\sum_{k \le n} \frac{(f,
  p_k)_n}{(p_k, p_k)_n}\, p_k$ of the orthogonal expansion. The discrete Chebyshev and Legendre
  transforms are instances.
* `Quadrature.exists_error_eq_of_hermite_of_convex`: the **remainder through Hermite
  interpolation**, $\int f\,d\mu - \sum_i w_i f(x_i) = \frac{f^{(N+1)}(\xi)}{(N+1)!} \int
  \omega\,d\mu$, when the nodal polynomial $\omega$ with multiplicities has constant sign.
  `Quadrature.exists_error_eq_of_hermite` is the case of a finite measure on a compact interval.
* `Quadrature.exists_gauss_error_eq_of_convex`, `Quadrature.exists_gauss_error_eq`: the **Gauss
  remainder** $\frac{f^{(2n)}(\xi)}{(2n)!} \int p_n^2\,d\mu$.
* `Quadrature.gauss_le_integral_le_gaussRadau`, `Quadrature.gauss_le_integral_le_gaussRadau_right`:
  a Gauss rule and a Gauss–Radau rule bound the integral from below and from above when $f^{(2k)}$
  and $f^{(2k+1)}$ have suitable signs.
* `Quadrature.error_eq_integral_peanoKernel`: **Peano's kernel theorem**: a rule exact to degree $m$
  has the error $\int_a^b K(t)\, f^{(m+1)}(t)\,dt$ with the Peano kernel $K$.
  `Quadrature.abs_error_le_integral_abs_peanoKernel` is the resulting error bound.

## Proof outline

For the norm of a rule, the inequality $\le$ is the triangle inequality, and for $\ge$ the Tietze
extension theorem gives a continuous function of norm $1$ with the value $\operatorname{sign} w_i$
at each node. In the Szegő–Pólya criterion, sufficiency is the density of the polynomials
(Weierstrass' theorem) together with the $\varepsilon/3$ argument
`ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded`, and necessity is the uniform
boundedness principle. For the Hermite remainder, the error is $\int (f - H)\,d\mu$ for the Hermite
interpolant $H$, and $f - H - c\omega$ has integral $0$ for a suitable $c$. So $f^{(N+1)}/(N+1)!$
cannot stay strictly on one side of $c$ on the carrier, and the intermediate value theorem gives
$\xi$. The Gauss remainder is the case of double nodes, whose nodal polynomial is $p_n^2$.

Peano's theorem needs no Fubini step. `Quadrature.eq_taylorSum_add_integral` is Taylor's formula
with the integral remainder, and `Quadrature.integral_eq_taylorSum_add_integral` is the same
telescoping identity with the kernel $(b - t)^{m+1}/(m+1)!$, which is the integral over $[a, b]$ of
the pointwise remainder. The first is applied at each node and the second over $[a, b]$, so that
both parts of the error are integrals over the same interval.

## Implementation notes

* Exactness has two forms. `Quadrature.IsExactOn` is stated for a target functional on `C(X, ℝ)`
  with $X \subseteq \mathbb{R}$ compact. The Gauss theory uses `Quadrature.IsExactOnMeasure`, stated
  for a measure on $\mathbb{R}$ and polynomials, so that it covers weights of unbounded support,
  such as the Laguerre weight on $(0, \infty)$ and the Hermite weight on $\mathbb{R}$.
  `Quadrature.isExactOnMeasure_iff_isExactOn` connects the two forms.
* `Quadrature.exists_gauss` and `Quadrature.not_forall_eq_integral_of_degree_le` are stated for
  polynomials and a measure, not through `Quadrature.IsExactOn`, which would need the weight to be
  carried by a compact set.
* Peano's theorem is stated for the target functional $f \mapsto \int_a^b f$ and a rule given by
  real nodes and weights, because the interchange in its proof needs the target to be the integral
  itself. The integrand and its derivatives are a sequence of functions `F : ℕ → ℝ → ℝ`, where
  `F (k + 1)` is the derivative of `F k`.
* $p_n$ is the monic orthogonal polynomial `OrthogonalPolynomial.family μ n`, and $\int p_n^2\,d\mu$
  is `OrthogonalPolynomial.normSq μ n`. A weight is a measure in the sense of
  `OrthogonalPolynomial.IsWeight`: all its moments are finite and it is not carried by a finite set.
* Nodes and weights are indexed by `Fin n`, so the indices start at $0$.
-/

open Filter Topology

open scoped Polynomial

namespace Quadrature

section Definition

variable {X : Type*} [TopologicalSpace X]

/-- A **quadrature rule** on a topological space $X$ with nodes $x_i \in X$ and weights
$w_i \in \mathbb{R}$, $i = 0, \dots, n - 1$: the bounded linear functional
$$f \mapsto \sum_i w_i\, f(x_i)$$
on $C(X)$, the elementary approximation of an integral. This is (2.4.3) of [han2009theoretical]. -/
noncomputable def functional {n : ℕ} (w : Fin n → ℝ) (x : Fin n → X) : C(X, ℝ) →L[ℝ] ℝ :=
  ∑ i, w i • ContinuousMap.evalCLM ℝ (x i)

/-- The quadrature rule with weights $w_i$ and nodes $x_i$ takes the value $\sum_i w_i\, f(x_i)$ at
$f$. -/
@[simp]
theorem functional_apply {n : ℕ} (w : Fin n → ℝ) (x : Fin n → X) (f : C(X, ℝ)) :
    functional w x f = ∑ i, w i * f (x i) := by
  simp [functional]

end Definition

section Norm

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Let $X$ be a compact Hausdorff space, let $x_0, \dots, x_{n-1} \in X$ be distinct nodes, and let
$w_0, \dots, w_{n-1} \in \mathbb{R}$. Then the quadrature rule $f \mapsto \sum_i w_i f(x_i)$ has
the norm $\sum_i |w_i|$ in the dual of $C(X)$. This is (2.4.4) and Exercise 2.4.2 of
[han2009theoretical].

The nodes must be distinct: the rule with the weights $1$ and $-1$ at one repeated node is the
zero functional. The inequality $\le$ is the triangle inequality. For $\ge$, the Tietze
extension theorem gives a continuous function of norm $1$ with the value
$\operatorname{sign} w_i$ at each node $x_i$. -/
theorem norm_functional {n : ℕ} (w : Fin n → ℝ) {x : Fin n → X} (hx : Function.Injective x) :
    ‖functional w x‖ = ∑ i, |w i| := by
  have hnn : (0 : ℝ) ≤ ∑ i, |w i| := by positivity
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ hnn fun f => ?_) ?_
  · rw [functional_apply, Real.norm_eq_abs]
    calc |∑ i, w i * f (x i)| ≤ ∑ i, |w i * f (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |w i| * |f (x i)| := by simp [abs_mul]
      _ ≤ ∑ i, |w i| * ‖f‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hfi := f.norm_coe_le_norm (x i)
          rw [Real.norm_eq_abs] at hfi
          exact mul_le_mul_of_nonneg_left hfi (abs_nonneg _)
      _ = (∑ i, |w i|) * ‖f‖ := by rw [Finset.sum_mul]
  · set σ : Fin n → ℝ := fun i => if 0 ≤ w i then 1 else -1 with hσdef
    have hσabs : ∀ i, |σ i| ≤ 1 := by
      intro i
      by_cases hi : 0 ≤ w i <;> simp [hσdef, hi]
    have hσmul : ∀ i, w i * σ i = |w i| := by
      intro i
      by_cases hi : 0 ≤ w i
      · simp [hσdef, hi, abs_of_nonneg hi]
      · simp [hσdef, hi, abs_of_neg (not_le.mp hi)]
    obtain ⟨f, hfnorm, hfnode⟩ := ContinuousMap.exists_norm_le_one_apply_eq hx σ hσabs
    have hval : functional w x f = ∑ i, |w i| := by
      rw [functional_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hfnode i, hσmul i]
    calc ∑ i, |w i| = |functional w x f| := by rw [hval, abs_of_nonneg hnn]
      _ = ‖functional w x f‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖functional w x‖ * ‖f‖ := (functional w x).le_opNorm f
      _ ≤ ‖functional w x‖ * 1 := by gcongr
      _ = ‖functional w x‖ := mul_one _

end Norm

section Exactness

variable {X : Set ℝ} [CompactSpace X] {n : ℕ}

/-- The constant function $1$ on $X$ is a polynomial of degree at most $d$, for every $d$. -/
private theorem one_mem_polyLE (X : Set ℝ) (d : ℕ) : (1 : C(X, ℝ)) ∈ polyLE X d :=
  mem_polyLE_iff.mpr
    ⟨1, Polynomial.degree_one_le.trans (by exact_mod_cast Nat.zero_le d), fun t => by simp⟩

/-- Lagrange interpolation at $n + 1$ distinct nodes fixes every polynomial of degree at most $n$.
-/
private theorem interpolateCLM_of_mem_polyLE {x : Fin (n + 1) → X} (hx : Function.Injective x)
    {p : C(X, ℝ)} (hp : p ∈ polyLE X n) : Lagrange.interpolateCLM x p = p := by
  obtain ⟨q, hq⟩ := (Lagrange.range_interpolateCLM hx).ge hp
  rw [ContinuousLinearMap.coe_coe] at hq
  rw [← hq]
  simpa using ContinuousLinearMap.ext_iff.mp (Lagrange.isIdempotentElem_interpolateCLM hx) q

/-- Let $X \subseteq \mathbb{R}$ and let $L$ be a bounded linear functional on $C(X)$. A quadrature
rule with weights $w_i$ and nodes $x_i \in X$ is **exact to degree $d$** for $L$ if
$$\sum_i w_i\, p(x_i) = L(p)$$
for every polynomial $p$ of degree at most $d$, restricted to $X$.

The polynomials of degree at most $d$ on $X$ are `polyLE X d`. -/
def IsExactOn (L : C(X, ℝ) →L[ℝ] ℝ) {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (d : ℕ) : Prop :=
  ∀ p ∈ polyLE X d, functional w x p = L p

omit [CompactSpace X] in
/-- A rule that is exact to degree $d$ for $L$ is exact to every degree $e \le d$ for $L$. -/
theorem IsExactOn.mono {L : C(X, ℝ) →L[ℝ] ℝ} {m : ℕ} {w : Fin m → ℝ} {x : Fin m → X} {d e : ℕ}
    (h : IsExactOn L w x d) (hed : e ≤ d) : IsExactOn L w x e := fun p hp => by
  obtain ⟨P, hP, hPval⟩ := mem_polyLE_iff.mp hp
  exact h p (mem_polyLE_iff.mpr ⟨P, hP.trans (by exact_mod_cast hed), hPval⟩)

/-- The **degree of exactness** of a quadrature rule for a target functional $L$: the largest $d$
such that the rule is exact to degree $d$ for $L$.

The value is $0$ when the set of these degrees is unbounded, as it is when $L$ is the rule
itself, and also when the set is empty. -/
noncomputable def degreeOfExactness (L : C(X, ℝ) →L[ℝ] ℝ) {m : ℕ} (w : Fin m → ℝ)
    (x : Fin m → X) : ℕ :=
  sSup {d | IsExactOn L w x d}

omit [CompactSpace X] in
/-- If a rule is exact to degree $d$ for $L$, and the set of degrees to which it is exact is
bounded, then $d$ is at most the degree of exactness of the rule. -/
theorem IsExactOn.le_degreeOfExactness {L : C(X, ℝ) →L[ℝ] ℝ} {m : ℕ} {w : Fin m → ℝ}
    {x : Fin m → X} {d : ℕ} (h : IsExactOn L w x d) (hbdd : BddAbove {e | IsExactOn L w x e}) :
    d ≤ degreeOfExactness L w x :=
  le_csSup hbdd h

/-- Let $X \subseteq \mathbb{R}$ and let $L$ be a bounded linear functional on $C(X)$. A quadrature
rule with nodes $x_0, \dots, x_n \in X$ is **interpolatory** for $L$ if its weights are
$$w_i = L(\ell_i), \quad i = 0, \dots, n,$$
where $\ell_i$ is the $i$-th Lagrange basis polynomial of the nodes. The rule is then $L$
applied to the Lagrange interpolant. See [kress1998numerical], §9.1.

The basis function $\ell_i$ on $X$ is `Lagrange.basisCM x i`. -/
def IsInterpolatory (L : C(X, ℝ) →L[ℝ] ℝ) (w : Fin (n + 1) → ℝ) (x : Fin (n + 1) → X) : Prop :=
  ∀ i, w i = L (Lagrange.basisCM x i)

/-- Let $X \subseteq \mathbb{R}$ be compact and let $x_0, \dots, x_n \in X$ be distinct. A rule with
these nodes is exact to degree $n$ for $L$ if and only if the rule equals $L \circ I_n$, where
$I_n$ is Lagrange interpolation at the nodes. -/
theorem isExactOn_iff_functional_eq {L : C(X, ℝ) →L[ℝ] ℝ} {w : Fin (n + 1) → ℝ}
    {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    IsExactOn L w x n ↔ functional w x = L.comp (Lagrange.interpolateCLM x) := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun f => ?_
    have hmem : Lagrange.interpolateCLM x f ∈ polyLE X n :=
      (Lagrange.range_interpolateCLM hx).le ⟨f, rfl⟩
    rw [ContinuousLinearMap.comp_apply, ← h _ hmem, functional_apply, functional_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Lagrange.interpolateCLM_apply_node hx f i]
  · intro h p hp
    rw [h, ContinuousLinearMap.comp_apply, interpolateCLM_of_mem_polyLE hx hp]

/-- Let $X \subseteq \mathbb{R}$ be compact and let $x_0, \dots, x_n \in X$ be distinct. A rule with
these nodes is interpolatory for $L$ if and only if it is exact to degree $n$ for $L$. See
[kress1998numerical], §9.1. -/
theorem isInterpolatory_iff_isExactOn {L : C(X, ℝ) →L[ℝ] ℝ} {w : Fin (n + 1) → ℝ}
    {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    IsInterpolatory L w x ↔ IsExactOn L w x n := by
  have hfix : ∀ i, Lagrange.interpolateCLM x (Lagrange.basisCM x i) = Lagrange.basisCM x i := by
    intro i
    ext t
    rw [Lagrange.interpolateCLM_apply, Finset.sum_eq_single i]
    · rw [Lagrange.basisCM_apply_node_self hx, one_mul]
    · intro j _ hji
      rw [Lagrange.basisCM_apply_node_ne (Ne.symm hji), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hval : ∀ i, functional w x (Lagrange.basisCM x i) = w i := by
    intro i
    rw [functional_apply, Finset.sum_eq_single i]
    · rw [Lagrange.basisCM_apply_node_self hx, mul_one]
    · intro j _ hji
      rw [Lagrange.basisCM_apply_node_ne (Ne.symm hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [isExactOn_iff_functional_eq hx]
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun f => ?_
    have hL : L (Lagrange.interpolateCLM x f) = ∑ i, f (x i) * L (Lagrange.basisCM x i) := by
      have hsum : Lagrange.interpolateCLM x f = ∑ i, f (x i) • Lagrange.basisCM x i := by
        ext t
        rw [Lagrange.interpolateCLM_apply, ContinuousMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ => rfl
      rw [hsum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [ContinuousLinearMap.comp_apply, hL, functional_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [h i, mul_comm]
  · intro h i
    have := congrArg (fun T : C(X, ℝ) →L[ℝ] ℝ => T (Lagrange.basisCM x i)) h
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [hval i, hfix i] at this
    exact this

open Set intervalIntegral in
/-- Let $a \le b$, let $x_0, \dots, x_{m-1} \in [a, b]$, and let
$\alpha_0, \dots, \alpha_{m-1} \in \mathbb{R}$. The formula $\sum_i \alpha_i f(x_i)$ has degree
of exactness at least $d$, that is,
$$\sum_i \alpha_i\, p(x_i) = \int_a^b p(t)\,dt$$
for every real polynomial $p$ of degree at most $d$, if and only if it is exact to degree $d$ in
the sense of `Quadrature.IsExactOn` for the integral functional
`ContinuousMap.integralIccCLM hab b` on $C([a, b])$. -/
theorem isExactOn_integralIccCLM_iff {a b : ℝ} (hab : a ≤ b) {m : ℕ} {x : Fin m → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) (α : Fin m → ℝ) (d : ℕ) :
    Quadrature.IsExactOn (ContinuousMap.integralIccCLM hab b) α
        (fun i => (⟨x i, hx i⟩ : Icc a b)) d ↔
      ∀ p : ℝ[X], p.degree ≤ d → ∑ i, α i * p.eval (x i) = ∫ t in a..b, p.eval t := by
  constructor
  · intro h p hp
    have hmem : p.toContinuousMapOn (Icc a b) ∈ polyLE (Icc a b) d :=
      mem_polyLE_iff.mpr ⟨p, hp, fun t => rfl⟩
    have hval := h _ hmem
    rw [Quadrature.functional_apply, ContinuousMap.integralIccCLM_apply] at hval
    simp only [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] at hval
    rw [hval]
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hab] at ht
    rw [ContinuousMap.coe_IccExtend, IccExtend_of_mem hab _ ht,
      Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply]
  · intro h q hq
    obtain ⟨p, hp, hqp⟩ := mem_polyLE_iff.mp hq
    rw [Quadrature.functional_apply, ContinuousMap.integralIccCLM_apply]
    calc ∑ i, α i * q ⟨x i, hx i⟩ = ∑ i, α i * p.eval (x i) :=
          Finset.sum_congr rfl fun i _ => by rw [hqp]
      _ = ∫ t in a..b, p.eval t := h p hp
      _ = ∫ t in a..b, ContinuousMap.IccExtend hab q t := by
          refine integral_congr fun t ht => ?_
          rw [uIcc_of_le hab] at ht
          rw [ContinuousMap.coe_IccExtend, IccExtend_of_mem hab _ ht, hqp]

end Exactness

section Convergence

variable {a b : ℝ}

/-- **Weierstrass' theorem**: the polynomial functions are dense in $C([a, b])$. -/
private theorem dense_polynomialFunctions (a b : ℝ) :
    Dense ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
      Set C(Set.Icc a b, ℝ)) := by
  have h := polynomialFunctions_closure_eq_top a b
  rw [SetLike.ext'_iff, Subalgebra.topologicalClosure_coe, Algebra.coe_top] at h
  exact dense_iff_closure_eq.2 h

/-- The **Szegő–Pólya convergence criterion**. Let $L$ be a bounded linear functional on
$C([a, b])$. For each $k$, let a rule with distinct nodes $x_{k,i} \in [a, b]$ and weights
$w_{k,i}$ be exact to degree $d_k$ for $L$, where $d_k \to \infty$. Then
$$\sum_i w_{k,i}\, v(x_{k,i}) \to L(v) \quad \text{for every } v \in C([a, b])$$
if and only if there is a constant $C$ with $\sum_i |w_{k,i}| \le C$ for every $k$. See
[han2009theoretical], §2.4.4, and Theorem 9.10 of [kress1998numerical].

Sufficiency is Weierstrass' theorem, because on a polynomial the rules are eventually equal to
$L$, together with the $\varepsilon/3$ argument for a uniformly bounded family. Necessity is the
uniform boundedness principle applied to the rules, whose norms are the sums $\sum_i |w_{k,i}|$. -/
theorem tendsto_iff_bddAbove_sum_abs {m d : ℕ → ℕ} {w : ∀ k, Fin (m k) → ℝ}
    {x : ∀ k, Fin (m k) → Set.Icc a b} (hx : ∀ k, Function.Injective (x k))
    {L : C(Set.Icc a b, ℝ) →L[ℝ] ℝ} (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, IsExactOn L (w k) (x k) (d k)) :
    (∀ v, Tendsto (fun k => functional (w k) (x k) v) atTop (𝓝 (L v))) ↔
      ∃ C, ∀ k, ∑ i, |w k i| ≤ C := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := banach_steinhaus fun v => (h v).exists_norm_le
    exact ⟨C, fun k => by rw [← norm_functional (w k) (hx k)]; exact hC k⟩
  · rintro ⟨C, hC⟩
    have hCk : ∀ k, ‖functional (w k) (x k)‖ ≤ C := fun k => by
      rw [norm_functional (w k) (hx k)]; exact hC k
    refine ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded
      (dense_polynomialFunctions a b) hCk ?_
    rintro v ⟨P, -, rfl⟩
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hd.eventually_ge_atTop P.natDegree] with k hk
    refine (hexact k _ ⟨P, Polynomial.mem_degreeLE.mpr ?_, rfl⟩).symm
    exact P.degree_le_natDegree.trans (by exact_mod_cast hk)

/-- **Rules with nonnegative weights converge.** Let $L$ be a bounded linear functional on
$C([a, b])$. For each $k$, let a rule with distinct nodes $x_{k,i} \in [a, b]$ and weights
$w_{k,i} \ge 0$ be exact to degree $d_k$ for $L$, where $d_k \to \infty$. Then
$\sum_i w_{k,i}\, v(x_{k,i}) \to L(v)$ for every $v \in C([a, b])$. This is Exercise 2.4.3 of
[han2009theoretical].

The sums $\sum_i |w_{k,i}|$ are bounded, because they are the values of the rules at the
constant function $1$, which equal $L(1)$ by exactness. So
`Quadrature.tendsto_iff_bddAbove_sum_abs` applies. -/
theorem tendsto_of_nonneg {m d : ℕ → ℕ} {w : ∀ k, Fin (m k) → ℝ}
    {x : ∀ k, Fin (m k) → Set.Icc a b} (hx : ∀ k, Function.Injective (x k))
    {L : C(Set.Icc a b, ℝ) →L[ℝ] ℝ} (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, IsExactOn L (w k) (x k) (d k)) (hw : ∀ k i, 0 ≤ w k i)
    (v : C(Set.Icc a b, ℝ)) :
    Tendsto (fun k => functional (w k) (x k) v) atTop (𝓝 (L v)) := by
  refine (tendsto_iff_bddAbove_sum_abs hx hd hexact).mpr ⟨L 1, fun k => le_of_eq ?_⟩ v
  have hval := hexact k _ (one_mem_polyLE (Set.Icc a b) (d k))
  rw [functional_apply] at hval
  rw [← hval]
  exact Finset.sum_congr rfl fun i _ => by rw [abs_of_nonneg (hw k i)]; simp

end Convergence

/-! ### Gauss quadrature -/

section Gauss

open OrthogonalPolynomial Polynomial MeasureTheory

variable {μ : Measure ℝ}

/-- **Gauss quadrature.** Let $\mu$ be a weight on $\mathbb{R}$ and let $n \in \mathbb{N}$. There
are distinct nodes $x_0, \dots, x_{n-1}$ and positive weights $w_0, \dots, w_{n-1}$ such that
$$\sum_i w_i\, p(x_i) = \int p\,d\mu$$
for every real polynomial $p$ of degree less than $2n$. This is twice the degree that an
interpolatory rule at $n$ arbitrary nodes reaches. See [kress1998numerical], §9.3, and
[han2009theoretical], §3.5.

The nodes are the $n$ distinct roots of the orthogonal polynomial
`OrthogonalPolynomial.family μ n` (`OrthogonalPolynomial.exists_injective_family_eq_prod`), and
the weights are the integrals of the Lagrange basis polynomials of the nodes. So the rule is
interpolatory, and it is exact to degree $n - 1$ by construction. Exactness to degree $2n - 1$
follows by division with remainder by the orthogonal polynomial: the quotient has degree less
than $n$, so its product with the orthogonal polynomial has integral $0$, and this product
vanishes at the nodes. The weights are positive by exactness at the square of a Lagrange basis
polynomial. `Quadrature.not_forall_eq_integral_of_degree_le` is the converse: no $n$-point rule
is exact to degree $2n$. -/
theorem exists_gauss (hw : IsWeight μ) (n : ℕ) :
    ∃ x w : Fin n → ℝ, Function.Injective x ∧ (∀ i, 0 < w i) ∧
      ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
        ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ := by
  classical
  obtain ⟨x, hxinj, hprod⟩ := exists_injective_family_eq_prod hw n
  obtain ⟨w, hwval⟩ : ∃ w : Fin n → ℝ,
      ∀ i, w i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ := ⟨_, fun _ => rfl⟩
  have hxroot : ∀ i, (family μ n).eval (x i) = 0 := by
    intro i
    rw [hprod, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hcarduniv : (Finset.univ : Finset (Fin n)).card = n := by simp
  -- the rule is interpolatory, hence exact below the number of nodes
  have hlow : ∀ r : ℝ[X], r.degree < (n : WithBot ℕ) →
      ∑ i, w i * r.eval (x i) = ∫ t, r.eval t ∂μ := by
    intro r hr
    have heq : r = Lagrange.interpolate Finset.univ x fun i => r.eval (x i) :=
      Lagrange.eq_interpolate hxinj.injOn (by rw [hcarduniv]; exact hr)
    have hev : ∀ t : ℝ,
        r.eval t = ∑ i, r.eval (x i) * (Lagrange.basis Finset.univ x i).eval t := by
      intro t
      conv_lhs => rw [heq]
      rw [Lagrange.interpolate_apply, eval_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by rw [eval_mul, eval_C]
    rw [integral_congr_ae (Filter.Eventually.of_forall hev),
      integral_finsetSum _ fun i _ => (hw.integrable_eval _).const_mul _]
    refine (Finset.sum_congr rfl fun i _ => ?_).symm
    rw [integral_const_mul, hwval i]
    ring
  -- division with remainder by the orthogonal polynomial doubles the reach
  have hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ := by
    intro p hp
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    have hmonic : (family μ n).Monic := monic_family μ n
    have hfamnat : (family μ n).natDegree = n :=
      natDegree_eq_of_degree_eq_some (degree_family μ n)
    have hnatp : p.natDegree < 2 * n := (natDegree_lt_iff_degree_lt hp0).mpr (by exact_mod_cast hp)
    obtain ⟨q, hqval⟩ : ∃ q : ℝ[X], q = p /ₘ family μ n := ⟨_, rfl⟩
    obtain ⟨r, hrval⟩ : ∃ r : ℝ[X], r = p %ₘ family μ n := ⟨_, rfl⟩
    have hdiv : r + family μ n * q = p := by
      rw [hrval, hqval]
      exact modByMonic_add_div p (family μ n)
    have hrdeg : r.degree < (n : WithBot ℕ) := by
      have h := degree_modByMonic_lt p hmonic
      rw [degree_family] at h
      rwa [hrval]
    have hqdeg : q.degree < (n : WithBot ℕ) := by
      have hqnat : q.natDegree = p.natDegree - n := by
        rw [hqval, natDegree_divByMonic p hmonic, hfamnat]
      refine lt_of_le_of_lt degree_le_natDegree ?_
      exact_mod_cast (by omega : q.natDegree < n)
    have hsplit : ∀ t : ℝ, p.eval t = r.eval t + (family μ n).eval t * q.eval t := by
      intro t
      conv_lhs => rw [← hdiv]
      rw [eval_add, eval_mul]
    have hint : ∫ t, p.eval t ∂μ = ∫ t, r.eval t ∂μ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
        integral_add (hw.integrable_eval r) (hw.integrable_eval_mul _ _),
        integral_family_mul_of_degree_lt hw hqdeg, add_zero]
    have hsum : ∑ i, w i * p.eval (x i) = ∑ i, w i * r.eval (x i) :=
      Finset.sum_congr rfl fun i _ => by rw [hsplit (x i), hxroot i]; ring
    rw [hsum, hlow r hrdeg, hint]
  refine ⟨x, w, hxinj, fun i => ?_, hexact⟩
  -- the weights are positive: apply exactness to the square of a Lagrange basis function
  have hne : Lagrange.basis Finset.univ x i ≠ 0 :=
    Lagrange.basis_ne_zero hxinj.injOn (Finset.mem_univ i)
  have hbnat : (Lagrange.basis Finset.univ x i).natDegree = n - 1 := by
    rw [Lagrange.natDegree_basis hxinj.injOn (Finset.mem_univ i), hcarduniv]
  have hn : 0 < n := Fin.pos i
  have hdeg2 : ((Lagrange.basis Finset.univ x i) ^ 2).degree < ((2 * n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    rw [natDegree_pow, hbnat]
    exact_mod_cast (by omega : 2 * (n - 1) < 2 * n)
  have h1 := hexact _ hdeg2
  have hlhs : ∑ j, w j * ((Lagrange.basis Finset.univ x i) ^ 2).eval (x j) = w i := by
    rw [Finset.sum_eq_single i]
    · rw [eval_pow, Lagrange.eval_basis_self hxinj.injOn (Finset.mem_univ i)]
      ring
    · intro j _ hji
      rw [eval_pow, Lagrange.eval_basis_of_ne (Ne.symm hji) (Finset.mem_univ j)]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hlhs] at h1
  rw [h1]
  exact hw.integral_eval_pos (pow_ne_zero 2 hne) fun t => by rw [eval_pow]; positivity

/-- Let $\mu$ be a weight on $\mathbb{R}$. No rule with $n$ nodes $x_i$ and weights $w_i$ satisfies
$\sum_i w_i\, p(x_i) = \int p\,d\mu$ for every real polynomial $p$ of degree at most $2n$. So
Gauss quadrature is optimal. See [kress1998numerical], §9.3.

The square of the nodal polynomial $\prod_i (X - x_i)$ has degree $2n$. The rule gives it the
value $0$, but its integral against the weight is positive. -/
theorem not_forall_eq_integral_of_degree_le (hw : IsWeight μ) {n : ℕ} (x w : Fin n → ℝ) :
    ¬ ∀ p : ℝ[X], p.degree ≤ ((2 * n : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ := by
  classical
  intro h
  obtain ⟨q, hqval⟩ : ∃ q : ℝ[X], q = ∏ i, (X - C (x i)) := ⟨_, rfl⟩
  have hqmonic : q.Monic := by
    rw [hqval]
    exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)
  have hqnat : q.natDegree = n := by
    rw [hqval, natDegree_prod _ _ fun i _ => (monic_X_sub_C (x i)).ne_zero]
    simp
  have hdeg : (q ^ 2).degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    refine degree_le_natDegree.trans ?_
    rw [natDegree_pow, hqnat]
  have hzero : ∀ i, q.eval (x i) = 0 := by
    intro i
    rw [hqval, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hlhs : ∑ i, w i * (q ^ 2).eval (x i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [eval_pow, hzero i]
    ring
  have hpos : 0 < ∫ t, (q ^ 2).eval t ∂μ :=
    hw.integral_eval_pos (pow_ne_zero 2 hqmonic.ne_zero) fun t => by rw [eval_pow]; positivity
  rw [← h _ hdeg, hlhs] at hpos
  exact absurd hpos (lt_irrefl 0)

end Gauss

/-! ### Exactness with respect to a weight -/

section ExactnessMeasure

open OrthogonalPolynomial Polynomial MeasureTheory

variable {μ : Measure ℝ} {n : ℕ}

/-- Let $\mu$ be a measure on $\mathbb{R}$. A rule with weights $w_i$ and nodes $x_i \in \mathbb{R}$
is **exact to degree $d$ for $\mu$** if
$$\sum_i w_i\, p(x_i) = \int p\,d\mu$$
for every real polynomial $p$ of degree at most $d$. This is the degree of exactness of
[quarteroni2000numerical], §10.2.

Unlike `Quadrature.IsExactOn`, which is stated for a functional on `C(X, ℝ)`, this definition is
stated for a measure on $\mathbb{R}$, so that it covers weights of unbounded support, such as
the Laguerre and Hermite weights. -/
def IsExactOnMeasure (μ : Measure ℝ) {n : ℕ} (w x : Fin n → ℝ) (d : ℕ) : Prop :=
  ∀ p : ℝ[X], p.degree ≤ d → ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ

/-- A rule that is exact to degree $d$ for $\mu$ is exact to every degree $e \le d$ for $\mu$. -/
theorem IsExactOnMeasure.mono {w x : Fin n → ℝ} {d e : ℕ} (h : IsExactOnMeasure μ w x d)
    (hed : e ≤ d) : IsExactOnMeasure μ w x e := fun p hp =>
  h p (hp.trans (by exact_mod_cast hed))

/-- For a polynomial $p$, $\deg p < d + 1$ if and only if $\deg p \le d$. -/
private theorem degree_lt_succ_iff {p : ℝ[X]} {d : ℕ} :
    p.degree < ((d + 1 : ℕ) : WithBot ℕ) ↔ p.degree ≤ d := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [degree_eq_natDegree hp]
    exact_mod_cast Nat.lt_succ_iff

/-- A rule is exact to degree $d$ for $\mu$ if and only if $\sum_i w_i\, p(x_i) = \int p\,d\mu$ for
every real polynomial $p$ with $\deg p < d + 1$. This is the strict form of the degree condition
that `Quadrature.exists_gauss` uses. -/
theorem isExactOnMeasure_iff_forall_degree_lt {w x : Fin n → ℝ} {d : ℕ} :
    IsExactOnMeasure μ w x d ↔ ∀ p : ℝ[X], p.degree < ((d + 1 : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ :=
  forall_congr' fun _ => imp_congr_left degree_lt_succ_iff.symm

/-- Let $\mu$ be a measure on $\mathbb{R}$. A rule with nodes $x_0, \dots, x_n$ is **interpolatory
for $\mu$** if its weights are
$$w_i = \int \ell_i\,d\mu, \quad i = 0, \dots, n,$$
where $\ell_i$ is the $i$-th Lagrange basis polynomial of the nodes. The rule is then the
integral of the Lagrange interpolant. This is (10.14) of [quarteroni2000numerical], and it is
the measure version of `Quadrature.IsInterpolatory`. -/
def IsInterpolatoryMeasure (μ : Measure ℝ) (w x : Fin (n + 1) → ℝ) : Prop :=
  ∀ i, w i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ

/-- For distinct nodes $x_0, \dots, x_n$, the rule with weights $w_j$ takes the value $w_i$ at the
$i$-th Lagrange basis polynomial of the nodes. -/
private theorem sum_mul_eval_basis {w x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (i : Fin (n + 1)) : ∑ j, w j * (Lagrange.basis Finset.univ x i).eval (x j) = w i := by
  rw [Finset.sum_eq_single i]
  · rw [Lagrange.eval_basis_self hx.injOn (Finset.mem_univ i), mul_one]
  · intro j _ hji
    rw [Lagrange.eval_basis_of_ne (Ne.symm hji) (Finset.mem_univ j), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Let $\mu$ be a weight on $\mathbb{R}$ and let $x_0, \dots, x_n$ be distinct. A rule with these
nodes is interpolatory for $\mu$ if and only if it is exact to degree $n$ for $\mu$. See
[quarteroni2000numerical], §10.2, (10.14), and [kress1998numerical], §9.1.

Exactness at a Lagrange basis polynomial gives the weight. Conversely, every polynomial of
degree at most $n$ is its own Lagrange interpolant. -/
theorem isInterpolatoryMeasure_iff_isExactOnMeasure (hw : IsWeight μ) {w x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) : IsInterpolatoryMeasure μ w x ↔ IsExactOnMeasure μ w x n := by
  have hcard : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
  constructor
  · intro h p hp
    have heq : p = Lagrange.interpolate Finset.univ x fun i => p.eval (x i) :=
      Lagrange.eq_interpolate hx.injOn (by rw [hcard]; exact degree_lt_succ_iff.mpr hp)
    have hev : ∀ t : ℝ,
        p.eval t = ∑ i, p.eval (x i) * (Lagrange.basis Finset.univ x i).eval t := by
      intro t
      conv_lhs => rw [heq]
      rw [Lagrange.interpolate_apply, eval_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by rw [eval_mul, eval_C]
    rw [integral_congr_ae (Filter.Eventually.of_forall hev),
      integral_finsetSum _ fun i _ => (hw.integrable_eval _).const_mul _]
    refine (Finset.sum_congr rfl fun i _ => ?_).symm
    rw [integral_const_mul, h i]
    ring
  · intro h i
    have hdeg : (Lagrange.basis Finset.univ x i).degree ≤ n := by
      rw [Lagrange.degree_basis hx.injOn (Finset.mem_univ i), hcard]
      simp
    rw [← h _ hdeg, sum_mul_eval_basis hx]

/-- Let $\omega$ be the nodal polynomial of $n + 1$ nodes and let $m \ge 1$. Every polynomial of
degree at most $n + m$ is $\omega q + r$ with $\deg q \le m - 1$ and $\deg r \le n$. -/
private theorem exists_nodal_mul_add {x : Fin (n + 1) → ℝ} {m : ℕ} (hm : 1 ≤ m) {p : ℝ[X]}
    (hp : p.degree ≤ ((n + m : ℕ) : WithBot ℕ)) :
    ∃ q r : ℝ[X], p = Lagrange.nodal Finset.univ x * q + r ∧
      q.degree ≤ ((m - 1 : ℕ) : WithBot ℕ) ∧ r.degree ≤ n := by
  have hmonic : (Lagrange.nodal Finset.univ x).Monic := Lagrange.nodal_monic
  have hnat : (Lagrange.nodal Finset.univ x).natDegree = n + 1 := by
    rw [Lagrange.natDegree_nodal]; simp
  refine ⟨p /ₘ Lagrange.nodal Finset.univ x, p %ₘ Lagrange.nodal Finset.univ x, ?_, ?_, ?_⟩
  · rw [add_comm]
    exact (modByMonic_add_div p _).symm
  · refine degree_le_natDegree.trans ?_
    rw [natDegree_divByMonic p hmonic, hnat]
    have hpnat : p.natDegree ≤ n + m := natDegree_le_iff_degree_le.mpr hp
    exact_mod_cast (by omega : p.natDegree - (n + 1) ≤ m - 1)
  · have h := degree_modByMonic_lt p hmonic
    rw [degree_eq_natDegree hmonic.ne_zero, hnat] at h
    exact degree_lt_succ_iff.mp h

/-- **Jacobi's theorem.** Let $\mu$ be a weight on $\mathbb{R}$, let $m \ge 1$, and let
$x_0, \dots, x_n$ be distinct. A rule with these nodes and weights $w_i$ is exact to degree
$n + m$ for $\mu$ if and only if it is interpolatory for $\mu$ and the nodal polynomial
$\omega = \prod_i (X - x_i)$ satisfies
$$\int \omega\, p\,d\mu = 0$$
for every real polynomial $p$ of degree at most $m - 1$. This is Theorem 10.1 of
[quarteroni2000numerical].

For sufficiency, divide $f \in \mathbb{P}_{n+m}$ by the monic polynomial $\omega$:
$f = \omega q + r$ with $\deg q \le m - 1$ and $\deg r \le n$. The rule gives $\omega q$ the
value $0$ because $\omega q$ vanishes at the nodes, the integral of $\omega q$ is $0$ by the
orthogonality, and an interpolatory rule is exact on $r$. For necessity, exactness to degree
$n + m \ge n$ makes the rule interpolatory, and for $p \in \mathbb{P}_{m-1}$ the polynomial
$\omega p \in \mathbb{P}_{n+m}$ vanishes at the nodes, so its integral is $0$.

The nodal polynomial is `Lagrange.nodal Finset.univ x`. -/
theorem isExactOnMeasure_add_iff (hw : IsWeight μ) {m : ℕ} (hm : 1 ≤ m)
    {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (w : Fin (n + 1) → ℝ) :
    IsExactOnMeasure μ w x (n + m) ↔
      IsInterpolatoryMeasure μ w x ∧ ∀ p : ℝ[X], p.degree ≤ ((m - 1 : ℕ) : WithBot ℕ) →
        ∫ t, (Lagrange.nodal Finset.univ x).eval t * p.eval t ∂μ = 0 := by
  have hroot : ∀ i, (Lagrange.nodal Finset.univ x).eval (x i) = 0 := fun i =>
    Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hnodaldeg : (Lagrange.nodal Finset.univ x).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [Lagrange.degree_nodal]; simp
  constructor
  · intro h
    refine ⟨(isInterpolatoryMeasure_iff_isExactOnMeasure hw hx).mpr (h.mono (by omega)),
      fun p hp => ?_⟩
    have hdeg : (Lagrange.nodal Finset.univ x * p).degree ≤ ((n + m : ℕ) : WithBot ℕ) := by
      refine (degree_mul_le _ _).trans ?_
      rw [hnodaldeg]
      calc ((n + 1 : ℕ) : WithBot ℕ) + p.degree
          ≤ ((n + 1 : ℕ) : WithBot ℕ) + ((m - 1 : ℕ) : WithBot ℕ) := by gcongr
        _ = ((n + m : ℕ) : WithBot ℕ) := by
            norm_cast
            omega
    have h2 : ∑ i, w i * (Lagrange.nodal Finset.univ x * p).eval (x i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [eval_mul, hroot i]; ring
    calc ∫ t, (Lagrange.nodal Finset.univ x).eval t * p.eval t ∂μ
        = ∫ t, (Lagrange.nodal Finset.univ x * p).eval t ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun t => (eval_mul).symm)
      _ = 0 := (h _ hdeg).symm.trans h2
  · rintro ⟨hint, horth⟩ p hp
    obtain ⟨q, r, rfl, hq, hr⟩ := exists_nodal_mul_add (x := x) hm hp
    have hsum : ∑ i, w i * (Lagrange.nodal Finset.univ x * q + r).eval (x i) =
        ∑ i, w i * r.eval (x i) :=
      Finset.sum_congr rfl fun i _ => by rw [eval_add, eval_mul, hroot i]; ring
    have hev : ∀ t : ℝ, (Lagrange.nodal Finset.univ x * q + r).eval t =
        (Lagrange.nodal Finset.univ x).eval t * q.eval t + r.eval t := fun t => by
      rw [eval_add, eval_mul]
    rw [hsum, integral_congr_ae (Filter.Eventually.of_forall hev),
      integral_add (hw.integrable_eval_mul _ _) (hw.integrable_eval r), horth q hq, zero_add]
    exact (isInterpolatoryMeasure_iff_isExactOnMeasure hw hx).mp hint r hr

/-- Let $\mu$ be a weight on $\mathbb{R}$. No rule with $n + 1$ nodes is exact to degree $2n + 2$
for $\mu$, so the degree $2n + 1$ of the Gauss rule is the maximum. This is Corollary 10.1 of
[quarteroni2000numerical], and a restatement of
`Quadrature.not_forall_eq_integral_of_degree_le`. -/
theorem not_isExactOnMeasure_two_mul_add_two (hw : IsWeight μ) (w x : Fin (n + 1) → ℝ) :
    ¬ IsExactOnMeasure μ w x (2 * n + 2) := fun h =>
  not_forall_eq_integral_of_degree_le hw x w fun p hp =>
    h p (hp.trans (by exact_mod_cast (by omega : 2 * n + 2 ≤ 2 * (n + 1))))

/-- **The Gauss nodes are the roots of the orthogonal polynomial.** Let $\mu$ be a weight on
$\mathbb{R}$ and let $x_0, \dots, x_n$ be distinct. A rule with these nodes and weights $w_i$ is
exact to degree $2n + 1$ for $\mu$ if and only if its nodal polynomial $\prod_i (X - x_i)$
equals the monic orthogonal polynomial $p_{n+1}$ of $\mu$ and the rule is interpolatory for
$\mu$. So the nodes are the roots of $p_{n+1}$. This is (10.16) of [quarteroni2000numerical].

This is Jacobi's theorem `Quadrature.isExactOnMeasure_add_iff` at $m = n + 1$. A monic
polynomial of degree $n + 1$ that is orthogonal to every polynomial of degree at most $n$
differs from $p_{n+1}$ by a polynomial of degree at most $n$ that is orthogonal to
$\mathbb{P}_n$, so it equals $p_{n+1}$. The polynomial $p_{n+1}$ is
`OrthogonalPolynomial.family μ (n + 1)`. -/
theorem isExactOnMeasure_two_mul_add_one_iff (hw : IsWeight μ) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (w : Fin (n + 1) → ℝ) :
    IsExactOnMeasure μ w x (2 * n + 1) ↔
      Lagrange.nodal Finset.univ x = family μ (n + 1) ∧ IsInterpolatoryMeasure μ w x := by
  have hnodaldeg : (Lagrange.nodal Finset.univ x).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [Lagrange.degree_nodal]; simp
  have h2 : 2 * n + 1 = n + (n + 1) := by omega
  rw [h2, isExactOnMeasure_add_iff hw (by omega) hx w, Nat.add_sub_cancel, and_comm]
  refine and_congr_left fun _ => ⟨fun h => ?_, fun h p hp => ?_⟩
  · refine sub_eq_zero.mp (eq_zero_of_degree_lt hw (n := n + 1) ?_ ?_)
    · have := degree_sub_lt_left (p := Lagrange.nodal Finset.univ x) (q := family μ (n + 1))
        (by rw [hnodaldeg, degree_family]) Lagrange.nodal_ne_zero
        (by rw [Lagrange.nodal_monic.leadingCoeff, (monic_family μ (n + 1)).leadingCoeff])
      rwa [hnodaldeg] at this
    · intro k hk
      have hkdeg : (family μ k).degree ≤ n := by
        rw [degree_family]; exact_mod_cast Nat.lt_succ_iff.mp hk
      have hev : ∀ t : ℝ, (Lagrange.nodal Finset.univ x - family μ (n + 1)).eval t *
          (family μ k).eval t = (Lagrange.nodal Finset.univ x).eval t * (family μ k).eval t -
            (family μ (n + 1)).eval t * (family μ k).eval t := fun t => by
        rw [eval_sub, sub_mul]
      rw [integral_congr_ae (Filter.Eventually.of_forall hev),
        integral_sub (hw.integrable_eval_mul _ _) (hw.integrable_eval_mul _ _), h _ hkdeg,
        integral_family_mul_family hw (by omega), sub_zero]
  · rw [h]
    exact integral_family_mul_of_degree_lt hw (degree_lt_succ_iff.mpr hp)

/-- Let $\mu$ be a measure on $\mathbb{R}$ with $\mu(\mathbb{R} \setminus [a, b]) = 0$, and let $L$
be a bounded linear functional on $C([a, b])$ with $L(f) = \int f\,d\mu$ for every $f$, where
$\mu$ is read as a measure on $[a, b]$. For nodes $x_i \in [a, b]$, weights $w_i$ and
$d \in \mathbb{N}$, the rule is exact to degree $d$ for $\mu$ if and only if it is exact to
degree $d$ for $L$ in the sense of `Quadrature.IsExactOn`. So the Szegő–Pólya criterion
`Quadrature.tendsto_of_nonneg` applies to the Gauss and Gauss–Lobatto rules, which are stated
for measures.

The measure on $[a, b]$ is `μ.comap Subtype.val`. -/
theorem isExactOnMeasure_iff_isExactOn {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (w : Fin n → ℝ) (x : Fin n → Set.Icc a b) {L : C(Set.Icc a b, ℝ) →L[ℝ] ℝ}
    (hL : ∀ f : C(Set.Icc a b, ℝ), L f = ∫ t, f t ∂(μ.comap Subtype.val)) (d : ℕ) :
    IsExactOnMeasure μ w (Subtype.val ∘ x) d ↔ IsExactOn L w x d := by
  have hae : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  have hint : ∀ P : ℝ[X], ∫ t : Set.Icc a b, P.eval (t : ℝ) ∂(μ.comap Subtype.val) =
      ∫ t, P.eval t ∂μ := by
    intro P
    have h1 := integral_subtype_comap (μ := μ) (s := Set.Icc a b) measurableSet_Icc
      fun t => P.eval t
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1
  constructor
  · intro h f hf
    obtain ⟨P, hP, hfP⟩ := mem_polyLE_iff.mp hf
    rw [functional_apply, hL]
    have hfun : (fun t : Set.Icc a b => f t) = fun t : Set.Icc a b => P.eval (t : ℝ) :=
      funext hfP
    rw [hfun, hint, ← h P hP]
    exact Finset.sum_congr rfl fun i _ => by rw [hfP]; rfl
  · intro h P hP
    have hmem : P.toContinuousMapOn (Set.Icc a b) ∈ polyLE (Set.Icc a b) d :=
      mem_polyLE_iff.mpr ⟨P, hP, fun t => by simp⟩
    have h1 := h _ hmem
    rw [functional_apply, hL] at h1
    simp only [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] at h1
    rw [hint] at h1
    exact h1

/-- **Change of variable.** Let $\mu$ be a measure on $\mathbb{R}$, let a rule with weights $w_i$
and nodes $x_i$ be exact to degree $r$ for $\mu$, and let $\varphi(t) = ct + d$ with
$c, d \in \mathbb{R}$. Then the rule with the same weights and the nodes $\varphi(x_i)$ is exact
to degree $r$ for the image measure $\varphi_* \mu$. See Remark 10.3 of
[quarteroni2000numerical].

The proof uses that $p \circ \varphi$ is a polynomial of degree at most $\deg p$. -/
theorem isExactOnMeasure_map_affine {w x : Fin n → ℝ} {r : ℕ} (h : IsExactOnMeasure μ w x r)
    (c d : ℝ) :
    IsExactOnMeasure (μ.map fun t => c * t + d) w ((fun t => c * t + d) ∘ x) r := by
  intro p hp
  have hφ : Measurable fun t : ℝ => c * t + d := by fun_prop
  rw [integral_map hφ.aemeasurable p.continuous.aestronglyMeasurable]
  have hcomp : ∀ t : ℝ, p.eval (c * t + d) = (p.comp (C c * X + C d)).eval t := fun t => by
    simp [eval_comp]
  simp only [Function.comp_apply, hcomp]
  refine h _ ?_
  refine degree_le_natDegree.trans ?_
  rw [natDegree_comp]
  have h1 : (C c * X + C d : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have h2 : p.natDegree ≤ r := natDegree_le_iff_degree_le.mpr hp
  exact_mod_cast (Nat.mul_le_mul h2 h1).trans (by omega)

/-- **Change of interval for Lebesgue measure.** Let $a < b$, and let a rule with nodes $\xi_j$ and
weights $\beta_j$ be exact to degree $r$ for Lebesgue measure on $[-1, 1]$. Then the rule with
the nodes $\frac{b - a}{2}\xi_j + \frac{a + b}{2}$ and the weights $\frac{b - a}{2}\beta_j$ is
exact to degree $r$ for Lebesgue measure on $[a, b]$.

This is Remark 10.3 of [quarteroni2000numerical], with the affine map corrected to
$\varphi(\xi) = \frac{b - a}{2}\xi + \frac{a + b}{2}$. -/
theorem isExactOnMeasure_volume_Icc_of_affine {a b : ℝ} (hab : a < b) {w x : Fin n → ℝ} {r : ℕ}
    (h : IsExactOnMeasure (volume.restrict (Set.Icc (-1 : ℝ) 1)) w x r) :
    IsExactOnMeasure (volume.restrict (Set.Icc a b)) (fun i => (b - a) / 2 * w i)
      (fun i => (b - a) / 2 * x i + (a + b) / 2) r := by
  intro p hp
  have hcomp : ∀ t : ℝ, p.eval ((b - a) / 2 * t + (a + b) / 2) =
      (p.comp (C ((b - a) / 2) * X + C ((a + b) / 2))).eval t := fun t => by simp [eval_comp]
  have hdeg : (p.comp (C ((b - a) / 2) * X + C ((a + b) / 2))).degree ≤ r := by
    refine degree_le_natDegree.trans ?_
    rw [natDegree_comp]
    have h1 : (C ((b - a) / 2) * X + C ((a + b) / 2) : ℝ[X]).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
      exact (natDegree_C_mul_le _ _).trans (by simp)
    have h2 : p.natDegree ≤ r := natDegree_le_iff_degree_le.mpr hp
    exact_mod_cast (Nat.mul_le_mul h2 h1).trans (by omega)
  have hrule := h _ hdeg
  simp only [hcomp]
  calc ∑ i, (b - a) / 2 * w i * (p.comp (C ((b - a) / 2) * X + C ((a + b) / 2))).eval (x i)
      = (b - a) / 2 * ∑ i, w i * (p.comp (C ((b - a) / 2) * X + C ((a + b) / 2))).eval (x i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = (b - a) / 2 * ∫ t in (-1 : ℝ)..1, p.eval ((b - a) / 2 * t + (a + b) / 2) := by
        rw [hrule, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        simp only [hcomp]
    _ = ∫ t in ((b - a) / 2 * (-1) + (a + b) / 2)..((b - a) / 2 * 1 + (a + b) / 2), p.eval t := by
        rw [← intervalIntegral.smul_integral_comp_mul_add, smul_eq_mul]
    _ = ∫ t in Set.Icc a b, p.eval t := by
        rw [show (b - a) / 2 * (-1) + (a + b) / 2 = a by ring,
          show (b - a) / 2 * 1 + (a + b) / 2 = b by ring, intervalIntegral.integral_of_le hab.le,
          integral_Icc_eq_integral_Ioc]

/-! ### Positivity of weights, interpolatory rules, and convergence -/

/-- Let $\mu$ be a weight on $\mathbb{R}$, and let a rule with weights $w_k$ and nodes $x_k$ be
exact to degree $d$ for $\mu$. Let $p \ne 0$ be a real polynomial of degree at most $d$ with
$p \ge 0$ $\mu$-almost everywhere, $p(x_k) = 0$ for every $k \ne i$, and $p(x_i) > 0$. Then
$w_i > 0$, because $w_i\, p(x_i) = \int p\,d\mu > 0$. -/
theorem pos_of_isExactOnMeasure (hw : IsWeight μ) {n : ℕ} {w x : Fin n → ℝ} {d : ℕ}
    (hexact : IsExactOnMeasure μ w x d) {p : ℝ[X]} (hp : p.degree ≤ d) (hp0 : p ≠ 0)
    (hnn : ∀ᵐ t ∂μ, 0 ≤ p.eval t) (i : Fin n) (hzero : ∀ k, k ≠ i → p.eval (x k) = 0)
    (hpos : 0 < p.eval (x i)) : 0 < w i := by
  have h := hexact p hp
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [hzero k hk, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h)] at h
  have hint := hw.integral_eval_pos_of_ae_nonneg hp0 hnn
  rw [← h] at hint
  exact (mul_pos_iff_of_pos_right hpos).mp hint

/-- Let $\mu$ be a measure on $\mathbb{R}$, and let $x_0, \dots, x_N$ be distinct roots of the monic
orthogonal polynomial $p_{N+1}$ of $\mu$. Then their nodal polynomial $\prod_j (X - x_j)$ equals
$p_{N+1}$. -/
theorem nodal_eq_family_of_forall_eval_eq_zero (μ : Measure ℝ) {N : ℕ} {x : Fin (N + 1) → ℝ}
    (hx : Function.Injective x) (hroot : ∀ j, (family μ (N + 1)).eval (x j) = 0) :
    Lagrange.nodal Finset.univ x = family μ (N + 1) := by
  refine (sub_eq_zero.mp ?_).symm
  refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hx.injOn ?_
    fun j _ => ?_
  · have := degree_sub_lt_left (p := family μ (N + 1)) (q := Lagrange.nodal Finset.univ x)
      (by rw [degree_family, Lagrange.degree_nodal]; simp) (family_ne_zero _ _)
      (by rw [(monic_family _ _).leadingCoeff, Lagrange.nodal_monic.leadingCoeff])
    rw [degree_family] at this
    simpa using this
  · rw [eval_sub, hroot j, Lagrange.eval_nodal_at_node (Finset.mem_univ j), sub_zero]

/-- Let $\mu$ be a weight on $\mathbb{R}$, and let a rule with nodes $x_0, \dots, x_n$ and weights
$\alpha_i$ be interpolatory for $\mu$, that is, $\alpha_i = \int \ell_i\,d\mu$. Then for every
function $f \colon \mathbb{R} \to \mathbb{R}$
$$\sum_i \alpha_i\, f(x_i) = \int \Pi_n f\,d\mu,$$
where $\Pi_n f$ is the Lagrange interpolant of $f$ at the nodes. -/
theorem sum_mul_eq_integral_interpolate (hw : IsWeight μ) {x α : Fin (n + 1) → ℝ}
    (hint : IsInterpolatoryMeasure μ α x) (f : ℝ → ℝ) :
    ∑ i, α i * f (x i) =
      ∫ t, (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t ∂μ := by
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
  rw [integral_finsetSum _ fun i _ => (hw.integrable_eval _).const_mul _]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul, hint i, mul_comm]

/-- Let $\mu$ be a weight on $\mathbb{R}$, and let a rule with $n + 1$ distinct nodes $x_i$ and
weights $\alpha_i$ be exact to degree $d \ge 2n$ for $\mu$. Then every weight is positive.
Exactness at the square $\ell_i^2 \in \mathbb{P}_{2n}$ of the $i$-th Lagrange basis polynomial
gives $\alpha_i = \int \ell_i^2\,d\mu > 0$. -/
theorem pos_of_isExactOnMeasure_of_le (hw : IsWeight μ) {x α : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) {d : ℕ} (hd : 2 * n ≤ d) (hexact : IsExactOnMeasure μ α x d)
    (i : Fin (n + 1)) : 0 < α i := by
  refine pos_of_isExactOnMeasure hw hexact (p := Lagrange.basis Finset.univ x i ^ 2) ?_
    (pow_ne_zero 2 (Lagrange.basis_ne_zero hx.injOn (Finset.mem_univ i)))
    (Eventually.of_forall fun t => by rw [eval_pow]; positivity) i (fun k hk => ?_) ?_
  · refine degree_le_of_natDegree_le ?_
    rw [natDegree_pow, Lagrange.natDegree_basis hx.injOn (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
    exact hd
  · rw [eval_pow, Lagrange.eval_basis_of_ne (Ne.symm hk) (Finset.mem_univ k)]
    norm_num
  · rw [eval_pow, Lagrange.eval_basis_self hx.injOn (Finset.mem_univ i)]
    norm_num

/-- Let $\sigma$ be a permutation of the indices. The rule with weights $w \circ \sigma$ and nodes
$x \circ \sigma$ is exact to degree $d$ for $\mu$ if and only if the rule with weights $w$ and
nodes $x$ is exact to degree $d$ for $\mu$. -/
theorem isExactOnMeasure_comp_equiv {m : ℕ} {w x : Fin m → ℝ}
    (σ : Equiv.Perm (Fin m)) {d : ℕ} :
    IsExactOnMeasure μ (w ∘ σ) (x ∘ σ) d ↔ IsExactOnMeasure μ w x d := by
  simp only [IsExactOnMeasure, Function.comp_apply]
  exact forall₂_congr fun p _ => by rw [Equiv.sum_comp σ fun i => w i * p.eval (x i)]

section

open Set

/-- The integral against a finite measure on $[a, b]$, as a bounded linear functional on
$C([a, b])$. -/
private noncomputable def integralCLM {a b : ℝ} (ν : Measure (Icc a b)) [IsFiniteMeasure ν] :
    C(Icc a b, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (α := Icc a b) (E := ℝ) (μ := ν)).comp (ContinuousMap.toLp 1 ν ℝ)

private theorem integralCLM_apply {a b : ℝ} (ν : Measure (Icc a b)) [IsFiniteMeasure ν]
    (f : C(Icc a b, ℝ)) : integralCLM ν f = ∫ t, f t ∂ν := by
  rw [integralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (μ := ν) (𝕜 := ℝ) f)

/-- **Convergence of rules with nonnegative weights.** Let $\mu$ be a finite measure on $\mathbb{R}$
with $\mu(\mathbb{R} \setminus [a, b]) = 0$. For each $k$, let a rule with distinct nodes
$x_{k,i} \in [a, b]$ and weights $\alpha_{k,i} \ge 0$ be exact to degree $d_k$ for $\mu$, where
$d_k \to \infty$. Then for every function $f$ that is continuous on $[a, b]$,
$$\sum_i \alpha_{k,i}\, f(x_{k,i}) \to \int f\,d\mu.$$
-/
theorem tendsto_of_isExactOnMeasure [IsFiniteMeasure μ] {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0)
    {m d : ℕ → ℕ} {x α : ∀ k, Fin (m k) → ℝ} (hx : ∀ k, Function.Injective (x k))
    (hmem : ∀ k i, x k i ∈ Icc a b) (hα : ∀ k i, 0 ≤ α k i) (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, IsExactOnMeasure μ (α k) (x k) (d k)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun k => ∑ i, α k i * f (x k i)) atTop (𝓝 (∫ t, f t ∂μ)) := by
  set ν : Measure (Icc a b) := μ.comap Subtype.val with hν
  set L : C(Icc a b, ℝ) →L[ℝ] ℝ := integralCLM ν with hL
  have hLapply : ∀ g : C(Icc a b, ℝ), L g = ∫ t, g t ∂(μ.comap Subtype.val) := fun g =>
    integralCLM_apply ν g
  set x' : ∀ k, Fin (m k) → Icc a b := fun k i => ⟨x k i, hmem k i⟩ with hx'
  have hx'inj : ∀ k, Function.Injective (x' k) := fun k i j h =>
    hx k (congrArg Subtype.val h)
  have hexact' : ∀ k, IsExactOn L (α k) (x' k) (d k) := fun k =>
    (isExactOnMeasure_iff_isExactOn hsupp (α k) (x' k) hLapply (d k)).mp (hexact k)
  set g : C(Icc a b, ℝ) := ⟨fun t => f t, hf.domRestrict⟩ with hg
  have hae : ∀ᵐ t ∂μ, t ∈ Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  have hLg : L g = ∫ t, f t ∂μ := by
    rw [hLapply]
    have h1 := integral_subtype_comap (μ := μ) (s := Icc a b) measurableSet_Icc fun t => f t
    rw [Measure.restrict_eq_self_of_ae_mem hae] at h1
    exact h1
  have h := tendsto_of_nonneg hx'inj hd hexact' hα g
  rw [hLg] at h
  refine h.congr fun k => ?_
  rw [functional_apply]
  rfl

end

/-- **The nodes of an exact rule lie in the interval of the measure.** Let $\mu$ be a measure on
$\mathbb{R}$ with $\mu(\mathbb{R} \setminus [a, b]) = 0$ for which every polynomial is
integrable, and let a rule with weights $w_i$ and nodes $x_i$ be exact to degree $d$ for $\mu$.
Let $P$ be a real polynomial with $\deg P + 1 \le d$, $P \ge 0$ on $[a, b]$, $P(x_i) = 0$ for
every $i \ne j$, and $w_j P(x_j) > 0$. Then $x_j \in [a, b]$.

Otherwise the integral $\int (x_j - t)\, P(t)\,d\mu$, or $\int (t - x_j)\, P(t)\,d\mu$, would be
$0$ by exactness and at least $\operatorname{dist}(x_j, [a, b]) \int P\,d\mu > 0$. -/
theorem mem_Icc_of_isExactOnMeasure {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) {d : ℕ} {w x : Fin n → ℝ}
    (hexact : IsExactOnMeasure μ w x d) {P : ℝ[X]} (hPdeg : P.natDegree + 1 ≤ d)
    (hPnonneg : ∀ t ∈ Set.Icc a b, 0 ≤ P.eval t) {j : Fin n}
    (hPzero : ∀ i, i ≠ j → P.eval (x i) = 0) (hpos : 0 < w j * P.eval (x j)) :
    x j ∈ Set.Icc a b := by
  have hae : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  have hdeg : ∀ Q : ℝ[X], Q.natDegree ≤ 1 → (Q * P).degree ≤ d := fun Q hQ =>
    degree_le_of_natDegree_le ((natDegree_mul_le).trans (by omega))
  have hsum : ∀ Q : ℝ[X], Q.natDegree ≤ 1 → Q.eval (x j) = 0 →
      ∫ t, (Q * P).eval t ∂μ = 0 := fun Q hQ hQj => by
    rw [← hexact _ (hdeg Q hQ)]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hij : i = j
    · rw [hij, eval_mul, hQj, zero_mul, mul_zero]
    · rw [eval_mul, hPzero i hij, mul_zero, mul_zero]
  have hP : ∫ t, P.eval t ∂μ = w j * P.eval (x j) := by
    rw [← hexact P (degree_le_of_natDegree_le (by omega))]
    refine Finset.sum_eq_single j (fun i _ hij => by rw [hPzero i hij, mul_zero]) (by simp)
  constructor
  · by_contra hlt
    push Not at hlt
    have h0 := hsum (X - C (x j)) (by rw [natDegree_X_sub_C]) (by simp)
    have hle : ∫ t, (a - x j) * P.eval t ∂μ ≤ ∫ t, ((X - C (x j)) * P).eval t ∂μ := by
      refine integral_mono_ae ((hint P).const_mul _) (hint _) ?_
      filter_upwards [hae] with t ht
      simp only [eval_mul, eval_sub, eval_X, eval_C]
      exact mul_le_mul_of_nonneg_right (by linarith [ht.1]) (hPnonneg t ht)
    rw [h0, integral_const_mul, hP] at hle
    nlinarith
  · by_contra hlt
    push Not at hlt
    have h0 := hsum (C (x j) - X) (by rw [← neg_sub, natDegree_neg, natDegree_X_sub_C]) (by simp)
    have hle : ∫ t, (x j - b) * P.eval t ∂μ ≤ ∫ t, ((C (x j) - X) * P).eval t ∂μ := by
      refine integral_mono_ae ((hint P).const_mul _) (hint _) ?_
      filter_upwards [hae] with t ht
      simp only [eval_mul, eval_sub, eval_X, eval_C]
      exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) (hPnonneg t ht)
    rw [h0, integral_const_mul, hP] at hle
    nlinarith

end ExactnessMeasure

/-! ### The discrete inner product -/

section DiscreteInner

open OrthogonalPolynomial Polynomial MeasureTheory

variable {μ : Measure ℝ} {n : ℕ}

/-- The **discrete inner product** of a rule with weights $w_i$ and nodes $x_i$:
$$(f, g)_n = \sum_i w_i\, f(x_i)\, g(x_i),$$
which is the value of the rule at the product $fg$. It is a symmetric bilinear form, positive
semidefinite for nonnegative weights. For positive weights and distinct nodes, it is an inner
product on the polynomials of degree less than the number of nodes
(`Quadrature.discreteInner_self_pos`). See (10.28) and (10.51) of [quarteroni2000numerical]. -/
def discreteInner (w x : Fin n → ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∑ i, w i * f (x i) * g (x i)

/-- The discrete inner product is symmetric: $(f, g)_n = (g, f)_n$. -/
theorem discreteInner_comm (w x : Fin n → ℝ) (f g : ℝ → ℝ) :
    discreteInner w x f g = discreteInner w x g f :=
  Finset.sum_congr rfl fun i _ => by ring

/-- The discrete inner product is additive in its first argument:
$(f_1 + f_2, g)_n = (f_1, g)_n + (f_2, g)_n$. -/
theorem discreteInner_add_left (w x : Fin n → ℝ) (f₁ f₂ g : ℝ → ℝ) :
    discreteInner w x (f₁ + f₂) g = discreteInner w x f₁ g + discreteInner w x f₂ g := by
  simp only [discreteInner, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The discrete inner product is homogeneous in its first argument: $(cf, g)_n = c\,(f, g)_n$ for
$c \in \mathbb{R}$. -/
theorem discreteInner_smul_left (w x : Fin n → ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    discreteInner w x (c • f) g = c * discreteInner w x f g := by
  simp only [discreteInner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The discrete inner product commutes with finite sums in its first argument: $\bigl(\sum_{k \in
s} f_k, g\bigr)_n = \sum_{k \in s} (f_k, g)_n$. -/
theorem discreteInner_sum_left (w x : Fin n → ℝ) {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (g : ℝ → ℝ) : discreteInner w x (∑ k ∈ s, f k) g = ∑ k ∈ s, discreteInner w x (f k) g := by
  simp only [discreteInner, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The discrete inner product depends only on the values at the nodes: if $f(x_i) = f'(x_i)$ and
$g(x_i) = g'(x_i)$ for every $i$, then $(f, g)_n = (f', g')_n$. -/
theorem discreteInner_congr (w x : Fin n → ℝ) {f f' g g' : ℝ → ℝ} (hf : ∀ i, f (x i) = f' (x i))
    (hg : ∀ i, g (x i) = g' (x i)) : discreteInner w x f g = discreteInner w x f' g' :=
  Finset.sum_congr rfl fun i _ => by rw [hf i, hg i]

/-- For nonnegative weights, $(f, f)_n \ge 0$ for every function $f$. -/
theorem discreteInner_self_nonneg {w x : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) :
    0 ≤ discreteInner w x f f :=
  Finset.sum_nonneg fun i _ => by rw [mul_assoc, ← sq]; exact mul_nonneg (hw i) (sq_nonneg _)

/-- Let the weights $w_i$ be positive and the nodes $x_0, \dots, x_{n-1}$ be distinct. Then
$(p, p)_n > 0$ for every nonzero real polynomial $p$ of degree less than $n$, because such a
polynomial cannot vanish at all $n$ nodes. So the discrete inner product is an inner product on
$\mathbb{P}_{n-1}$. This is Exercise 10.4 of [quarteroni2000numerical]. -/
theorem discreteInner_self_pos {w x : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hx : Function.Injective x)
    {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.degree < n) :
    0 < discreteInner w x (fun t => p.eval t) fun t => p.eval t := by
  classical
  have hne : ∃ i, p.eval (x i) ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hp (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hx.injOn
      (by simpa using hdeg) fun i _ => hall i)
  obtain ⟨i, hi⟩ := hne
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [mul_assoc, ← sq]; exact mul_nonneg (hw j).le (sq_nonneg _)
  · rw [mul_assoc, ← sq]; exact mul_pos (hw i) (by positivity)

/-- Let a rule be exact to degree $d$ for $\mu$, and let $p$ and $q$ be real polynomials with
$\deg p + \deg q \le d$. Then the discrete inner product of $p$ and $q$ is their $L^2(\mu)$
inner product: $(p, q)_n = \int pq\,d\mu$. -/
theorem discreteInner_eq_integral_of_degree_le {w x : Fin n → ℝ} {d : ℕ}
    (h : IsExactOnMeasure μ w x d) {p q : ℝ[X]} (hpq : p.degree + q.degree ≤ d) :
    discreteInner w x (fun t => p.eval t) (fun t => q.eval t) = ∫ t, p.eval t * q.eval t ∂μ := by
  rw [← degree_mul] at hpq
  have h1 := h _ hpq
  simp only [eval_mul] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Discrete orthogonality.** Let $\mu$ be a weight on $\mathbb{R}$, let $n \ge 1$, and let a rule
with $n + 1$ nodes be exact to degree $2n - 1$ for $\mu$. Then the monic orthogonal polynomials
$p_0, \dots, p_n$ of $\mu$ are orthogonal for the discrete inner product: $(p_j, p_k)_n = 0$ for
$j \ne k$ with $j, k \le n$, because $p_j p_k$ then has degree at most $2n - 1$. See
[quarteroni2000numerical], §10.1 and §10.3.

The rule need not integrate $p_n^2$ exactly. The value $(p_n, p_n)_n$ is where the Gauss and the
Gauss–Lobatto rules differ. -/
theorem discreteInner_family_family (hw : IsWeight μ) (hn : 1 ≤ n) {w x : Fin (n + 1) → ℝ}
    (hexact : IsExactOnMeasure μ w x (2 * n - 1)) {j k : ℕ} (hjk : j ≠ k) (hj : j ≤ n)
    (hk : k ≤ n) :
    discreteInner w x (fun t => (family μ j).eval t) (fun t => (family μ k).eval t) = 0 := by
  rw [discreteInner_eq_integral_of_degree_le hexact, integral_family_mul_family hw hjk]
  rw [degree_family, degree_family]
  norm_cast
  omega

/-- Let $n \ge 1$, and let a rule with $n + 1$ nodes be exact to degree $2n - 1$ for $\mu$. For
$k < n$, the discrete norm of the monic orthogonal polynomial $p_k$ is its $L^2(\mu)$ norm,
$(p_k, p_k)_n = \int p_k^2\,d\mu$, because the rule integrates $p_k^2$ exactly. -/
theorem discreteInner_family_self (hn : 1 ≤ n) {w x : Fin (n + 1) → ℝ}
    (hexact : IsExactOnMeasure μ w x (2 * n - 1)) {k : ℕ} (hk : k < n) :
    discreteInner w x (fun t => (family μ k).eval t) (fun t => (family μ k).eval t) =
      normSq μ k := by
  rw [discreteInner_eq_integral_of_degree_le hexact, normSq]
  · exact integral_congr_ae (Filter.Eventually.of_forall fun t => (sq _).symm)
  · rw [degree_family]
    norm_cast
    omega

/-- **The interpolant at the nodes of a rule is the discrete truncation of the orthogonal
expansion.** Let $\mu$ be a weight on $\mathbb{R}$, let $n \ge 1$, and let a rule with $n + 1$
distinct nodes $x_i$ and positive weights $w_i$ be exact to degree $2n - 1$ for $\mu$. Let $p_k$
be the monic orthogonal polynomials of $\mu$. Then for every function
$f \colon \mathbb{R} \to \mathbb{R}$, the Lagrange interpolant of $f$ at the nodes is
$$\Pi_n f = \sum_{k=0}^{n} \tilde f_k\, p_k, \qquad \tilde f_k = \frac{(f, p_k)_n}{(p_k,
  p_k)_n}.$$
The discrete Chebyshev and Legendre transforms are instances. See (10.4)–(10.5), (10.29),
(10.38) and §10.7 of [quarteroni2000numerical].

The proof expands the interpolant in the basis $p_0, \dots, p_n$ of $\mathbb{P}_n$ and pairs it
with $p_j$ in the discrete inner product. The basis is orthogonal by
`Quadrature.discreteInner_family_family`, and the interpolant agrees with $f$ at the nodes. -/
theorem interpolate_eq_sum_discreteInner_smul (hw : IsWeight μ) (hn : 1 ≤ n)
    {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {w : Fin (n + 1) → ℝ} (hwpos : ∀ i, 0 < w i)
    (hexact : IsExactOnMeasure μ w x (2 * n - 1)) (f : ℝ → ℝ) :
    Lagrange.interpolate Finset.univ x (fun i => f (x i)) =
      ∑ k : Fin (n + 1),
        C (discreteInner w x f (fun t => (family μ k).eval t) /
            discreteInner w x (fun t => (family μ k).eval t) (fun t => (family μ k).eval t)) *
          family μ k := by
  classical
  set P : ℝ[X] := Lagrange.interpolate Finset.univ x (fun i => f (x i)) with hP
  have hPdeg : P.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (n + 1))))
      (r := fun i => f (x i)) hx.injOn
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hPnode : ∀ i, P.eval (x i) = f (x i) := fun i =>
    Lagrange.eval_interpolate_at_node _ hx.injOn (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := exists_eq_sum_family μ hPdeg
  have hcoeff : ∀ j : Fin (n + 1), c j =
      discreteInner w x f (fun t => (family μ j).eval t) /
        discreteInner w x (fun t => (family μ j).eval t) (fun t => (family μ j).eval t) := by
    intro j
    have hpos : 0 < discreteInner w x (fun t => (family μ j).eval t)
        (fun t => (family μ j).eval t) :=
      discreteInner_self_pos hwpos hx (family_ne_zero μ j)
        (by rw [degree_family]; exact_mod_cast j.2)
    rw [eq_div_iff hpos.ne']
    have h1 : discreteInner w x (fun t => P.eval t) (fun t => (family μ j).eval t) =
        discreteInner w x f (fun t => (family μ j).eval t) :=
      discreteInner_congr w x (fun i => hPnode i) fun _ => rfl
    rw [← h1, hc]
    have hev : (fun t => (∑ k ∈ Finset.range (n + 1), c k • family μ k).eval t) =
        ∑ k ∈ Finset.range (n + 1), c k • fun t => (family μ k).eval t := by
      funext t
      simp [eval_finsetSum]
    rw [hev, discreteInner_sum_left, Finset.sum_eq_single (j : ℕ)]
    · rw [discreteInner_smul_left]
    · intro k hk hkj
      rw [discreteInner_smul_left,
        discreteInner_family_family hw hn hexact hkj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
          (Nat.lt_succ_iff.mp j.2), mul_zero]
    · intro hj
      exact absurd (Finset.mem_range.mpr j.2) hj
  rw [hc, ← Fin.sum_univ_eq_sum_range (fun k => c k • family μ k) (n + 1)]
  exact Finset.sum_congr rfl fun j _ => by rw [hcoeff j, smul_eq_C_mul]

end DiscreteInner

/-! ### The Gauss remainder -/

section GaussError

open OrthogonalPolynomial Polynomial MeasureTheory

variable {μ : Measure ℝ}

/-- A continuous function is integrable for a finite measure carried by a compact interval $[a, b]$.
-/
private theorem integrable_of_continuous_of_compl_eq_zero [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hf).isBounded.exists_norm_le
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  have hae : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  filter_upwards [hae] with t ht
  exact hC _ ⟨t, ht, rfl⟩

/-- Finitely many points of a convex set $s \subseteq \mathbb{R}$, at least one, together with a
point $t \in s$, lie in a compact interval contained in $s$. -/
private theorem exists_Icc_subset_of_convex {s : Set ℝ} (hs : Convex ℝ s) {n : ℕ} [NeZero n]
    {x : Fin n → ℝ} (hxmem : ∀ i, x i ∈ s) {t : ℝ} (ht : t ∈ s) :
    ∃ a b : ℝ, Set.Icc a b ⊆ s ∧ t ∈ Set.Icc a b ∧ ∀ i, x i ∈ Set.Icc a b := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  refine ⟨min t (x i₀), max t (x i₁), hs.ordConnected.out ?_ ?_,
    ⟨min_le_left _ _, le_max_left _ _⟩, fun i => ⟨le_trans (min_le_right _ _) ?_,
      le_trans ?_ (le_max_right _ _)⟩⟩
  · rcases min_cases t (x i₀) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    exacts [ht, hxmem i₀]
  · rcases max_cases t (x i₁) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    exacts [ht, hxmem i₁]
  · rw [← hi₀]; exact Finset.inf'_le _ (Finset.mem_univ i)
  · rw [← hi₁]; exact Finset.le_sup' _ (Finset.mem_univ i)

/-- **The remainder of a rule through Hermite interpolation.** Let $s \subseteq \mathbb{R}$ be
convex, and let $\mu$ be a measure on $\mathbb{R}$ with $\mu(\mathbb{R} \setminus s) = 0$ for
which every polynomial is integrable. Let $x_0, \dots, x_{n-1} \in s$ be distinct nodes with
multiplicities $m_i$, where $\sum_i (m_i + 1) = N + 1$, and suppose that the nodal polynomial
$$\omega = \prod_i (X - x_i)^{m_i + 1}$$
is nonnegative on $s$ or nonpositive on $s$. Let a rule with weights $w_i$ at these nodes be
exact to degree $N$ for $\mu$. Then for every $\mu$-integrable function $f$ of class $C^{N+1}$
on $\mathbb{R}$ there is $\xi \in s$ with
$$\int f\,d\mu - \sum_i w_i\, f(x_i) = \frac{f^{(N+1)}(\xi)}{(N+1)!} \int \omega\,d\mu.$$
The Gauss rule is the case where every $m_i = 1$ (`Quadrature.exists_gauss_error_eq_of_convex`).
The Gauss–Radau rule has $m_i = 0$ at the fixed endpoint and $m_i = 1$ elsewhere. The
Gauss–Lobatto rule has $m_i = 0$ at both endpoints and $m_i = 1$ elsewhere. See §10.2.2 of
[golub2013matrix] and (10.41)–(10.42) of [quarteroni2000numerical].

The rule uses only the values of $f$ at the nodes. The Hermite interpolant $H$ of $f$ has the
same values there and degree at most $N$, so the error is $\int (f - H)\,d\mu$. On a compact
interval in $s$ that contains $t$ and the nodes, `Hermite.exists_sub_interpolate_eq` gives
$f(t) - H(t) = f^{(N+1)}(\xi_t)\, \omega(t)/(N+1)!$, and the mean value theorem with a moving
point `MeasureTheory.exists_integral_eq_mul_integral` ends the proof. The measure need not be a
weight: if $\int \omega\,d\mu = 0$, then $\mu$ is carried by the nodes, where $f = H$, and the
error is $0$. The nodal polynomial is `Hermite.nodal x m`. -/
theorem exists_error_eq_of_hermite_of_convex {s : Set ℝ} (hs : Convex ℝ s) (hsupp : μ sᶜ = 0)
    (hpoly : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) {N n : ℕ} {w x : Fin n → ℝ}
    (hx : Function.Injective x) (hxmem : ∀ i, x i ∈ s) {m : Fin n → ℕ}
    (hsum : ∑ i, (m i + 1) = N + 1)
    (hsign : (∀ t ∈ s, 0 ≤ (Hermite.nodal x m).eval t) ∨
      ∀ t ∈ s, (Hermite.nodal x m).eval t ≤ 0)
    (hexact : IsExactOnMeasure μ w x N) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f) (hfint : Integrable f μ) :
    ∃ ξ ∈ s, (∫ t, f t ∂μ) - ∑ i, w i * f (x i) =
      iteratedDeriv (N + 1) f ξ / (N + 1).factorial * ∫ t, (Hermite.nodal x m).eval t ∂μ := by
  classical
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hsum
  have : NeZero n := ⟨hn⟩
  set H : ℝ[X] := Hermite.interpolate x m f with hH
  have hHdeg : H.degree ≤ N := by
    have hd := Hermite.degree_interpolate_lt hx m f
    rw [hsum] at hd
    exact degree_lt_succ_iff.mp hd
  have hsumH : ∑ i, w i * f (x i) = ∫ t, H.eval t ∂μ := by
    rw [← hexact H hHdeg]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := Hermite.eval_iterate_derivative_interpolate (f := f) hx i (Nat.zero_le (m i))
    simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero] at hi
    rw [hi]
  have hpt : ∀ t ∈ s, ∃ ξ ∈ s, f t - H.eval t =
      iteratedDeriv (N + 1) f ξ / (N + 1).factorial * (Hermite.nodal x m).eval t := by
    intro t ht
    obtain ⟨a, b, hab, hta, hxab⟩ := exists_Icc_subset_of_convex hs hxmem ht
    obtain ⟨ξ, hξ, hξeq⟩ := Hermite.exists_sub_interpolate_eq hf hx hxab hsum hta
    exact ⟨ξ, hab hξ, by rw [hξeq, Hermite.eval_nodal]⟩
  rw [hsumH, ← integral_sub hfint (hpoly H)]
  exact exists_integral_eq_mul_integral hs ⟨x 0, hxmem 0⟩ hsupp (hfint.sub (hpoly H))
    (hpoly _) ((hf.continuous_iteratedDeriv _ le_rfl).div_const _).continuousOn hsign hpt

/-- **The remainder of a rule through Hermite interpolation, for a finite measure on a compact
interval.** Let $\mu$ be a finite measure on $\mathbb{R}$ with
$\mu(\mathbb{R} \setminus [a, b]) = 0$. Let $x_0, \dots, x_{n-1} \in [a, b]$ be distinct nodes
with multiplicities $m_i$, where $\sum_i (m_i + 1) = N + 1$, and suppose that the nodal
polynomial $\omega = \prod_i (X - x_i)^{m_i + 1}$ is nonnegative on $[a, b]$ or nonpositive on
$[a, b]$. Let a rule with weights $w_i$ at these nodes be exact to degree $N$ for $\mu$. Then
for every function $f$ of class $C^{N+1}$ on $\mathbb{R}$ there is $\xi \in [a, b]$ with
$$\int f\,d\mu - \sum_i w_i\, f(x_i) = \frac{f^{(N+1)}(\xi)}{(N+1)!} \int \omega\,d\mu.$$
Unlike the Gauss remainder, this result does not need $\mu$ to be a weight: a finitely supported
measure, such as the spectral measure of a symmetric matrix, is allowed. See §10.2.2 and §10.2.6
of [golub2013matrix].

This is the case $s = [a, b]$ of `Quadrature.exists_error_eq_of_hermite_of_convex`, where the
integrability of $f$ and of the polynomials is automatic. -/
theorem exists_error_eq_of_hermite [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {N n : ℕ} {w x : Fin n → ℝ} (hx : Function.Injective x)
    (hxmem : ∀ i, x i ∈ Set.Icc a b) {m : Fin n → ℕ} (hsum : ∑ i, (m i + 1) = N + 1)
    (hsign : (∀ t ∈ Set.Icc a b, 0 ≤ (Hermite.nodal x m).eval t) ∨
      ∀ t ∈ Set.Icc a b, (Hermite.nodal x m).eval t ≤ 0)
    (hexact : IsExactOnMeasure μ w x N) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f) :
    ∃ ξ ∈ Set.Icc a b, (∫ t, f t ∂μ) - ∑ i, w i * f (x i) =
      iteratedDeriv (N + 1) f ξ / (N + 1).factorial * ∫ t, (Hermite.nodal x m).eval t ∂μ :=
  exists_error_eq_of_hermite_of_convex (convex_Icc a b) hsupp
    (fun p => integrable_of_continuous_of_compl_eq_zero hsupp p.continuous) hx hxmem hsum hsign
    hexact hf (integrable_of_continuous_of_compl_eq_zero hsupp hf.continuous)

/-- The nodal polynomial with every multiplicity $1$, that is, with double nodes, takes at $t$ the
value $\prod_i (t - x_i)^2$, the square of the value of the nodal polynomial with simple nodes. -/
private theorem eval_nodal_one {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    (Hermite.nodal x fun _ => 1).eval t = (Lagrange.nodal Finset.univ x).eval t ^ 2 := by
  rw [Hermite.eval_nodal, Lagrange.eval_nodal, ← Finset.prod_pow]

/-- **The Gauss remainder.** Let $\mu$ be a weight on $\mathbb{R}$ with
$\mu(\mathbb{R} \setminus s) = 0$ for a convex set $s \subseteq \mathbb{R}$. Let
$x_0, \dots, x_{n-1} \in s$ be distinct, and let a rule with weights $w_i$ at these nodes
satisfy $\sum_i w_i\, p(x_i) = \int p\,d\mu$ for every real polynomial $p$ of degree less than
$2n$, as the Gauss rule of `Quadrature.exists_gauss` does. Then for every $\mu$-integrable
function $f$ of class $C^{2n}$ on $\mathbb{R}$ there is $\xi \in s$ with
$$\int f\,d\mu - \sum_i w_i\, f(x_i) = \frac{f^{(2n)}(\xi)}{(2n)!} \int p_n^2\,d\mu,$$
where $p_n$ is the monic orthogonal polynomial of degree $n$ of $\mu$, which is the nodal
polynomial of the rule. See (10.41)–(10.42) of [quarteroni2000numerical] and §9.3 of
[kress1998numerical].

Neither $s$ nor $f^{(2n)}$ needs to be bounded, as the Laguerre weight on $(0, \infty)$ and the
Hermite weight on $\mathbb{R}$ require. For $n \ge 1$ the proof is
`Quadrature.exists_error_eq_of_hermite_of_convex` with every multiplicity $1$: the nodal
polynomial with double nodes is $p_n^2$, because by Jacobi's theorem the nodes of the rule are
the roots of $p_n$. For $n = 0$ it is the first mean value theorem for integrals. The number
$\int p_n^2\,d\mu$ is `OrthogonalPolynomial.normSq μ n`. `Quadrature.exists_gauss_error_eq` is
the case of a compact interval, where $f$ is integrable without a further hypothesis. -/
theorem exists_gauss_error_eq_of_convex (hw : IsWeight μ) {s : Set ℝ} (hs : Convex ℝ s)
    (hsupp : μ sᶜ = 0) {n : ℕ} {x w : Fin n → ℝ} (hx : Function.Injective x)
    (hxmem : ∀ i, x i ∈ s)
    (hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) f) (hfint : Integrable f μ) :
    ∃ ξ ∈ s, (∫ t, f t ∂μ) - ∑ i, w i * f (x i) =
      iteratedDeriv (2 * n) f ξ / (2 * n).factorial * normSq μ n := by
  classical
  cases n with
  | zero =>
    -- the empty rule: the first mean value theorem for integrals
    have hne : s.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro rfl
      exact hw.measure_compl_ne_zero Set.finite_empty hsupp
    obtain ⟨ξ, hξ, heq⟩ := exists_integral_eq_mul_integral (D := f) hs hne hsupp hfint
      (hw.integrable_eval_sq (family μ 0)) hf.continuous.continuousOn
      (Or.inl fun t _ => sq_nonneg _) fun t ht => ⟨t, ht, by simp⟩
    exact ⟨ξ, hξ, by simpa [normSq] using heq⟩
  | succ k =>
    have hexact' : IsExactOnMeasure μ w x (2 * k + 1) := isExactOnMeasure_iff_forall_degree_lt.mpr
      (by rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]; exact hexact)
    have hnodal : Lagrange.nodal Finset.univ x = family μ (k + 1) :=
      ((isExactOnMeasure_two_mul_add_one_iff hw hx w).mp hexact').1
    have hf' : ContDiff ℝ ((2 * k + 1 + 1 : ℕ) : WithTop ℕ∞) f := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]; exact hf
    obtain ⟨ξ, hξ, heq⟩ := exists_error_eq_of_hermite_of_convex hs hsupp hw.integrable_eval hx
      hxmem (m := fun _ => 1) (by simp; ring)
      (Or.inl fun t _ => by rw [eval_nodal_one]; exact sq_nonneg _) hexact' hf' hfint
    refine ⟨ξ, hξ, ?_⟩
    rw [heq, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    congr 1
    simp only [eval_nodal_one, hnodal, normSq]

/-- **The Gauss remainder on a compact interval.** Let $\mu$ be a weight on $\mathbb{R}$ with
$\mu(\mathbb{R} \setminus [a, b]) = 0$. Let $x_0, \dots, x_{n-1} \in [a, b]$ be distinct, and
let a rule with weights $w_i$ at these nodes satisfy $\sum_i w_i\, p(x_i) = \int p\,d\mu$ for
every real polynomial $p$ of degree less than $2n$, as the Gauss rule of
`Quadrature.exists_gauss` does. Then for every function $f$ of class $C^{2n}$ on $\mathbb{R}$
there is $\xi \in [a, b]$ with
$$\int f\,d\mu - \sum_i w_i\, f(x_i) = \frac{f^{(2n)}(\xi)}{(2n)!} \int p_n^2\,d\mu,$$
where $p_n$ is the monic orthogonal polynomial of degree $n$ of $\mu$, the nodal polynomial of
the rule. At $n = 0$ this is the mean value theorem for integrals. See (10.41)–(10.42) of
[quarteroni2000numerical] and §9.3 of [kress1998numerical].

This is the case $s = [a, b]$ of `Quadrature.exists_gauss_error_eq_of_convex`. On a compact
interval the integrability of $f$, which that result assumes, holds without a hypothesis. -/
theorem exists_gauss_error_eq (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    {n : ℕ} {x w : Fin n → ℝ} (hx : Function.Injective x) (hxmem : ∀ i, x i ∈ Set.Icc a b)
    (hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) f) :
    ∃ ξ ∈ Set.Icc a b, (∫ t, f t ∂μ) - ∑ i, w i * f (x i) =
      iteratedDeriv (2 * n) f ξ / (2 * n).factorial * normSq μ n := by
  have := hw.isFiniteMeasure
  exact exists_gauss_error_eq_of_convex hw (convex_Icc a b) hsupp hx hxmem hexact hf
    (integrable_of_continuous_of_compl_eq_zero hsupp hf.continuous)

/-- A function of class $C^k$ on an open set $U \supseteq [a, b]$ agrees near every point of
$[a, b]$ with a function of class $C^k$ on $\mathbb{R}$, obtained by multiplying it by a smooth
bump function that equals $1$ near $[a, b]$ and has support in $U$. -/
private theorem exists_contDiff_eventuallyEq {U : Set ℝ} (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ U) {k : ℕ} {f : ℝ → ℝ} (hf : ContDiffOn ℝ (k : WithTop ℕ∞) f U) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (k : WithTop ℕ∞) g ∧ ∀ t ∈ Set.Icc a b, g =ᶠ[𝓝 t] f := by
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.mp hU a (hsub ⟨le_rfl, hab⟩)
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.mp hU b (hsub ⟨hab, le_rfl⟩)
  set ε : ℝ := min ε₁ ε₂ / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hε₁' : ε < ε₁ := by linarith [min_le_left ε₁ ε₂]
  have hε₂' : ε < ε₂ := by linarith [min_le_right ε₁ ε₂]
  have hbig : Set.Icc (a - ε) (b + ε) ⊆ U := by
    rintro y ⟨hy₁, hy₂⟩
    by_cases hya : y < a
    · exact h₁ (by rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith)
    by_cases hyb : b < y
    · exact h₂ (by rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith)
    exact hsub ⟨not_lt.mp hya, not_lt.mp hyb⟩
  let φ : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 2 + ε / 3, (b - a) / 2 + 2 * ε / 3, by linarith, by linarith⟩
  have hrOut : φ.rOut = (b - a) / 2 + 2 * ε / 3 := rfl
  refine ⟨fun y => φ y * f y, ?_, fun t ht => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun y => ?_
    by_cases hy : y ∈ U
    · exact φ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hy))
    · have hyφ : y ∉ tsupport φ := by
        rw [φ.tsupport_eq]
        intro hy'
        rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hy'
        rw [hrOut] at hy'
        exact hy (hbig ⟨by linarith [hy'.1], by linarith [hy'.2]⟩)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyφ] with z hz
      rw [hz, Pi.zero_apply, zero_mul]
  · have hball : Metric.ball ((a + b) / 2) ((b - a) / 2 + ε / 3) ∈ 𝓝 t :=
      Metric.isOpen_ball.mem_nhds (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
    filter_upwards [hball] with z hz
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_mul]

/-- The Hermite remainder of `Quadrature.exists_error_eq_of_hermite` for a function $f$ that is of
class $C^{N+1}$ only on an open set $U \supseteq [a, b]$: under the other hypotheses of that
result, there is $\xi \in [a, b]$ with $\int f\,d\mu - \sum_i w_i\, f(x_i) =
\frac{f^{(N+1)}(\xi)}{(N+1)!} \int \omega\,d\mu$. Both sides use $f$ only on $[a, b]$, where $f$
agrees, with all its derivatives, with a function of class $C^{N+1}$ on $\mathbb{R}$. -/
theorem exists_error_eq_of_hermite_of_contDiffOn [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {N n : ℕ} {w x : Fin n → ℝ} (hx : Function.Injective x)
    (hxmem : ∀ i, x i ∈ Set.Icc a b) {m : Fin n → ℕ} (hsum : ∑ i, (m i + 1) = N + 1)
    (hsign : (∀ t ∈ Set.Icc a b, 0 ≤ (Hermite.nodal x m).eval t) ∨
      ∀ t ∈ Set.Icc a b, (Hermite.nodal x m).eval t ≤ 0)
    (hexact : IsExactOnMeasure μ w x N) {U : Set ℝ} (hU : IsOpen U) (hUsub : Set.Icc a b ⊆ U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Set.Icc a b, (∫ t, f t ∂μ) - ∑ i, w i * f (x i) =
      iteratedDeriv (N + 1) f ξ / (N + 1).factorial * ∫ t, (Hermite.nodal x m).eval t ∂μ := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hsum
    · exact h
  have hab : a ≤ b := (hxmem ⟨0, hn⟩).1.trans (hxmem ⟨0, hn⟩).2
  have hae : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]; exact hsupp
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hab hUsub hf
  have hval : ∀ t ∈ Set.Icc a b, f t = g t := fun t ht => (hgf t ht).eq_of_nhds.symm
  obtain ⟨ξ, hξ, heq⟩ := exists_error_eq_of_hermite hsupp hx hxmem hsum hsign hexact hg
  refine ⟨ξ, hξ, ?_⟩
  rw [integral_congr_ae (by filter_upwards [hae] with t ht using hval t ht),
    Finset.sum_congr rfl fun i _ => by rw [hval _ (hxmem i)], ← (hgf ξ hξ).iteratedDeriv_eq]
  exact heq

/-- **The Gauss rule is a lower bound.** Let $\mu$ be a finite measure on $\mathbb{R}$ with
$\mu(\mathbb{R} \setminus [a, b]) = 0$, let $k \ge 1$, and let a rule with $k$ distinct nodes
$x_i \in [a, b]$ and weights $w_i$ be exact to degree $2k - 1$ for $\mu$. If $f$ is of class
$C^{2k}$ on an open set that contains $[a, b]$, and $f^{(2k)} \ge 0$ on $[a, b]$, then
$\sum_i w_i\, f(x_i) \le \int f\,d\mu$. See §10.2.2 of [golub2013matrix].

With every multiplicity $1$, the nodal polynomial $\omega = \prod_i (X - x_i)^2$ is nonnegative,
so the error $f^{(2k)}(\xi) \int \omega\,d\mu / (2k)!$ of
`Quadrature.exists_error_eq_of_hermite_of_contDiffOn` is nonnegative. -/
theorem gauss_le_integral [IsFiniteMeasure μ] {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ}
    (hk : 1 ≤ k) {w x : Fin k → ℝ} (hx : Function.Injective x) (hxmem : ∀ i, x i ∈ Set.Icc a b)
    (hexact : IsExactOnMeasure μ w x (2 * k - 1)) {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Set.Icc a b ⊆ U) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ((2 * k : ℕ) : WithTop ℕ∞) f U)
    (heven : ∀ t ∈ Set.Icc a b, 0 ≤ iteratedDeriv (2 * k) f t) :
    ∑ i, w i * f (x i) ≤ ∫ t, f t ∂μ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hexact
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring] at hf heven
  obtain ⟨ξ, hξ, heq⟩ := exists_error_eq_of_hermite_of_contDiffOn hsupp hx hxmem
    (m := fun _ => 1) (by simp; ring) (Or.inl fun t _ => by rw [eval_nodal_one]; exact sq_nonneg _)
    hexact hU hUsub hf
  have hω : 0 ≤ ∫ t, (Hermite.nodal x fun _ => 1).eval t ∂μ :=
    integral_nonneg fun t => by rw [eval_nodal_one]; exact sq_nonneg _
  have hD : 0 ≤ iteratedDeriv (2 * j + 1 + 1) f ξ / (2 * j + 1 + 1).factorial :=
    div_nonneg (heven ξ hξ) (Nat.cast_nonneg _)
  nlinarith [mul_nonneg hD hω]

/-- The Gauss–Radau multiplicities, $0$ at the node of index $0$ and $1$ at the other $k$ nodes,
satisfy $\sum_i (m_i + 1) = 2k + 1$. -/
private theorem sum_radau_multiplicity (k : ℕ) :
    ∑ i : Fin (k + 1), ((if i = 0 then 0 else 1 : ℕ) + 1) = 2 * k + 1 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.succ_ne_zero, ite_true, ite_false, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

/-- With the Gauss–Radau multiplicities, the nodal polynomial takes at $t$ the value
$(t - x'_0) \prod_{i \ge 1} (t - x'_i)^2$. -/
private theorem eval_nodal_radau {k : ℕ} (x' : Fin (k + 1) → ℝ) (t : ℝ) :
    (Hermite.nodal x' fun i => if i = 0 then 0 else 1).eval t =
      (t - x' 0) * ∏ i : Fin k, (t - x' i.succ) ^ 2 := by
  rw [Hermite.eval_nodal, Fin.prod_univ_succ]
  simp only [Fin.succ_ne_zero, ite_true, ite_false, zero_add, pow_one]

/-- **The Gauss–Radau rule with the fixed node at the left end is an upper bound.** Let $\mu$ be a
finite measure on $\mathbb{R}$ with $\mu(\mathbb{R} \setminus [a, b]) = 0$, and let a rule with
$k + 1$ distinct nodes $x'_i \in [a, b]$, where $x'_0 = a$, and weights $w'_i$ be exact to
degree $2k$ for $\mu$. If $f$ is of class $C^{2k+1}$ on an open set that contains $[a, b]$, and
$f^{(2k+1)} \le 0$ on $[a, b]$, then $\int f\,d\mu \le \sum_i w'_i\, f(x'_i)$. See §10.2.6 of
[golub2013matrix].

With multiplicity $0$ at $a$ and $1$ at the other nodes, the nodal polynomial
$\omega = (X - a) \prod_{i \ge 1} (X - x'_i)^2$ is nonnegative on $[a, b]$, so the error
$f^{(2k+1)}(\xi) \int \omega\,d\mu / (2k+1)!$ is nonpositive. -/
theorem integral_le_gaussRadau [IsFiniteMeasure μ] {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    {k : ℕ} {w' x' : Fin (k + 1) → ℝ} (hx' : Function.Injective x')
    (hx'mem : ∀ i, x' i ∈ Set.Icc a b) (hx'0 : x' 0 = a)
    (hexact' : IsExactOnMeasure μ w' x' (2 * k)) {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Set.Icc a b ⊆ U) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) f U)
    (hodd : ∀ t ∈ Set.Icc a b, iteratedDeriv (2 * k + 1) f t ≤ 0) :
    ∫ t, f t ∂μ ≤ ∑ i, w' i * f (x' i) := by
  have hω : ∀ t ∈ Set.Icc a b,
      0 ≤ (Hermite.nodal x' fun i => if i = 0 then 0 else 1).eval t := fun t ht => by
    rw [eval_nodal_radau, hx'0]
    exact mul_nonneg (by linarith [ht.1]) (Finset.prod_nonneg fun i _ => sq_nonneg _)
  obtain ⟨ξ, hξ, heq⟩ := exists_error_eq_of_hermite_of_contDiffOn hsupp hx' hx'mem
    (sum_radau_multiplicity k) (Or.inl hω) hexact' hU hUsub hf
  have hae : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]; exact hsupp
  have hωint : 0 ≤ ∫ t, (Hermite.nodal x' fun i => if i = 0 then 0 else 1).eval t ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hae] with t ht using hω t ht)
  have hD : iteratedDeriv (2 * k + 1) f ξ / (2 * k + 1).factorial ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (hodd ξ hξ) (Nat.cast_nonneg _)
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hD hωint]

/-- **The Gauss–Radau rule with the fixed node at the right end is an upper bound.** Let $\mu$ be a
finite measure on $\mathbb{R}$ with $\mu(\mathbb{R} \setminus [a, b]) = 0$, and let a rule with
$k + 1$ distinct nodes $x'_i \in [a, b]$, where $x'_0 = b$, and weights $w'_i$ be exact to
degree $2k$ for $\mu$. If $f$ is of class $C^{2k+1}$ on an open set that contains $[a, b]$, and
$f^{(2k+1)} \ge 0$ on $[a, b]$, then $\int f\,d\mu \le \sum_i w'_i\, f(x'_i)$. This is the rule
of (10.2.9) in §10.2.6 of [golub2013matrix].

The nodal polynomial $(X - b) \prod_{i \ge 1} (X - x'_i)^2$ is now nonpositive on $[a, b]$, and
so is the error. -/
theorem integral_le_gaussRadau_right [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ} {w' x' : Fin (k + 1) → ℝ}
    (hx' : Function.Injective x') (hx'mem : ∀ i, x' i ∈ Set.Icc a b) (hx'0 : x' 0 = b)
    (hexact' : IsExactOnMeasure μ w' x' (2 * k)) {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Set.Icc a b ⊆ U) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) f U)
    (hodd : ∀ t ∈ Set.Icc a b, 0 ≤ iteratedDeriv (2 * k + 1) f t) :
    ∫ t, f t ∂μ ≤ ∑ i, w' i * f (x' i) := by
  have hω : ∀ t ∈ Set.Icc a b,
      (Hermite.nodal x' fun i => if i = 0 then 0 else 1).eval t ≤ 0 := fun t ht => by
    rw [eval_nodal_radau, hx'0]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.2])
      (Finset.prod_nonneg fun i _ => sq_nonneg _)
  obtain ⟨ξ, hξ, heq⟩ := exists_error_eq_of_hermite_of_contDiffOn hsupp hx' hx'mem
    (sum_radau_multiplicity k) (Or.inr hω) hexact' hU hUsub hf
  have hae : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]; exact hsupp
  have hωint : ∫ t, (Hermite.nodal x' fun i => if i = 0 then 0 else 1).eval t ∂μ ≤ 0 :=
    integral_nonpos_of_ae (by filter_upwards [hae] with t ht using hω t ht)
  have hD : 0 ≤ iteratedDeriv (2 * k + 1) f ξ / (2 * k + 1).factorial :=
    div_nonneg (hodd ξ hξ) (Nat.cast_nonneg _)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hD hωint]

/-- **The two-sided Gauss and Gauss–Radau bound.** Let $\mu$ be a finite measure on $\mathbb{R}$
with $\mu(\mathbb{R} \setminus [a, b]) = 0$, and let $k \ge 1$. Let a rule with $k$ distinct
nodes $x_i \in [a, b]$ and weights $w_i$ be exact to degree $2k - 1$ for $\mu$ (a Gauss rule).
Let a rule with $k + 1$ distinct nodes $x'_i \in [a, b]$, where $x'_0 = a$, and weights $w'_i$
be exact to degree $2k$ for $\mu$ (a Gauss–Radau rule with the fixed node at the left end). Let
$f$ be of class $C^{2k+1}$ on an open set that contains $[a, b]$, with $f^{(2k)} \ge 0$ and
$f^{(2k+1)} \le 0$ on $[a, b]$. Then
$$\sum_i w_i\, f(x_i) \le \int f\,d\mu \le \sum_i w'_i\, f(x'_i).$$
See §10.2.2 and §10.2.6 of [golub2013matrix].

The two bounds are `Quadrature.gauss_le_integral` and `Quadrature.integral_le_gaussRadau`.
`Quadrature.gauss_le_integral_le_gaussRadau_right` is the version with the fixed node at the
right end. The rules can be the Gauss and Gauss–Radau rules of a weight
(`Quadrature.exists_gauss`, `Quadrature.exists_gaussRadau`), or the Lanczos rules of the
spectral measure of a symmetric matrix, with $f(\lambda) = 1/\lambda^2$ and $0 < a$. -/
theorem gauss_le_integral_le_gaussRadau [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ} (hk : 1 ≤ k) {w x : Fin k → ℝ}
    (hx : Function.Injective x) (hxmem : ∀ i, x i ∈ Set.Icc a b)
    (hexact : IsExactOnMeasure μ w x (2 * k - 1)) {w' x' : Fin (k + 1) → ℝ}
    (hx' : Function.Injective x') (hx'mem : ∀ i, x' i ∈ Set.Icc a b) (hx'0 : x' 0 = a)
    (hexact' : IsExactOnMeasure μ w' x' (2 * k)) {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Set.Icc a b ⊆ U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) f U)
    (heven : ∀ t ∈ Set.Icc a b, 0 ≤ iteratedDeriv (2 * k) f t)
    (hodd : ∀ t ∈ Set.Icc a b, iteratedDeriv (2 * k + 1) f t ≤ 0) :
    ∑ i, w i * f (x i) ≤ ∫ t, f t ∂μ ∧ ∫ t, f t ∂μ ≤ ∑ i, w' i * f (x' i) :=
  ⟨gauss_le_integral hsupp hk hx hxmem hexact hU hUsub
      (hf.of_le (by exact_mod_cast Nat.le_succ _)) heven,
    integral_le_gaussRadau hsupp hx' hx'mem hx'0 hexact' hU hUsub hf hodd⟩

/-- **The two-sided Gauss and Gauss–Radau bound, with the fixed node at the right end.** Let $\mu$
be a finite measure on $\mathbb{R}$ with $\mu(\mathbb{R} \setminus [a, b]) = 0$, and let
$k \ge 1$. Let a rule with $k$ distinct nodes $x_i \in [a, b]$ and weights $w_i$ be exact to
degree $2k - 1$ for $\mu$. Let a rule with $k + 1$ distinct nodes $x'_i \in [a, b]$, where
$x'_0 = b$, and weights $w'_i$ be exact to degree $2k$ for $\mu$. Let $f$ be of class $C^{2k+1}$
on an open set that contains $[a, b]$, with $f^{(2k)} \ge 0$ and $f^{(2k+1)} \ge 0$ on $[a, b]$.
Then
$$\sum_i w_i\, f(x_i) \le \int f\,d\mu \le \sum_i w'_i\, f(x'_i).$$
See §10.2.6 of [golub2013matrix].

The rules can be those of `Quadrature.exists_gauss` and `Quadrature.exists_gaussRadau_right`. -/
theorem gauss_le_integral_le_gaussRadau_right [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ} (hk : 1 ≤ k) {w x : Fin k → ℝ}
    (hx : Function.Injective x) (hxmem : ∀ i, x i ∈ Set.Icc a b)
    (hexact : IsExactOnMeasure μ w x (2 * k - 1)) {w' x' : Fin (k + 1) → ℝ}
    (hx' : Function.Injective x') (hx'mem : ∀ i, x' i ∈ Set.Icc a b) (hx'0 : x' 0 = b)
    (hexact' : IsExactOnMeasure μ w' x' (2 * k)) {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Set.Icc a b ⊆ U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) f U)
    (heven : ∀ t ∈ Set.Icc a b, 0 ≤ iteratedDeriv (2 * k) f t)
    (hodd : ∀ t ∈ Set.Icc a b, 0 ≤ iteratedDeriv (2 * k + 1) f t) :
    ∑ i, w i * f (x i) ≤ ∫ t, f t ∂μ ∧ ∫ t, f t ∂μ ≤ ∑ i, w' i * f (x' i) :=
  ⟨gauss_le_integral hsupp hk hx hxmem hexact hU hUsub
      (hf.of_le (by exact_mod_cast Nat.le_succ _)) heven,
    integral_le_gaussRadau_right hsupp hx' hx'mem hx'0 hexact' hU hUsub hf hodd⟩

end GaussError


/-! ### Peano's kernel theorem -/

section Peano

open MeasureTheory

variable {F : ℕ → ℝ → ℝ}

/-- For a chain of derivatives $F_0, \dots, F_{m+1}$, the function
$s \mapsto \sum_{k \le m} F_k(s)\,(v - s)^k/k!$ has the derivative $(v - t)^m F_{m+1}(t)/m!$ at
$t$, because the other terms cancel in pairs. -/
private theorem hasDerivAt_taylorSum {v x : ℝ} :
    ∀ m : ℕ, (∀ k ≤ m, HasDerivAt (F k) (F (k + 1) x) x) →
      HasDerivAt (fun t => ∑ k ∈ Finset.range (m + 1), F k t * (v - t) ^ k / (k.factorial : ℝ))
        ((v - x) ^ m / (m.factorial : ℝ) * F (m + 1) x) x := by
  have hvt : HasDerivAt (fun t : ℝ => v - t) (-1) x := (hasDerivAt_id x).const_sub v
  intro m
  induction m with
  | zero =>
    intro hF
    simpa using hF 0 le_rfl
  | succ m ih =>
    intro hF
    have h1 := ih fun k hk => hF k (by omega)
    have h2 : HasDerivAt (fun t => F (m + 1) t * (v - t) ^ (m + 1) / ((m + 1).factorial : ℝ))
        ((F (m + 1 + 1) x * (v - x) ^ (m + 1)
            + F (m + 1) x * ((m + 1 : ℕ) * (v - x) ^ m * (-1))) / ((m + 1).factorial : ℝ)) x :=
      ((hF (m + 1) le_rfl).mul (hvt.pow (m + 1))).div_const _
    have h3 : HasDerivAt
        (fun t => (∑ k ∈ Finset.range (m + 1), F k t * (v - t) ^ k / (k.factorial : ℝ))
          + F (m + 1) t * (v - t) ^ (m + 1) / ((m + 1).factorial : ℝ))
        ((v - x) ^ m / (m.factorial : ℝ) * F (m + 1) x
          + (F (m + 1 + 1) x * (v - x) ^ (m + 1)
              + F (m + 1) x * ((m + 1 : ℕ) * (v - x) ^ m * (-1))) /
            ((m + 1).factorial : ℝ)) x := h1.add h2
    have hsplit : (fun t => ∑ k ∈ Finset.range (m + 1 + 1), F k t * (v - t) ^ k / (k.factorial : ℝ))
        = fun t => (∑ k ∈ Finset.range (m + 1), F k t * (v - t) ^ k / (k.factorial : ℝ))
          + F (m + 1) t * (v - t) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
      funext t
      rw [Finset.sum_range_succ]
    rw [hsplit]
    convert h3 using 1
    have hfac : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    rw [hfac]
    push_cast
    field_simp
    ring

/-- For a chain of derivatives $F_0, \dots, F_{m+1}$, the function $s \mapsto \sum_{k \le m}
F_k(s)\,(b - s)^{k+1}/(k+1)!$ has the derivative $(b - t)^{m+1} F_{m+1}(t)/(m+1)! - F_0(t)$ at
$t$. -/
private theorem hasDerivAt_integratedTaylorSum {b x : ℝ} :
    ∀ m : ℕ, (∀ k ≤ m, HasDerivAt (F k) (F (k + 1) x) x) →
      HasDerivAt
        (fun t => ∑ k ∈ Finset.range (m + 1),
          F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
        ((b - x) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) x - F 0 x) x := by
  have hvt : HasDerivAt (fun t : ℝ => b - t) (-1) x := (hasDerivAt_id x).const_sub b
  intro m
  induction m with
  | zero =>
    intro hF
    have hsplit : (fun t => ∑ k ∈ Finset.range (0 + 1),
          F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
        = fun t => F 0 t * (b - t) ^ (0 + 1) / ((0 + 1).factorial : ℝ) := by
      funext t
      rw [Finset.sum_range_one]
    have h : HasDerivAt (fun t => F 0 t * (b - t) ^ (0 + 1) / ((0 + 1).factorial : ℝ))
        ((F (0 + 1) x * (b - x) ^ (0 + 1)
            + F 0 x * ((0 + 1 : ℕ) * (b - x) ^ 0 * (-1))) / ((0 + 1).factorial : ℝ)) x :=
      ((hF 0 le_rfl).mul (hvt.pow (0 + 1))).div_const _
    rw [hsplit]
    convert h using 1
    have hfac : ((0 + 1).factorial : ℝ) = 1 := by norm_num
    rw [hfac]
    push_cast
    ring
  | succ m ih =>
    intro hF
    have h1 := ih fun k hk => hF k (by omega)
    have h2 : HasDerivAt
        (fun t => F (m + 1) t * (b - t) ^ (m + 1 + 1) / ((m + 1 + 1).factorial : ℝ))
        ((F (m + 1 + 1) x * (b - x) ^ (m + 1 + 1)
            + F (m + 1) x * ((m + 1 + 1 : ℕ) * (b - x) ^ (m + 1) * (-1))) /
          ((m + 1 + 1).factorial : ℝ)) x :=
      ((hF (m + 1) le_rfl).mul (hvt.pow (m + 1 + 1))).div_const _
    have h3 : HasDerivAt
        (fun t => (∑ k ∈ Finset.range (m + 1),
            F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
          + F (m + 1) t * (b - t) ^ (m + 1 + 1) / ((m + 1 + 1).factorial : ℝ))
        (((b - x) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) x - F 0 x)
          + (F (m + 1 + 1) x * (b - x) ^ (m + 1 + 1)
              + F (m + 1) x * ((m + 1 + 1 : ℕ) * (b - x) ^ (m + 1) * (-1))) /
            ((m + 1 + 1).factorial : ℝ)) x := h1.add h2
    have hsplit : (fun t => ∑ k ∈ Finset.range (m + 1 + 1),
          F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
        = fun t => (∑ k ∈ Finset.range (m + 1),
            F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
          + F (m + 1) t * (b - t) ^ (m + 1 + 1) / ((m + 1 + 1).factorial : ℝ) := by
      funext t
      rw [Finset.sum_range_succ]
    rw [hsplit]
    convert h3 using 1
    have hfac : ((m + 1 + 1).factorial : ℝ) = ((m : ℝ) + 1 + 1) * ((m + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hne : ((m + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (m + 1))
    rw [hfac]
    push_cast
    field_simp
    ring

/-- **Taylor's formula with the integral remainder.** Let $F_0, F_1, \dots, F_{m+1}$ be functions on
$\mathbb{R}$ such that, for $k \le m$, $F_k$ has the derivative $F_{k+1}$ at every point of the
closed interval between $u$ and $v$, and let $F_{m+1}$ be integrable on that interval. Then
$$F_0(v) = \sum_{k=0}^{m} \frac{F_k(u)\,(v - u)^k}{k!} + \int_u^v \frac{(v - t)^m}{m!}\,
  F_{m+1}(t)\,dt.$$

This is Mathlib's `taylor_integral_remainder` in the form with a family of derivatives that the
quadrature results use. It is proved from a telescoping identity, not by $m + 1$ integrations by
parts. -/
theorem eq_taylorSum_add_integral {u v : ℝ} {m : ℕ}
    (hF : ∀ k ≤ m, ∀ t ∈ Set.uIcc u v, HasDerivAt (F k) (F (k + 1) t) t)
    (hint : IntervalIntegrable (F (m + 1)) volume u v) :
    F 0 v = (∑ k ∈ Finset.range (m + 1), F k u * (v - u) ^ k / (k.factorial : ℝ))
      + ∫ t in u..v, (v - t) ^ m / (m.factorial : ℝ) * F (m + 1) t := by
  have hΦ : ∀ t ∈ Set.uIcc u v,
      HasDerivAt (fun s => ∑ k ∈ Finset.range (m + 1), F k s * (v - s) ^ k / (k.factorial : ℝ))
        ((v - t) ^ m / (m.factorial : ℝ) * F (m + 1) t) t :=
    fun t ht => hasDerivAt_taylorSum m fun k hk => hF k hk t ht
  have hi : IntervalIntegrable
      (fun t => (v - t) ^ m / (m.factorial : ℝ) * F (m + 1) t) volume u v :=
    hint.continuousOn_mul (by fun_prop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ hi
  have hv : (∑ k ∈ Finset.range (m + 1), F k v * (v - v) ^ k / (k.factorial : ℝ)) = F 0 v := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      rw [sub_self, zero_pow hk]
      ring
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.succ_pos m)) h
  rw [hv] at hftc
  linarith

/-- **The integrated Taylor formula.** Let $F_0, F_1, \dots, F_{m+1}$ be functions on $\mathbb{R}$
such that, for $k \le m$, $F_k$ has the derivative $F_{k+1}$ at every point of the closed
interval between $a$ and $b$, and let $F_{m+1}$ be integrable on that interval. Then
$$\int_a^b F_0(t)\,dt = \sum_{k=0}^{m} \frac{F_k(a)\,(b - a)^{k+1}}{(k+1)!} + \int_a^b
  \frac{(b - t)^{m+1}}{(m+1)!}\, F_{m+1}(t)\,dt.$$
The sum is the integral over $[a, b]$ of the Taylor polynomial of $F_0$ at $a$.

This identity replaces the Fubini step in the usual proof of Peano's theorem: the double
integral $\int_a^b \int_a^x (x - t)^m F_{m+1}(t)\,dt\,dx$ is never formed. -/
theorem integral_eq_taylorSum_add_integral {a b : ℝ} {m : ℕ}
    (hF : ∀ k ≤ m, ∀ t ∈ Set.uIcc a b, HasDerivAt (F k) (F (k + 1) t) t)
    (hint : IntervalIntegrable (F (m + 1)) volume a b) :
    (∫ t in a..b, F 0 t)
      = (∑ k ∈ Finset.range (m + 1), F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ))
        + ∫ t in a..b, (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t := by
  have hΨ : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => ∑ k ∈ Finset.range (m + 1),
          F k s * (b - s) ^ (k + 1) / ((k + 1).factorial : ℝ))
        ((b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t - F 0 t) t :=
    fun t ht => hasDerivAt_integratedTaylorSum m fun k hk => hF k hk t ht
  have hc0 : ContinuousOn (F 0) (Set.uIcc a b) := fun t ht =>
    (hF 0 (Nat.zero_le m) t ht).continuousAt.continuousWithinAt
  have hi0 : IntervalIntegrable (F 0) volume a b := hc0.intervalIntegrable
  have hi1 : IntervalIntegrable
      (fun t => (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t) volume a b :=
    hint.continuousOn_mul (by fun_prop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hΨ (hi1.sub hi0)
  rw [intervalIntegral.integral_sub hi1 hi0] at hftc
  have hb : (∑ k ∈ Finset.range (m + 1),
      F k b * (b - b) ^ (k + 1) / ((k + 1).factorial : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [sub_self, zero_pow (Nat.succ_ne_zero k)]
    ring
  rw [hb] at hftc
  linarith

/-- The **truncated power** $(y - t)_+^m$: it is $(y - t)^m$ for $t \le y$ and $0$ for $t > y$. The
function $t \mapsto (y - t)_+^m$ is the part of the monomial that the Peano kernel integrates
against.

At $m = 0$ the value is $1$ for $t \le y$, so $(y - t)_+^0$ is the indicator of $t \le y$. -/
noncomputable def truncPow (m : ℕ) (y t : ℝ) : ℝ := if t ≤ y then (y - t) ^ m else 0

/-- As a function of $t$, the truncated power $(y - t)_+^m$ is the indicator of the half-line
$(-\infty, y]$ times $(y - t)^m$. -/
theorem truncPow_eq_indicator (m : ℕ) (y : ℝ) :
    truncPow m y = (Set.Iic y).indicator fun t => (y - t) ^ m := by
  funext t
  by_cases h : t ≤ y <;> simp [truncPow, h]

/-- As a function of $y$, the truncated power $(y - t)_+^m$ is the indicator of the half-line
$[t, \infty)$ times $(y - t)^m$. -/
theorem truncPow_flip_eq_indicator (m : ℕ) (t : ℝ) :
    (fun y => truncPow m y t) = (Set.Ici t).indicator fun y => (y - t) ^ m := by
  funext y
  by_cases h : t ≤ y <;> simp [truncPow, h]

/-- The truncated power $t \mapsto (y - t)_+^m$ is integrable on every bounded interval. -/
theorem intervalIntegrable_truncPow (m : ℕ) (y u v : ℝ) :
    IntervalIntegrable (truncPow m y) volume u v := by
  have hc : IntervalIntegrable (fun t : ℝ => (y - t) ^ m) volume u v :=
    Continuous.intervalIntegrable (by fun_prop) u v
  rw [intervalIntegrable_iff] at hc ⊢
  rw [truncPow_eq_indicator]
  exact hc.indicator measurableSet_Iic

/-- The truncated power $y \mapsto (y - t)_+^m$ is integrable on every bounded interval. -/
theorem intervalIntegrable_truncPow_flip (m : ℕ) (t u v : ℝ) :
    IntervalIntegrable (fun y => truncPow m y t) volume u v := by
  have hc : IntervalIntegrable (fun y : ℝ => (y - t) ^ m) volume u v :=
    Continuous.intervalIntegrable (by fun_prop) u v
  rw [intervalIntegrable_iff] at hc ⊢
  rw [truncPow_flip_eq_indicator]
  exact hc.indicator measurableSet_Ici

/-- Let $a \le y \le b$ and let $g$ be continuous on $[a, b]$. Then
$$\int_a^b (y - t)_+^m\, g(t)\,dt = \int_a^y (y - t)^m\, g(t)\,dt.$$
-/
theorem integral_truncPow_mul {a b y : ℝ} {m : ℕ} {g : ℝ → ℝ} (hay : a ≤ y) (hyb : y ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    (∫ t in a..b, truncPow m y t * g t) = ∫ t in a..y, (y - t) ^ m * g t := by
  have hsub1 : Set.uIcc a y ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hay]
    exact Set.Icc_subset_Icc le_rfl hyb
  have hsub2 : Set.uIcc y b ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hyb]
    exact Set.Icc_subset_Icc hay le_rfl
  have h1 : IntervalIntegrable (fun t => truncPow m y t * g t) volume a y :=
    (intervalIntegrable_truncPow m y a y).mul_continuousOn (hg.mono hsub1)
  have h2 : IntervalIntegrable (fun t => truncPow m y t * g t) volume y b :=
    (intervalIntegrable_truncPow m y y b).mul_continuousOn (hg.mono hsub2)
  have e1 : (∫ t in a..y, truncPow m y t * g t) = ∫ t in a..y, (y - t) ^ m * g t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hay] at ht
    simp [truncPow, ht.2]
  have e2 : (∫ t in y..b, truncPow m y t * g t) = 0 := by
    rw [intervalIntegral.integral_of_le hyb,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ : ℝ => (0 : ℝ)) fun t ht => by
          have hty : ¬ t ≤ y := not_le.2 ht.1
          simp [truncPow, hty],
      MeasureTheory.integral_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, e1, e2, add_zero]

/-- For $a \le t \le b$, the integral of the truncated power in its upper variable is
$$\int_a^b (x - t)_+^m\,dx = \frac{(b - t)^{m+1}}{m + 1}.$$
-/
theorem integral_truncPow_flip {a b t : ℝ} {m : ℕ} (hat : a ≤ t) (htb : t ≤ b) :
    (∫ x in a..b, truncPow m x t) = (b - t) ^ (m + 1) / ((m : ℝ) + 1) := by
  have e1 : (∫ x in a..t, truncPow m x t) = 0 := by
    rw [intervalIntegral.integral_of_le hat, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (g := fun _ : ℝ => (0 : ℝ)) fun x hx => by
          have hxt : ¬ t ≤ x := not_le.2 hx.2
          simp [truncPow, hxt],
      MeasureTheory.integral_zero]
  have e2 : (∫ x in t..b, truncPow m x t) = ∫ x in t..b, (x - t) ^ m := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le htb] at hx
    simp [truncPow, hx.1]
  have e3 : (∫ x in t..b, (x - t) ^ m) = (b - t) ^ (m + 1) / ((m : ℝ) + 1) := by
    have h := intervalIntegral.integral_comp_sub_right (a := t) (b := b) (fun x : ℝ => x ^ m) t
    simp only [sub_self] at h
    rw [h, integral_pow]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_truncPow_flip m t a t) (intervalIntegrable_truncPow_flip m t t b),
    e1, e2, e3, zero_add]

/-- The **Peano kernel** of order $m$ of the rule with weights $w_i$ and nodes $z_i$ on $[a, b]$:
$$K(t) = \frac{1}{m!}\Bigl(\int_a^b (x - t)_+^m\,dx - \sum_i w_i\,(z_i - t)_+^m\Bigr),$$
the error functional of the rule applied to $x \mapsto (x - t)_+^m$ and divided by $m!$.

`Quadrature.peanoKernel_eq` gives its closed form on $[a, b]$, and
`Quadrature.error_eq_integral_peanoKernel` is Peano's theorem. -/
noncomputable def peanoKernel {n : ℕ} (a b : ℝ) (w z : Fin n → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ((∫ x in a..b, truncPow m x t) - ∑ i, w i * truncPow m (z i) t) / (m.factorial : ℝ)

/-- For $t \in [a, b]$, the Peano kernel has the closed form
$$K(t) = \frac{(b - t)^{m+1}}{(m+1)!} - \sum_i \frac{w_i\,(z_i - t)_+^m}{m!}.$$
-/
theorem peanoKernel_eq {n : ℕ} {a b : ℝ} (w z : Fin n → ℝ) (m : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    peanoKernel a b w z m t
      = (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ)
        - ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ) := by
  have hfac : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [peanoKernel, integral_truncPow_flip ht.1 ht.2, hfac, sub_div, Finset.sum_div]
  congr 1
  field_simp

/-- For $m \ge 1$, the truncated power $t \mapsto (y - t)_+^m$ is continuous. -/
theorem continuous_truncPow {m : ℕ} (hm : 1 ≤ m) (y : ℝ) : Continuous (truncPow m y) := by
  unfold truncPow
  refine Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
    fun t ht => ?_
  have ht' : t = y := ht
  rw [ht', sub_self, zero_pow (by omega)]

open Set in
/-- For $m \ge 1$, the Peano kernel of order $m$ is continuous on $[a, b]$. -/
theorem continuousOn_peanoKernel {a b : ℝ} {k : ℕ} (w z : Fin k → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ContinuousOn (peanoKernel a b w z m) (Icc a b) := by
  have hclosed : ∀ t ∈ Icc a b, peanoKernel a b w z m t
      = (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ)
        - ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ) := fun t ht => peanoKernel_eq w z m ht
  refine ContinuousOn.congr ?_ hclosed
  refine (by fun_prop : Continuous fun t : ℝ => (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ))
    |>.continuousOn.sub (continuousOn_finsetSum _ fun i _ => ?_)
  exact (((continuous_truncPow hm (z i)).const_mul (w i)).div_const _).continuousOn

/-- **Peano's kernel theorem.** Let $a \le b$, and let a rule with weights $w_i$ and nodes
$z_i \in [a, b]$ satisfy $\int_a^b p(t)\,dt = \sum_i w_i\, p(z_i)$ for every real polynomial $p$
of degree at most $m$. Let $F_0, F_1, \dots, F_{m+1}$ be functions on $\mathbb{R}$ such that,
for $k \le m$, $F_k$ has the derivative $F_{k+1}$ at every point of $[a, b]$, and let $F_{m+1}$
be continuous on $[a, b]$. Then
$$\int_a^b F_0(t)\,dt - \sum_i w_i\, F_0(z_i) = \int_a^b K(t)\, F_{m+1}(t)\,dt,$$
where $K$ is the Peano kernel `Quadrature.peanoKernel a b w z m`. See §9.2 of
[kress1998numerical].

Taylor's formula with the integral remainder, applied once over $[a, b]$
(`Quadrature.integral_eq_taylorSum_add_integral`) and once at each node
(`Quadrature.eq_taylorSum_add_integral`), splits both parts of the error into a Taylor
polynomial, on which the rule is exact, and a remainder integral. The truncated power puts the
node remainders on the same interval as the remainder over $[a, b]$, and the finitely many node
remainders come out of the integral by linearity, so no Fubini step is needed. -/
theorem error_eq_integral_peanoKernel {a b : ℝ} {n m : ℕ} (hab : a ≤ b) {w z : Fin n → ℝ}
    (hz : ∀ i, z i ∈ Set.Icc a b)
    (hF : ∀ k ≤ m, ∀ t ∈ Set.Icc a b, HasDerivAt (F k) (F (k + 1) t) t)
    (hc : ContinuousOn (F (m + 1)) (Set.Icc a b))
    (hexact : ∀ p : ℝ[X], p.degree ≤ (m : WithBot ℕ) →
      (∫ t in a..b, p.eval t) = ∑ i, w i * p.eval (z i)) :
    (∫ t in a..b, F 0 t) - ∑ i, w i * F 0 (z i)
      = ∫ t in a..b, peanoKernel a b w z m t * F (m + 1) t := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hint : IntervalIntegrable (F (m + 1)) volume a b :=
    ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hc)
  -- exactness on the shifted monomials
  have hmono : ∀ k ≤ m, (∫ t in a..b, (t - a) ^ k) = ∑ i, w i * (z i - a) ^ k := by
    intro k hk
    have hdeg : ((Polynomial.X - Polynomial.C a) ^ k).degree ≤ (m : WithBot ℕ) := by
      have h1 : ((Polynomial.X - Polynomial.C a) ^ k).degree = (k : WithBot ℕ) := by
        simp [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
      rw [h1]
      exact_mod_cast hk
    simpa using hexact _ hdeg
  -- the moments of the shifted monomials
  have hpow : ∀ k : ℕ, (∫ t in a..b, (t - a) ^ k) = (b - a) ^ (k + 1) / ((k : ℝ) + 1) := by
    intro k
    have h := intervalIntegral.integral_comp_sub_right (a := a) (b := b) (fun x : ℝ => x ^ k) a
    simp only [sub_self] at h
    rw [h, integral_pow]
    simp
  -- exactness, applied to the Taylor polynomial of `F` at `a`
  have hkey : (∑ k ∈ Finset.range (m + 1), F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ))
      = ∑ i, w i * ∑ k ∈ Finset.range (m + 1), F k a * (z i - a) ^ k / (k.factorial : ℝ) := by
    have step : ∀ k ∈ Finset.range (m + 1),
        F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ)
          = ∑ i, w i * (F k a * (z i - a) ^ k / (k.factorial : ℝ)) := by
      intro k hk
      have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have h1 : (b - a) ^ (k + 1) / ((k : ℝ) + 1) = ∑ i, w i * (z i - a) ^ k := by
        rw [← hpow k, hmono k hk']
      have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hkne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      calc F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ)
          = F k a / (k.factorial : ℝ) * ((b - a) ^ (k + 1) / ((k : ℝ) + 1)) := by
            rw [hfac]
            field_simp
        _ = F k a / (k.factorial : ℝ) * ∑ i, w i * (z i - a) ^ k := by rw [h1]
        _ = ∑ i, w i * (F k a * (z i - a) ^ k / (k.factorial : ℝ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  -- the panel half of the error
  have hleft : (∫ t in a..b, F 0 t)
      = (∑ k ∈ Finset.range (m + 1), F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ))
        + ∫ t in a..b, (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t :=
    integral_eq_taylorSum_add_integral (by rw [huIcc]; exact hF) hint
  -- the rule half of the error, node by node
  have hright : ∀ i, F 0 (z i)
      = (∑ k ∈ Finset.range (m + 1), F k a * (z i - a) ^ k / (k.factorial : ℝ))
        + ∫ t in a..b, truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t := by
    intro i
    have haz : a ≤ z i := (hz i).1
    have hzb : z i ≤ b := (hz i).2
    have hsub : Set.uIcc a (z i) ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le haz]
      exact Set.Icc_subset_Icc le_rfl hzb
    have h := eq_taylorSum_add_integral (F := F) (u := a) (v := z i) (m := m)
      (fun k hk t ht => hF k hk t (hsub ht)) (hint.mono_set (by rw [huIcc]; exact hsub))
    rw [h]
    congr 1
    calc (∫ t in a..(z i), (z i - t) ^ m / (m.factorial : ℝ) * F (m + 1) t)
        = ∫ t in a..(z i), (z i - t) ^ m * (F (m + 1) t / (m.factorial : ℝ)) :=
          intervalIntegral.integral_congr fun t _ => by ring
      _ = ∫ t in a..b, truncPow m (z i) t * (F (m + 1) t / (m.factorial : ℝ)) :=
          (integral_truncPow_mul haz hzb (hc.div_const _)).symm
      _ = ∫ t in a..b, truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t :=
          intervalIntegral.integral_congr fun t _ => by ring
  -- integrability of the pieces
  have hRint : ∀ i, IntervalIntegrable
      (fun t => w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t)) volume a b := by
    intro i
    have h := (intervalIntegrable_truncPow m (z i) a b).mul_continuousOn
      (g := fun t => w i * (F (m + 1) t / (m.factorial : ℝ)))
      (by rw [huIcc]; exact (hc.div_const _).const_smul (w i))
    have hfun : (fun t => truncPow m (z i) t * (w i * (F (m + 1) t / (m.factorial : ℝ))))
        = fun t => w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t) := by
      funext t
      ring
    rwa [hfun] at h
  have hsumint : IntervalIntegrable
      (fun t => ∑ i, w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t)) volume a b := by
    have h := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
      fun i (_ : i ∈ Finset.univ) => hRint i
    have hfun : (∑ i ∈ Finset.univ,
          fun t => w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t))
        = fun t => ∑ i, w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t) := by
      funext t
      rw [Finset.sum_apply]
    rwa [hfun] at h
  have hi1 : IntervalIntegrable
      (fun t => (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t) volume a b :=
    hint.continuousOn_mul (by fun_prop)
  -- the kernel integral, expanded
  have hK : (∫ t in a..b, peanoKernel a b w z m t * F (m + 1) t)
      = (∫ t in a..b, (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t)
        - ∑ i, w i * ∫ t in a..b, truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t := by
    have e0 : (∫ t in a..b, peanoKernel a b w z m t * F (m + 1) t)
        = ∫ t in a..b, ((b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t
            - ∑ i, w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [huIcc] at ht
      rw [peanoKernel_eq w z m ht, sub_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e0, intervalIntegral.integral_sub hi1 hsumint,
      intervalIntegral.integral_finsetSum fun i _ => hRint i]
    congr 1
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  have hsumF : ∑ i, w i * F 0 (z i)
      = (∑ i, w i * ∑ k ∈ Finset.range (m + 1), F k a * (z i - a) ^ k / (k.factorial : ℝ))
        + ∑ i, w i * ∫ t in a..b, truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hright i]; ring
  rw [hK, hleft, hsumF, hkey]
  ring

/-- **The Peano error bound.** Under the hypotheses of `Quadrature.error_eq_integral_peanoKernel`,
if $|F_{m+1}(t)| \le M$ for every $t \in [a, b]$, then
$$\Bigl|\int_a^b F_0(t)\,dt - \sum_i w_i\, F_0(z_i)\Bigr| \le M \int_a^b |K(t)|\,dt,$$
where $K$ is the Peano kernel of order $m$. -/
theorem abs_error_le_integral_abs_peanoKernel {a b : ℝ} {n m : ℕ} (hab : a ≤ b) {w z : Fin n → ℝ}
    {M : ℝ} (hz : ∀ i, z i ∈ Set.Icc a b)
    (hF : ∀ k ≤ m, ∀ t ∈ Set.Icc a b, HasDerivAt (F k) (F (k + 1) t) t)
    (hc : ContinuousOn (F (m + 1)) (Set.Icc a b))
    (hexact : ∀ p : ℝ[X], p.degree ≤ (m : WithBot ℕ) →
      (∫ t in a..b, p.eval t) = ∑ i, w i * p.eval (z i))
    (hM : ∀ t ∈ Set.Icc a b, |F (m + 1) t| ≤ M) :
    |(∫ t in a..b, F 0 t) - ∑ i, w i * F 0 (z i)|
      ≤ (∫ t in a..b, |peanoKernel a b w z m t|) * M := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  -- the kernel is integrable on the panel: on it, it is the closed form
  have hclosed : ∀ t ∈ Set.uIcc a b, peanoKernel a b w z m t
      = (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ)
        - ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ) := by
    intro t ht
    rw [huIcc] at ht
    exact peanoKernel_eq w z m ht
  have hKint : IntervalIntegrable (peanoKernel a b w z m) volume a b := by
    have hbase : IntervalIntegrable (fun t => (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ)
        - ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ)) volume a b := by
      refine (Continuous.intervalIntegrable (by fun_prop) a b).sub ?_
      have h := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
        fun i (_ : i ∈ Finset.univ) =>
          ((intervalIntegrable_truncPow m (z i) a b).const_mul (w i)).div_const
            ((m.factorial : ℝ))
      have hfun : (∑ i ∈ Finset.univ, fun t => w i * truncPow m (z i) t / (m.factorial : ℝ))
          = fun t => ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ) := by
        funext t
        rw [Finset.sum_apply]
      rwa [hfun] at h
    exact hbase.congr fun t ht => (hclosed t (Set.uIoc_subset_uIcc ht)).symm
  have habs : IntervalIntegrable (fun t => |peanoKernel a b w z m t|) volume a b := hKint.abs
  have hprod : IntervalIntegrable
      (fun t => |peanoKernel a b w z m t * F (m + 1) t|) volume a b := by
    have := (hKint.mul_continuousOn (by rw [huIcc]; exact hc)).abs
    exact this
  have hbdd : IntervalIntegrable (fun t => |peanoKernel a b w z m t| * M) volume a b :=
    habs.mul_const M
  rw [error_eq_integral_peanoKernel hab hz hF hc hexact]
  calc |∫ t in a..b, peanoKernel a b w z m t * F (m + 1) t|
      ≤ ∫ t in a..b, |peanoKernel a b w z m t * F (m + 1) t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, |peanoKernel a b w z m t| * M := by
        refine intervalIntegral.integral_mono_on hab hprod hbdd fun t ht => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM t ht) (abs_nonneg _)
    _ = (∫ t in a..b, |peanoKernel a b w z m t|) * M := intervalIntegral.integral_mul_const _ _

end Peano

end Quadrature
