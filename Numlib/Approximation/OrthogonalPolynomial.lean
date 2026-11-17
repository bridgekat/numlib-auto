/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Weierstrass
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Orthogonal polynomials of a measure

Let $\mu$ be a measure on $\mathbb{R}$ with finite moments that is not carried by a finite set. Then
$\langle p, q \rangle = \int p q \, d\mu$ is an inner product on the real polynomials, and the
Gram–Schmidt process on the monomials gives monic polynomials $p_0, p_1, \dots$ with $\deg p_n = n$
that are pairwise orthogonal. This module constructs them and proves their main properties: the
three-term recurrence
$$p_{n+2} = (x - \alpha_{n+1}) p_{n+1} - \beta_n p_n, \qquad \alpha_n = \frac{\langle x p_n, p_n
  \rangle}{\|p_n\|^2}, \quad \beta_n = \frac{\|p_{n+1}\|^2}{\|p_n\|^2},$$
the Christoffel–Darboux identity, the fact that $p_n$ has $n$ distinct real zeros inside every
interval that carries $\mu$, and the identification of $p_n$ with the characteristic polynomial of
the Jacobi matrix of $\alpha$ and $\sqrt\beta$. It also proves that the truncated expansion in the
$p_k$ is the best $L^2(\mu)$ approximation by polynomials of a given degree, and that the
orthonormal polynomials $\hat p_n = p_n / \|p_n\|$ form a Hilbert basis of $L^2(\mu)$ when $\mu$ is
carried by a compact interval. The presentation follows [han2009theoretical], §3.5,
[kress1998numerical], §9.3, and [quarteroni2000numerical], §10.1–10.2 and §10.6.

The Legendre polynomials $P_n$, defined by Rodrigues' formula, are the main example: the module
proves their recurrence, their differential equation, their orthogonality on $[-1, 1]$, and that
$p_n$ for Lebesgue measure on $(-1, 1)$ is the monic rescaling of $P_n$. The orthogonality of the
Chebyshev polynomials is stated for comparison.

## Main definitions

* `OrthogonalPolynomial.IsWeight`: the standing hypothesis on $\mu$. Every moment is finite, and
  $\mu$ gives positive mass to the complement of every finite set.
* `OrthogonalPolynomial.family`: the monic orthogonal polynomials $p_n$ of $\mu$.
* `OrthogonalPolynomial.normSq`, `OrthogonalPolynomial.alpha`, `OrthogonalPolynomial.beta`: the
  squared norms $\|p_n\|^2$ and the recurrence coefficients $\alpha_n$ and $\beta_n$.
* `OrthogonalPolynomial.cdKernel`: the Christoffel–Darboux kernel $K_N(\cdot, t) = \sum_{k \le N}
  p_k(t) p_k / \|p_k\|^2$.
* `OrthogonalPolynomial.orthonormalFamily`: the orthonormal polynomials $\hat p_n = p_n / \|p_n\|$,
  with the coefficients `OrthogonalPolynomial.cdA`, `OrthogonalPolynomial.cdB` and
  `OrthogonalPolynomial.cdC` of their three-term recurrence.
* `OrthogonalPolynomial.jacobiMatrix`: the symmetric tridiagonal matrix with diagonal
  $\alpha_0, \dots, \alpha_{n-1}$ and off-diagonal $\sqrt{\beta_0}, \dots, \sqrt{\beta_{n-2}}$.
* `OrthogonalPolynomial.hilbertBasis`: the orthonormal polynomials as a Hilbert basis of $L^2(\mu)$.
* `Polynomial.legendre`: the Legendre polynomial $P_n = (2^n n!)^{-1} \frac{d^n}{dx^n} (x^2 - 1)^n$.
* `OrthogonalPolynomial.legendreMeasure`: Lebesgue measure on $(-1, 1)$.

## Main results

* `OrthogonalPolynomial.integral_family_mul_family`,
  `OrthogonalPolynomial.integral_family_mul_of_degree_lt`: $p_n$ is orthogonal to $p_m$ for
  $m \neq n$ and to every polynomial of degree less than $n$.
* `OrthogonalPolynomial.three_term_recurrence`: $p_{n+2} = (x - \alpha_{n+1}) p_{n+1} - \beta_n
  p_n$.
* `OrthogonalPolynomial.christoffel_darboux`: $\|p_N\|^2 (x - t) K_N(x, t) = p_{N+1}(x) p_N(t) -
  p_N(x) p_{N+1}(t)$.
* `OrthogonalPolynomial.exists_injective_family_eq_prod`: $p_n$ has $n$ distinct real zeros, the
  nodes of the $n$-point Gauss rule of $\mu$.
* `OrthogonalPolynomial.root_family_mem_Ioo`: if $\mu$ is carried by $[a, b]$, the zeros of $p_n$
  lie in $(a, b)$; `OrthogonalPolynomial.lt_root_family` and `OrthogonalPolynomial.root_family_lt`
  are the one-sided forms.
* `OrthogonalPolynomial.charpoly_jacobiMatrix`: the characteristic polynomial of the $n \times n$
  Jacobi matrix is $p_n$, so the Gauss nodes are its eigenvalues.
* `OrthogonalPolynomial.isBestApprox_truncation`: the truncated expansion $\sum_{k \le N} \langle u,
  p_k \rangle p_k / \|p_k\|^2$ is the best $L^2(\mu)$ approximation of $u$ by polynomials of degree
  at most $N$.
* `OrthogonalPolynomial.IsWeight.denseRange_toLpₗ`: if $\mu$ is carried by a compact interval, the
  polynomials are dense in $L^2(\mu)$.
* `OrthogonalPolynomial.hilbertBasisOfDegreeEq`: an orthonormal family of polynomials with one
  member of each degree is then a Hilbert basis of $L^2(\mu)$.
* `Polynomial.legendre_recurrence`, `Polynomial.legendre_ode`, `Polynomial.legendre_eq_sum`,
  `Polynomial.integral_legendre_mul_legendre`: the recurrence, the differential equation, the
  explicit form and the orthogonality relations of the Legendre polynomials.
* `OrthogonalPolynomial.family_eq_legendre`: $p_n$ for Lebesgue measure on $(-1, 1)$ is the monic
  rescaling of $P_n$.
* `Polynomial.Chebyshev.integral_T_mul_T_div_sqrt`: the orthogonality relations of the Chebyshev
  polynomials.

## Proof outline

The zeros: if $p_n$ changed sign at fewer than $n$ points, the product of $p_n$ with the monic
polynomial that vanishes at those points would have only real roots of even multiplicity, and hence
constant sign. Its integral would then be nonzero, but orthogonality of $p_n$ to the polynomials of
lower degree makes the integral zero. The three-term recurrence follows because $x p_{n+1}$ is
orthogonal to $p_k$ for $k < n$. The Christoffel–Darboux identity follows from the recurrence by
induction on $N$. Laplace expansion of the tridiagonal determinant along its last row gives the same
recurrence for the characteristic polynomials of the Jacobi matrices. Density of the polynomials
follows from the density of the bounded continuous functions in $L^2(\mu)$ and the Weierstrass
approximation theorem.

## Implementation notes

* `OrthogonalPolynomial.family` is defined by the monic Gram–Schmidt recursion for every measure. A
  coefficient whose denominator $\|p_k\|^2$ is zero is $0$, by the convention for division by zero,
  so $p_n$ is always monic of degree $n$. Orthogonality needs `OrthogonalPolynomial.IsWeight`. The
  same convention applies to `OrthogonalPolynomial.alpha` and `OrthogonalPolynomial.beta`.
* A polynomial acts on $\mathbb{R}$ by `Polynomial.eval`. Its class in $L^2(\mu)$ is given by the
  linear map `OrthogonalPolynomial.IsWeight.toLpₗ`.
* "$\mu$ is carried by $[a, b]$" is the hypothesis `μ (Set.Icc a b)ᶜ = 0`.
* The Legendre polynomials are in the namespace `Polynomial`. The Chebyshev polynomials are
  Mathlib's `Polynomial.Chebyshev.T`.
-/

open MeasureTheory Polynomial

open scoped Nat

noncomputable section

namespace Polynomial

/-!
### Real polynomials of constant sign

The argument for the zeros of the orthogonal polynomials needs that a real polynomial whose real
roots all have even multiplicity does not change sign.
-/

/-- Let $p$ be a real polynomial with $p(x) \neq 0$ for every $x \in \mathbb{R}$. Then $p$ has
**constant sign**: either $p(x) > 0$ for all $x$, or $p(x) < 0$ for all $x$.

The proof uses the intermediate value theorem. -/
theorem forall_pos_or_forall_neg_of_forall_eval_ne_zero {p : ℝ[X]} (h : ∀ x : ℝ, p.eval x ≠ 0) :
    (∀ x, 0 < p.eval x) ∨ (∀ x, p.eval x < 0) := by
  by_cases hpos : ∀ x, 0 < p.eval x
  · exact Or.inl hpos
  refine Or.inr fun v => ?_
  push Not at hpos
  obtain ⟨u, hu⟩ := hpos
  have hu' : p.eval u < 0 := lt_of_le_of_ne hu (h u)
  by_contra hv
  push Not at hv
  have hv' : 0 < p.eval v := lt_of_le_of_ne hv (Ne.symm (h v))
  have hmem : (0 : ℝ) ∈ Set.uIcc (p.eval u) (p.eval v) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hu'.le, hv'.le⟩)
  obtain ⟨c, -, hc⟩ :=
    intermediate_value_uIcc (f := fun x => p.eval x) p.continuous.continuousOn hmem
  exact h c hc

/-- Let $p \neq 0$ be a real polynomial such that every $r \in \mathbb{R}$ has even multiplicity as
a root of $p$ (multiplicity $0$ included). Then $p$ **does not change sign**: either
$p(x) \ge 0$ for all $x$, or $p(x) \le 0$ for all $x$.

Splitting off the square of the product of the linear factors leaves a polynomial without real
roots, which has constant sign by `Polynomial.forall_pos_or_forall_neg_of_forall_eval_ne_zero`. -/
theorem forall_nonneg_or_forall_nonpos_of_even_rootMultiplicity {p : ℝ[X]} (hp : p ≠ 0)
    (heven : ∀ r : ℝ, Even (p.rootMultiplicity r)) :
    (∀ x, 0 ≤ p.eval x) ∨ (∀ x, p.eval x ≤ 0) := by
  classical
  set g : ℝ[X] := ∏ r ∈ p.roots.toFinset, (X - C r) ^ (p.rootMultiplicity r / 2) with hg
  clear_value g
  have hgsq : g ^ 2 = ∏ r ∈ p.roots.toFinset, (X - C r) ^ p.rootMultiplicity r := by
    rw [hg, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [← pow_mul]
    obtain ⟨k, hk⟩ := heven r
    congr 1
    omega
  have hdvd : g ^ 2 ∣ p := by
    rw [hgsq, ← Polynomial.prod_multiset_root_eq_finset_root]
    exact p.prod_multiset_X_sub_C_dvd
  obtain ⟨h, hh⟩ := hdvd
  have hne : ∀ x : ℝ, h.eval x ≠ 0 := by
    intro x hx
    have hroot : p.IsRoot x := by
      rw [IsRoot, hh, eval_mul, hx, mul_zero]
    have hmem : x ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hp).2 hroot)
    have hdvd1 : (X - C x) ^ p.rootMultiplicity x ∣ g ^ 2 := by
      rw [hgsq]
      exact Finset.dvd_prod_of_mem _ hmem
    have hdvd2 : (X - C x) ∣ h := dvd_iff_isRoot.mpr hx
    have hdvd3 : (X - C x) ^ (p.rootMultiplicity x + 1) ∣ p := by
      have hgh : (X - C x) ^ (p.rootMultiplicity x + 1) ∣ g ^ 2 * h := by
        rw [pow_succ]
        exact mul_dvd_mul hdvd1 hdvd2
      rwa [← hh] at hgh
    have := (le_rootMultiplicity_iff hp).2 hdvd3
    omega
  have heval : ∀ x : ℝ, p.eval x = g.eval x ^ 2 * h.eval x := by
    intro x
    rw [hh, eval_mul, eval_pow]
  rcases forall_pos_or_forall_neg_of_forall_eval_ne_zero hne with hpos | hneg
  · exact Or.inl fun x => by rw [heval x]; exact mul_nonneg (sq_nonneg _) (hpos x).le
  · refine Or.inr fun x => ?_
    rw [heval x]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hneg x).le

end Polynomial

namespace OrthogonalPolynomial

variable {μ : Measure ℝ}

/-! ### The standing hypothesis -/

/-- A measure $\mu$ on $\mathbb{R}$ is a **weight** if all its moments are finite and it is not
carried by a finite set: $x \mapsto x^n$ is $\mu$-integrable for every $n$, and
$\mu(\mathbb{R} \setminus s) \neq 0$ for every finite set $s$.

The second condition makes $\int p^2 \, d\mu$ positive for every nonzero polynomial $p$, because
a polynomial vanishes only on a finite set. -/
structure IsWeight (μ : Measure ℝ) : Prop where
  /-- Every moment of $\mu$ is finite: $x \mapsto x^n$ is $\mu$-integrable for every $n$. -/
  integrable_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) μ
  /-- $\mu$ gives positive mass to the complement of every finite set $s$:
  $\mu(\mathbb{R} \setminus s) \neq 0$. -/
  measure_compl_ne_zero {s : Set ℝ} (hs : s.Finite) : μ sᶜ ≠ 0

/-- Every polynomial is integrable for a finite measure carried by a bounded interval. -/
theorem integrable_eval_of_measure_compl_Icc_eq_zero [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : μ (Set.Icc a b)ᶜ = 0) (p : ℝ[X]) : Integrable (fun x => p.eval x) μ := by
  have h : IntegrableOn (fun x => p.eval x) (Set.Icc a b) μ :=
    p.continuous.continuousOn.integrableOn_Icc
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (MeasureTheory.ae_iff.2 hμ)] at h

/-- The squared norm of a polynomial is positive when the measure has positive mass off its
roots and the square is integrable. -/
theorem integral_eval_sq_pos_of_measure_compl_ne_zero {p : ℝ[X]} (hp : p ≠ 0)
    (hint : Integrable (fun x => p.eval x ^ 2) μ)
    (hm : μ (↑p.roots.toFinset : Set ℝ)ᶜ ≠ 0) :
    0 < ∫ x, p.eval x ^ 2 ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
  refine pos_iff_ne_zero.2 fun hzero => hm (measure_mono_null (fun x hx => ?_) hzero)
  simp only [Set.mem_compl_iff, Finset.mem_coe, Multiset.mem_toFinset] at hx
  exact pow_ne_zero 2 fun he => hx ((mem_roots hp).2 he)

/-- If a measure is carried by no set of at most $n$ points, integration gives a positive norm
for every nonzero polynomial of degree at most $n$. -/
theorem integral_eval_sq_pos_of_degree_le
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) {n : ℕ}
    (hm : ∀ s : Finset ℝ, s.card ≤ n → μ (↑s : Set ℝ)ᶜ ≠ 0)
    {p : ℝ[X]} (hp : p ≠ 0) (hd : p.degree ≤ n) :
    0 < ∫ x, p.eval x ^ 2 ∂μ := by
  refine integral_eval_sq_pos_of_measure_compl_ne_zero hp ?_ (hm _ ?_)
  · convert hint (p ^ 2) using 1
    funext x
    rw [eval_pow]
  · exact (Multiset.toFinset_card_le p.roots).trans
      ((card_roots' p).trans (natDegree_le_iff_degree_le.2 hd))

namespace IsWeight

/-- A weight is a finite measure, because its moment of order zero is finite. -/
theorem isFiniteMeasure (hw : IsWeight μ) : IsFiniteMeasure μ := by
  have h : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by simpa using hw.integrable_pow 0
  rcases (integrable_const_iff (μ := μ) (c := (1 : ℝ))).1 h with h1 | h1
  · exact absurd h1 one_ne_zero
  · exact h1

/-- For a weight $\mu$, every polynomial is $\mu$-integrable. -/
theorem integrable_eval (hw : IsWeight μ) (p : ℝ[X]) :
    Integrable (fun x => p.eval x) μ := by
  have h : (fun x => p.eval x) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
    funext x; exact p.eval_eq_sum_range x
  rw [h]
  exact integrable_finsetSum _ fun i _ => (hw.integrable_pow i).const_mul _

/-- For a weight $\mu$, the product $pq$ of two polynomials is $\mu$-integrable. -/
theorem integrable_eval_mul (hw : IsWeight μ) (p q : ℝ[X]) :
    Integrable (fun x => p.eval x * q.eval x) μ := by
  simpa using hw.integrable_eval (p * q)

/-- For a weight $\mu$, the square $p^2$ of every polynomial is $\mu$-integrable. -/
theorem integrable_eval_sq (hw : IsWeight μ) (p : ℝ[X]) :
    Integrable (fun x => p.eval x ^ 2) μ := by
  simpa [sq] using hw.integrable_eval_mul p p

/-- For a weight $\mu$ and a nonzero polynomial $p$,
$$\int p^2 \, d\mu > 0.$$
This is where the condition that $\mu$ is not carried by a finite set is used. -/
theorem integral_eval_sq_pos (hw : IsWeight μ) {p : ℝ[X]} (hp : p ≠ 0) :
    0 < ∫ x, p.eval x ^ 2 ∂μ :=
  integral_eval_sq_pos_of_measure_compl_ne_zero hp (hw.integrable_eval_sq p)
    (hw.measure_compl_ne_zero p.roots.toFinset.finite_toSet)

/-- Let $\mu$ be a weight, and let $p \neq 0$ be a polynomial with $p(x) \ge 0$ for all $x$. Then
$\int p \, d\mu > 0$. -/
theorem integral_eval_pos (hw : IsWeight μ) {p : ℝ[X]} (hp : p ≠ 0)
    (hnn : ∀ x, 0 ≤ p.eval x) : 0 < ∫ x, p.eval x ∂μ := by
  refine lt_of_le_of_ne (integral_nonneg hnn) fun h => ?_
  have hae : (fun x => p.eval x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn (hw.integrable_eval p)).1 h.symm
  have hsub : (↑p.roots.toFinset : Set ℝ)ᶜ ⊆ {x | p.eval x ≠ 0} := by
    intro x hx
    simp only [Set.mem_compl_iff, Multiset.mem_toFinset, Finset.mem_coe] at hx
    exact fun h0 => hx ((mem_roots hp).2 (by simpa [IsRoot] using h0))
  refine hw.measure_compl_ne_zero p.roots.toFinset.finite_toSet ?_
  refine measure_mono_null hsub ?_
  simpa [Filter.EventuallyEq, ae_iff] using hae

/-- Let $\mu$ be a weight, and let $p \neq 0$ be a polynomial with $p \ge 0$ $\mu$-almost
everywhere. Then
$$\int p \, d\mu > 0.$$

The polynomial vanishes only on a finite set, and $\mu$ gives positive mass to the complement of
every finite set. This is `OrthogonalPolynomial.IsWeight.integral_eval_pos` with an
almost-everywhere hypothesis. -/
theorem integral_eval_pos_of_ae_nonneg (hw : IsWeight μ) {p : ℝ[X]} (hp : p ≠ 0)
    (hnn : ∀ᵐ x ∂μ, 0 ≤ p.eval x) : 0 < ∫ x, p.eval x ∂μ := by
  refine lt_of_le_of_ne (integral_nonneg_of_ae hnn) fun h => ?_
  have hae : (fun x => p.eval x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn (hw.integrable_eval p)).1 h.symm
  have hsub : (↑p.roots.toFinset : Set ℝ)ᶜ ⊆ {x | p.eval x ≠ 0} := by
    intro x hx
    simp only [Set.mem_compl_iff, Multiset.mem_toFinset, Finset.mem_coe] at hx
    exact fun h0 => hx ((mem_roots hp).2 (by simpa [IsRoot] using h0))
  refine hw.measure_compl_ne_zero p.roots.toFinset.finite_toSet ?_
  refine measure_mono_null hsub ?_
  simpa [Filter.EventuallyEq, ae_iff] using hae

/-- Let $\mu$ be a weight, and let $c \neq 0$ and $d$ be real numbers. Then the image of $\mu$ under
the affine map $t \mapsto ct + d$ is a weight. -/
theorem map_affine (hw : IsWeight μ) {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    IsWeight (μ.map fun t => c * t + d) := by
  have hφ : Measurable fun t : ℝ => c * t + d := by fun_prop
  refine ⟨fun n => ?_, fun {s} hs => ?_⟩
  · rw [integrable_map_measure (by fun_prop) hφ.aemeasurable]
    have := hw.integrable_eval ((C c * X + C d) ^ n)
    simpa [Function.comp_def] using this
  · rw [Measure.map_apply hφ hs.measurableSet.compl, Set.preimage_compl]
    refine hw.measure_compl_ne_zero (hs.preimage ?_)
    intro x _ y _ hxy
    have : c * x = c * y := by linarith
    exact mul_left_cancel₀ hc this

end IsWeight

/-- For $a < b$, Lebesgue measure on the open interval $(a, b)$ is a weight. This is the weight of
$L^2(a, b)$, in which the polynomials are dense by
`OrthogonalPolynomial.IsWeight.denseRange_toLpₗ`. -/
theorem isWeight_volume_restrict_Ioo {a b : ℝ} (hab : a < b) :
    IsWeight (volume.restrict (Set.Ioo a b)) := by
  constructor
  · intro n
    exact ((continuous_pow n).continuousOn.integrableOn_Icc (a := a) (b := b)).mono_set
      Set.Ioo_subset_Icc_self
  · intro s hs hzero
    rw [Measure.restrict_apply hs.measurableSet.compl] at hzero
    rw [show sᶜ ∩ Set.Ioo a b = Set.Ioo a b \ s by ext x; simp [and_comm],
      measure_sdiff_null (hs.measure_zero volume), Real.volume_Ioo] at hzero
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne' hzero

/-! ### The family -/

/-- The **monic orthogonal polynomials** $p_n$ of a measure $\mu$ on $\mathbb{R}$, defined by the
Gram–Schmidt recursion on the monomials for $\langle p, q \rangle = \int p q \, d\mu$:
$$p_n = x^n - \sum_{k < n} \frac{\int x^n p_k \, d\mu}{\int p_k^2 \, d\mu} \, p_k.$$

For every measure, $p_n$ is monic of degree $n$ (`OrthogonalPolynomial.monic_family`,
`OrthogonalPolynomial.degree_family`). If $\mu$ is a weight, $p_m$ and $p_n$ are orthogonal for
$m \neq n$ (`OrthogonalPolynomial.integral_family_mul_family`). A coefficient with denominator
$0$ is $0$, by the convention for division by zero. -/
def family (μ : Measure ℝ) : ℕ → ℝ[X]
  | n => X ^ n - ∑ k ∈ (Finset.range n).attach,
      C ((∫ x, x ^ n * (family μ k.1).eval x ∂μ) / ∫ x, (family μ k.1).eval x ^ 2 ∂μ) *
        family μ k.1
  termination_by n => n
  decreasing_by all_goals exact Finset.mem_range.mp k.2

/-- The defining recursion of `OrthogonalPolynomial.family`: for every measure $\mu$ and every $n$,
$$p_n = x^n - \sum_{k < n} \frac{\int x^n p_k \, d\mu}{\int p_k^2 \, d\mu} \, p_k.$$
-/
theorem family_eq (μ : Measure ℝ) (n : ℕ) :
    family μ n = X ^ n - ∑ k ∈ Finset.range n,
      C ((∫ x, x ^ n * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ) * family μ k := by
  rw [family]
  congr 1
  exact Finset.sum_attach _ fun k =>
    C ((∫ x, x ^ n * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ) * family μ k

/-- The zeroth monic orthogonal polynomial is $p_0 = 1$. -/
@[simp]
theorem family_zero (μ : Measure ℝ) : family μ 0 = 1 := by rw [family_eq]; simp

/-- If $p_0, \dots, p_{n-1}$ have the degrees $0, \dots, n-1$, then every linear combination of them
has degree less than $n$. -/
private theorem degree_sum_C_mul_family_lt (μ : Measure ℝ) (c : ℕ → ℝ) (n : ℕ)
    (h : ∀ k < n, (family μ k).degree = k) :
    (∑ k ∈ Finset.range n, C (c k) * family μ k).degree < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  rw [h k hkn]
  calc (C (c k) : ℝ[X]).degree + (k : WithBot ℕ) ≤ 0 + (k : WithBot ℕ) := by
        gcongr; exact degree_C_le
    _ = (k : WithBot ℕ) := zero_add _
    _ < (n : WithBot ℕ) := by exact_mod_cast hkn

/-- For every measure $\mu$, the polynomial $p_n$ has degree $n$. -/
@[simp]
theorem degree_family (μ : Measure ℝ) (n : ℕ) : (family μ n).degree = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [family_eq, degree_sub_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow]
    exact degree_sum_C_mul_family_lt μ _ n ih

/-- For every measure $\mu$, the polynomial $p_n$ is monic. -/
theorem monic_family (μ : Measure ℝ) (n : ℕ) : (family μ n).Monic := by
  have hlt := degree_sum_C_mul_family_lt μ
    (fun k => (∫ x, x ^ n * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ) n
    (fun k _ => degree_family μ k)
  rw [family_eq, sub_eq_add_neg]
  refine (monic_X_pow n).add_of_left ?_
  rw [degree_neg, degree_X_pow]
  exact hlt

/-- For every measure $\mu$, the polynomial $p_n$ is nonzero. -/
theorem family_ne_zero (μ : Measure ℝ) (n : ℕ) : family μ n ≠ 0 :=
  (monic_family μ n).ne_zero

/-- For $k < n$, every constant multiple of $p_k$ has degree less than $n$. -/
private theorem degree_C_mul_family_lt (μ : Measure ℝ) (a : ℝ) {k n : ℕ} (h : k < n) :
    (C a * family μ k).degree < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  rw [degree_family]
  calc (C a : ℝ[X]).degree + (k : WithBot ℕ) ≤ 0 + (k : WithBot ℕ) := by
        gcongr; exact degree_C_le
    _ = (k : WithBot ℕ) := zero_add _
    _ < (n : WithBot ℕ) := by exact_mod_cast h

/-- For $k + 1 < n$, the polynomial $x p_k$ has degree less than $n$. -/
private theorem degree_X_mul_family_lt (μ : Measure ℝ) {k n : ℕ} (h : k + 1 < n) :
    (X * family μ k).degree < (n : WithBot ℕ) := by
  rw [degree_mul, degree_X, degree_family]
  norm_cast
  omega

/-- The monic orthogonal polynomials of $\mu$ as a `Polynomial.Sequence`, a sequence of polynomials
with $\deg p_n = n$, so that the Mathlib results on the span and the independence of such
sequences apply. -/
def sequence (μ : Measure ℝ) : Polynomial.Sequence ℝ :=
  ⟨family μ, degree_family μ⟩

/-- The $n$-th member of `OrthogonalPolynomial.sequence` is $p_n$. -/
@[simp]
theorem sequence_apply (μ : Measure ℝ) (n : ℕ) : sequence μ n = family μ n := rfl

/-- The squared $L^2(\mu)$ norm of the $n$-th monic orthogonal polynomial:
$$\|p_n\|^2 = \int p_n^2 \, d\mu.$$
-/
def normSq (μ : Measure ℝ) (n : ℕ) : ℝ := ∫ x, (family μ n).eval x ^ 2 ∂μ

/-- For a weight $\mu$, the squared norm $\|p_n\|^2$ is positive. -/
theorem normSq_pos (hw : IsWeight μ) (n : ℕ) : 0 < normSq μ n :=
  hw.integral_eval_sq_pos (family_ne_zero μ n)

/-- For a weight $\mu$, the squared norm $\|p_n\|^2$ is nonzero, so the Fourier coefficients
$\langle u, p_n \rangle / \|p_n\|^2$ are well defined. -/
theorem normSq_ne_zero (hw : IsWeight μ) (n : ℕ) : normSq μ n ≠ 0 :=
  (normSq_pos hw n).ne'

/-- Norms below degree $n$ are nonzero for a measure carried by no set with fewer than $n$
points. -/
theorem normSq_ne_zero_of_card_lt
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) {n : ℕ}
    (hm : ∀ s : Finset ℝ, s.card < n → μ (↑s : Set ℝ)ᶜ ≠ 0) {j : ℕ} (hj : j < n) :
    normSq μ j ≠ 0 :=
  (integral_eval_sq_pos_of_degree_le hint (fun s hs => hm s (hs.trans_lt hj))
    (family_ne_zero μ j) (degree_family μ j).le).ne'

/-! ### Orthogonality -/

private theorem integral_family_mul_family_of_lt
    (hintegrable : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) :
    ∀ n : ℕ, (∀ k < n, normSq μ k ≠ 0) →
      ∀ j < n, ∫ x, (family μ n).eval x * (family μ j).eval x ∂μ = 0 := by
  have hint_mul (p q : ℝ[X]) : Integrable (fun x => p.eval x * q.eval x) μ := by
    simpa only [eval_mul] using hintegrable (p * q)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnorm j hj
    have hint : ∀ k, Integrable
        (fun x => (family μ k).eval x * (family μ j).eval x) μ :=
      fun k => hint_mul _ _
    have hsplit : ∀ x : ℝ, (family μ n).eval x * (family μ j).eval x =
        x ^ n * (family μ j).eval x - ∑ k ∈ Finset.range n,
          ((∫ x, x ^ n * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ) *
            ((family μ k).eval x * (family μ j).eval x) := by
      intro x
      rw [family_eq μ n]
      simp only [eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, sub_mul,
        Finset.sum_mul, mul_assoc]
    simp only [hsplit]
    rw [integral_sub (by simpa using hint_mul (X ^ n) (family μ j))
      (integrable_finsetSum _ fun k _ => (hint k).const_mul _),
      integral_finsetSum _ fun k _ => (hint k).const_mul _]
    simp only [integral_const_mul]
    rw [Finset.sum_eq_single j]
    · have hnz : (∫ x, (family μ j).eval x ^ 2 ∂μ) ≠ 0 := hnorm j hj
      have : (∫ x, (family μ j).eval x * (family μ j).eval x ∂μ) =
          ∫ x, (family μ j).eval x ^ 2 ∂μ := by simp [sq]
      rw [this, div_mul_cancel₀ _ hnz]
      simp
    · intro k hk hkj
      have hkn : k < n := Finset.mem_range.mp hk
      rcases lt_or_gt_of_ne hkj with h | h
      · have := ih j hj (fun i hi => hnorm i (hi.trans hj)) k h
        rw [show (∫ x, (family μ k).eval x * (family μ j).eval x ∂μ) =
          ∫ x, (family μ j).eval x * (family μ k).eval x ∂μ from
          integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), this, mul_zero]
      · rw [ih k hkn (fun i hi => hnorm i (hi.trans hkn)) j h, mul_zero]
    · intro hj'
      exact absurd (Finset.mem_range.mpr hj) hj'

/-- Let $\mu$ be a weight, and let $m \neq n$. Then $p_m$ and $p_n$ are orthogonal in $L^2(\mu)$:
$$\int p_m p_n \, d\mu = 0.$$
This is the orthogonality of the family in [han2009theoretical], §3.5. -/
theorem integral_family_mul_family (hw : IsWeight μ) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x, (family μ m).eval x * (family μ n).eval x ∂μ = 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [show (∫ x, (family μ m).eval x * (family μ n).eval x ∂μ) =
      ∫ x, (family μ n).eval x * (family μ m).eval x ∂μ from
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)]
    exact integral_family_mul_family_of_lt hw.integrable_eval n (fun i _ => normSq_ne_zero hw i) m h
  · exact integral_family_mul_family_of_lt hw.integrable_eval m (fun i _ => normSq_ne_zero hw i) n h

private theorem integral_family_mul_family_of_ne_of_integrable
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) {n : ℕ}
    (hnorm : ∀ j < n, normSq μ j ≠ 0) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (hne : i ≠ j) : ∫ x, (family μ i).eval x * (family μ j).eval x ∂μ = 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
      mul_comm ((family μ i).eval x) ((family μ j).eval x))]
    exact integral_family_mul_family_of_lt hint j (fun k hk => hnorm k (hk.trans_le hj)) i h
  · exact integral_family_mul_family_of_lt hint i (fun k hk => hnorm k (hk.trans_le hi)) j h

/-- For every measure $\mu$, every polynomial $q$ of degree less than $n$ is a linear combination
$q = \sum_{k < n} c_k p_k$ of $p_0, \dots, p_{n-1}$. -/
theorem exists_eq_sum_family (μ : Measure ℝ) {n : ℕ} {q : ℝ[X]} (hq : q.degree < n) :
    ∃ c : ℕ → ℝ, q = ∑ k ∈ Finset.range n, c k • family μ k := by
  have hmem : q ∈ Polynomial.degreeLT ℝ n := Polynomial.mem_degreeLT.mpr hq
  rw [← Polynomial.Sequence.span_degreeLT (sequence μ)
      (fun i _ => by simp [(monic_family μ i).leadingCoeff]),
    show Set.Iio n = (↑(Finset.range n) : Set ℕ) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by simpa using hc.symm⟩

/-- Orthogonality of the $n$th monic orthogonal polynomial uses only integrability of
polynomials and nonzero norms below degree $n$. This includes finite distributions with at
least $n$ support points, even if the $n$th polynomial itself has zero norm. -/
theorem integral_family_mul_of_degree_lt_of_integrable
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) {n : ℕ}
    (hnorm : ∀ j < n, normSq μ j ≠ 0) {q : ℝ[X]} (hq : q.degree < n) :
    ∫ x, (family μ n).eval x * q.eval x ∂μ = 0 := by
  obtain ⟨c, hc⟩ := exists_eq_sum_family μ hq
  have hev (x : ℝ) : (family μ n).eval x * q.eval x =
      ∑ k ∈ Finset.range n, c k * ((family μ n).eval x * (family μ k).eval x) := by
    rw [hc]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  simp only [hev]
  rw [integral_finsetSum _ (fun k _ => by
    simpa only [eval_mul] using (hint (family μ n * family μ k)).const_mul (c k))]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [integral_const_mul,
    integral_family_mul_family_of_lt hint n hnorm k (Finset.mem_range.1 hk), mul_zero]

/-- Let $\mu$ be a weight, and let $(q_n)$ be polynomials with $\deg q_n = n$ and
$\int q_n q_m \, d\mu = 0$ for all $m < n$. Then $q_n$ is orthogonal to every polynomial $p$ of
degree less than $n$:
$$\int q_n p \, d\mu = 0.$$

A polynomial of degree less than $n$ is a linear combination of $q_0, \dots, q_{n-1}$. -/
theorem integral_mul_of_degree_lt_of_orthogonal (hw : IsWeight μ) {q : ℕ → ℝ[X]}
    (hdeg : ∀ n, (q n).degree = n)
    (horth : ∀ m n, m < n → ∫ x, (q n).eval x * (q m).eval x ∂μ = 0) {n : ℕ} {p : ℝ[X]}
    (hp : p.degree < n) : ∫ x, (q n).eval x * p.eval x ∂μ = 0 := by
  have hunit : ∀ i, IsUnit (q i).leadingCoeff := fun i =>
    isUnit_iff_ne_zero.2 (leadingCoeff_ne_zero.2 fun h => by
      have := hdeg i
      rw [h, degree_zero] at this
      exact absurd this (by simp))
  have hmem : p ∈ Polynomial.degreeLT ℝ n := Polynomial.mem_degreeLT.mpr hp
  rw [← Polynomial.Sequence.span_degreeLT (⟨q, hdeg⟩ : Polynomial.Sequence ℝ)
      (fun i _ => hunit i), show Set.Iio n = (↑(Finset.range n) : Set ℕ) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hev : ∀ x : ℝ, (q n).eval x * p.eval x =
      ∑ k ∈ Finset.range n, c k * ((q n).eval x * (q k).eval x) := by
    intro x
    rw [← hc]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  simp only [hev]
  rw [integral_finsetSum _ fun k _ => (hw.integrable_eval_mul _ _).const_mul _]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [integral_const_mul, horth k n (Finset.mem_range.mp hk), mul_zero]

/-- Let $\mu$ be a weight. Then $p_n$ is orthogonal to every polynomial $q$ of degree less than $n$:
$$\int p_n q \, d\mu = 0.$$

This is the form in which orthogonality is used: in the arguments for Gauss quadrature and best
approximation, the second factor is an arbitrary polynomial, not another member of the family. -/
theorem integral_family_mul_of_degree_lt (hw : IsWeight μ) {n : ℕ} {q : ℝ[X]}
    (hq : q.degree < n) : ∫ x, (family μ n).eval x * q.eval x ∂μ = 0 :=
  integral_family_mul_of_degree_lt_of_integrable hw.integrable_eval
    (fun j _ => normSq_ne_zero hw j) hq

/-- For integrable polynomials with nonzero norms below degree $n$, the coefficients of the
expansion of $q$ of degree less than $n$ in $p_0, \dots, p_{n-1}$ are given by
$$q = \sum_{k < n} \frac{\int q p_k \, d\mu}{\|p_k\|^2} \, p_k.$$
-/
theorem eq_sum_family_of_integrable
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) {n : ℕ}
    (hnorm : ∀ j < n, normSq μ j ≠ 0) {q : ℝ[X]} (hq : q.degree < n) :
    q = ∑ k ∈ Finset.range n,
      ((∫ x, q.eval x * (family μ k).eval x ∂μ) / normSq μ k) • family μ k := by
  obtain ⟨c, rfl⟩ := exists_eq_sum_family μ hq
  have hcoeff : ∀ j ∈ Finset.range n,
      (∫ x, (∑ k ∈ Finset.range n, c k • family μ k).eval x * (family μ j).eval x ∂μ) =
        c j * normSq μ j := by
    intro j hj
    have hev : ∀ x : ℝ, (∑ k ∈ Finset.range n, c k • family μ k).eval x * (family μ j).eval x =
        ∑ k ∈ Finset.range n, c k * ((family μ k).eval x * (family μ j).eval x) := by
      intro x
      simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.sum_mul, mul_assoc]
    simp only [hev]
    rw [integral_finsetSum _ fun k _ => by
      simpa only [eval_mul] using (hint (family μ k * family μ j)).const_mul (c k)]
    rw [Finset.sum_eq_single j]
    · rw [integral_const_mul, normSq]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => (sq _).symm)
    · intro k hk hkj
      rw [integral_const_mul, integral_family_mul_family_of_ne_of_integrable hint hnorm
        (Finset.mem_range.1 hk).le (Finset.mem_range.1 hj).le hkj, mul_zero]
    · intro hj'; exact absurd hj hj'
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hcoeff j hj, mul_div_assoc, div_self (hnorm j (Finset.mem_range.1 hj)), mul_one]

/-- For a weight, each polynomial of degree less than $n$ is the sum of its orthogonal
expansion in $p_0, \dots, p_{n-1}$. -/
theorem eq_sum_family (hw : IsWeight μ) {n : ℕ} {q : ℝ[X]} (hq : q.degree < n) :
    q = ∑ k ∈ Finset.range n,
      ((∫ x, q.eval x * (family μ k).eval x ∂μ) / normSq μ k) • family μ k :=
  eq_sum_family_of_integrable hw.integrable_eval (fun j _ => normSq_ne_zero hw j) hq

/-- If polynomial evaluations are integrable and the first $n$ norms are nonzero, a polynomial
of degree less than $n$ orthogonal to the first $n$ members of the monic family vanishes. -/
theorem eq_zero_of_degree_lt_of_integrable
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) {n : ℕ}
    (hnorm : ∀ j < n, normSq μ j ≠ 0) {q : ℝ[X]} (hq : q.degree < n)
    (h : ∀ k < n, ∫ x, q.eval x * (family μ k).eval x ∂μ = 0) : q = 0 := by
  rw [eq_sum_family_of_integrable hint hnorm hq]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [h k (Finset.mem_range.mp hk), zero_div, zero_smul]

/-- Let $\mu$ be a weight, and let $q$ be a polynomial of degree less than $n$ with
$\int q p_k \, d\mu = 0$ for all $k < n$. Then $q = 0$. -/
theorem eq_zero_of_degree_lt (hw : IsWeight μ) {n : ℕ} {q : ℝ[X]} (hq : q.degree < n)
    (h : ∀ k < n, ∫ x, q.eval x * (family μ k).eval x ∂μ = 0) : q = 0 :=
  eq_zero_of_degree_lt_of_integrable hw.integrable_eval (fun j _ => normSq_ne_zero hw j) hq h

/-! ### The zeros of the orthogonal polynomials -/

private theorem measure_support_ne_zero_of_eval {p : ℝ[X]} (hp : p ≠ 0)
    (hm : μ (↑p.roots.toFinset : Set ℝ)ᶜ ≠ 0) {f : ℝ → ℝ}
    (hf : ∀ x, p.eval x ≠ 0 → f x ≠ 0) : μ (Function.support f) ≠ 0 := by
  intro hzero
  apply hm (measure_mono_null (fun x hx => ?_) hzero)
  apply hf
  intro h
  exact hx (Multiset.mem_toFinset.2 ((mem_roots hp).2 h))

/-- The polynomial $p_n$ has at least $n$ distinct roots of odd multiplicity when the
measure cannot be carried by its roots. -/
private theorem le_card_odd_rootMultiplicity
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) (n : ℕ)
    (hm : ∀ s : Finset ℝ, s.card ≤ n → μ (↑s : Set ℝ)ᶜ ≠ 0) :
    n ≤ ((family μ n).roots.toFinset.filter
      fun r => Odd ((family μ n).rootMultiplicity r)).card := by
  classical
  by_contra hlt
  push Not at hlt
  set S : Finset ℝ :=
    (family μ n).roots.toFinset.filter fun r => Odd ((family μ n).rootMultiplicity r) with hS
  set q : ℝ[X] := ∏ r ∈ S, (X - C r) with hq
  have hqmonic : q.Monic := monic_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  have hqnat : q.natDegree = S.card := by
    rw [hq, natDegree_prod _ _ fun r _ => (monic_X_sub_C r).ne_zero]
    simp
  have hqdeg : q.degree < (n : WithBot ℕ) := by
    rw [degree_eq_natDegree hqmonic.ne_zero, hqnat]
    exact_mod_cast hlt
  have hzero : ∫ x, (family μ n).eval x * q.eval x ∂μ = 0 :=
    integral_family_mul_of_degree_lt_of_integrable hint
      (fun _ hj => normSq_ne_zero_of_card_lt hint (fun s hs => hm s hs.le) hj) hqdeg
  have hf0 : family μ n * q ≠ 0 := mul_ne_zero (family_ne_zero μ n) hqmonic.ne_zero
  -- the multiplicities of the auxiliary factor
  have hqroots : q.roots = S.val := by
    rw [hq, Finset.prod_eq_multiset_prod]
    exact roots_multiset_prod_X_sub_C S.val
  have hqmult : ∀ r : ℝ, q.rootMultiplicity r = if r ∈ S then 1 else 0 := by
    intro r
    rw [← count_roots, hqroots]
    by_cases hr : r ∈ S
    · rw [ite_eq_left hr]
      exact Multiset.count_eq_one_of_mem S.nodup (Finset.mem_val.mpr hr)
    · rw [ite_eq_right hr]
      exact Multiset.count_eq_zero_of_notMem fun h => hr (Finset.mem_val.mp h)
  -- every real root of the product has even multiplicity
  have heven : ∀ r : ℝ, Even ((family μ n * q).rootMultiplicity r) := by
    intro r
    rw [rootMultiplicity_mul hf0, hqmult r]
    by_cases hr : r ∈ S
    · rw [ite_eq_left hr]
      exact ((Finset.mem_filter.mp hr).2).add_one
    · rw [ite_eq_right hr, add_zero]
      rcases Nat.even_or_odd ((family μ n).rootMultiplicity r) with hev | hodd
      · exact hev
      · exfalso
        have hpos : 0 < (family μ n).rootMultiplicity r :=
          Nat.pos_of_ne_zero fun h0 => by rw [h0] at hodd; simp at hodd
        have hmem : r ∈ (family μ n).roots.toFinset :=
          Multiset.mem_toFinset.mpr
            ((mem_roots (family_ne_zero μ n)).2
              ((rootMultiplicity_pos (family_ne_zero μ n)).mp hpos))
        exact hr (Finset.mem_filter.mpr ⟨hmem, hodd⟩)
  -- a polynomial of constant sign cannot integrate to zero against a weight
  have hcongr : ∫ x, (family μ n * q).eval x ∂μ = 0 := by
    rw [← hzero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => eval_mul)
  have hfmeasure : μ (Function.support ((family μ n * q).eval)) ≠ 0 := by
    refine measure_support_ne_zero_of_eval (family_ne_zero μ n) (hm _ ?_) (fun x hx => ?_)
    · exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans
        (natDegree_eq_of_degree_eq_some (degree_family μ n)).le)
    · rw [eval_mul, mul_ne_zero_iff]
      refine ⟨hx, fun h => ?_⟩
      have hxS : x ∈ S.val := hqroots ▸ (mem_roots hqmonic.ne_zero).2 h
      exact hx ((mem_roots (family_ne_zero μ n)).1 (Multiset.mem_toFinset.1
        ((Finset.mem_filter.1 hxS).1)))
  rcases Polynomial.forall_nonneg_or_forall_nonpos_of_even_rootMultiplicity hf0 heven with
    hsign | hsign
  · have hpos := (integral_pos_iff_support_of_nonneg hsign (hint (family μ n * q))).2
      (pos_iff_ne_zero.2 hfmeasure)
    exact hpos.ne' hcongr
  · have hg : 0 ≤ fun x => -(family μ n * q).eval x := fun x => neg_nonneg.2 (hsign x)
    have hgpos := (integral_pos_iff_support_of_nonneg hg (hint (family μ n * q)).neg).2
      (pos_iff_ne_zero.2 (by simpa using hfmeasure))
    rw [integral_neg, hcongr, neg_zero] at hgpos
    exact (lt_irrefl _ hgpos).elim

/-- Let $\mu$ be a weight. Then $p_n$ **has $n$ distinct real zeros**: there are pairwise distinct
$x_1, \dots, x_n \in \mathbb{R}$ with
$$p_n = \prod_{i=1}^n (x - x_i).$$
These zeros are the nodes of the $n$-point Gauss quadrature rule of $\mu$. This follows
[kress1998numerical], §9.3, and [han2009theoretical], §3.5.

The nodes are indexed by `Fin n`. -/
theorem exists_injective_family_eq_prod_of_measure_compl_ne_zero
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) (n : ℕ)
    (hm : ∀ s : Finset ℝ, s.card ≤ n → μ (↑s : Set ℝ)ᶜ ≠ 0) :
    ∃ x : Fin n → ℝ, Function.Injective x ∧ family μ n = ∏ i, (X - C (x i)) := by
  classical
  have hp0 : family μ n ≠ 0 := family_ne_zero μ n
  have hnat : (family μ n).natDegree = n := natDegree_eq_of_degree_eq_some (degree_family μ n)
  -- the number of distinct roots is squeezed between `n` and `n`
  have hsub : ((family μ n).roots.toFinset.filter
      fun r => Odd ((family μ n).rootMultiplicity r)) ⊆ (family μ n).roots.toFinset :=
    Finset.filter_subset _ _
  have hcard : (family μ n).roots.toFinset.card = n := by
    have h1 := le_card_odd_rootMultiplicity hint n hm
    have h2 := Finset.card_le_card hsub
    have h3 := Multiset.toFinset_card_le (family μ n).roots
    have h4 := card_roots' (family μ n)
    omega
  -- the product of the linear factors divides, and both sides are monic of degree `n`
  have hGmonic : (∏ r ∈ (family μ n).roots.toFinset, (X - C r)).Monic :=
    monic_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  have hGnat : (∏ r ∈ (family μ n).roots.toFinset, (X - C r)).natDegree = n := by
    rw [natDegree_prod _ _ fun r _ => (monic_X_sub_C r).ne_zero]
    simpa using hcard
  have hmid : (∏ r ∈ (family μ n).roots.toFinset,
      (X - C r) ^ (family μ n).rootMultiplicity r) ∣ family μ n := by
    rw [← Polynomial.prod_multiset_root_eq_finset_root]
    exact (family μ n).prod_multiset_X_sub_C_dvd
  have hGdvd : (∏ r ∈ (family μ n).roots.toFinset, (X - C r)) ∣ family μ n := by
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun r hr => ?_) hmid
    have hpos : 0 < (family μ n).rootMultiplicity r :=
      (rootMultiplicity_pos hp0).mpr ((mem_roots hp0).1 (Multiset.mem_toFinset.mp hr))
    exact dvd_pow_self _ hpos.ne'
  have hGeq : family μ n = ∏ r ∈ (family μ n).roots.toFinset, (X - C r) := by
    have h := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hGmonic hGdvd (by
      rw [hnat, hGnat])
    rwa [Monic.leadingCoeff (monic_family μ n), map_one, one_mul] at h
  -- enumerate the roots
  refine ⟨⇑(((family μ n).roots.toFinset).orderEmbOfFin hcard),
    (((family μ n).roots.toFinset).orderEmbOfFin hcard).strictMono.injective, ?_⟩
  have himg : Finset.image (⇑(((family μ n).roots.toFinset).orderEmbOfFin hcard)) Finset.univ
      = (family μ n).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun r hr => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.orderEmbOfFin_mem _ hcard i
    · rw [Finset.card_image_of_injective _
        (((family μ n).roots.toFinset).orderEmbOfFin hcard).strictMono.injective,
        Finset.card_univ, Fintype.card_fin, hcard]
  calc family μ n = ∏ r ∈ (family μ n).roots.toFinset, (X - C r) := hGeq
    _ = ∏ r ∈ Finset.image (⇑(((family μ n).roots.toFinset).orderEmbOfFin hcard)) Finset.univ,
          (X - C r) := by rw [himg]
    _ = ∏ i, (X - C ((((family μ n).roots.toFinset).orderEmbOfFin hcard) i)) :=
        Finset.prod_image fun i _ j _ h =>
          (((family μ n).roots.toFinset).orderEmbOfFin hcard).strictMono.injective h

/-- A weight's $n$th monic orthogonal polynomial has $n$ distinct real roots. -/
theorem exists_injective_family_eq_prod (hw : IsWeight μ) (n : ℕ) :
    ∃ x : Fin n → ℝ, Function.Injective x ∧ family μ n = ∏ i, (X - C (x i)) :=
  exists_injective_family_eq_prod_of_measure_compl_ne_zero hw.integrable_eval n
    (fun s _ => hw.measure_compl_ne_zero s.finite_toSet)

/-- For a weight $\mu$ and a zero $x_0$ of $p_n$, there is a polynomial $q \neq 0$ with
$\int (t - x_0) q(t)^2 \, d\mu(t) = 0$. -/
private theorem exists_integral_X_sub_C_mul_sq_eq_zero
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) {n : ℕ}
    (hnorm : ∀ j < n, normSq μ j ≠ 0) {x₀ : ℝ} (hx₀ : (family μ n).eval x₀ = 0) :
    ∃ q : ℝ[X], q ≠ 0 ∧ family μ n = (X - C x₀) * q ∧
      ∫ t, ((X - C x₀) * q ^ 2).eval t ∂μ = 0 := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ[X], family μ n = (X - C x₀) * q :=
    ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hx₀).symm⟩
  have hq0 : q ≠ 0 := fun h => family_ne_zero μ n (by rw [hq, h, mul_zero])
  have hqdeg : q.degree < n := by
    have hnat : (family μ n).natDegree = n := natDegree_eq_of_degree_eq_some (degree_family μ n)
    rw [hq, natDegree_mul (X_sub_C_ne_zero _) hq0, natDegree_X_sub_C] at hnat
    exact (natDegree_lt_iff_degree_lt hq0).mp (by omega)
  refine ⟨q, hq0, hq, ?_⟩
  rw [← integral_family_mul_of_degree_lt_of_integrable hint hnorm hqdeg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  rw [hq]
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_pow]
  ring

/-- Let $\mu$ be a weight with $t \ge a$ for $\mu$-almost every $t$. Then **every zero of $p_n$ lies
to the right of $a$**: if $p_n(x_0) = 0$, then $a < x_0$. This follows
[quarteroni2000numerical], §10.2, and [kress1998numerical], §9.3.

Write $p_n = (x - x_0) q$ with $\deg q < n$. Orthogonality gives
$\int (t - x_0) q(t)^2 \, d\mu = 0$. If $x_0 \le a$, the integrand would be nonnegative almost
everywhere, and a nonzero polynomial of constant sign cannot have integral zero against a
weight. The one-sided form serves weights whose carrier is unbounded on the other side, such as
the Laguerre weight on $(0, \infty)$; `OrthogonalPolynomial.root_family_mem_Ioo` is the
two-sided form. -/
theorem lt_root_family (hw : IsWeight μ) {a : ℝ} (hae : ∀ᵐ t ∂μ, a ≤ t) {n : ℕ} {x₀ : ℝ}
    (hx₀ : (family μ n).eval x₀ = 0) : a < x₀ := by
  obtain ⟨q, hq0, _, hzero⟩ := exists_integral_X_sub_C_mul_sq_eq_zero hw.integrable_eval
    (fun j _ => normSq_ne_zero hw j) hx₀
  have hne : (X - C x₀) * q ^ 2 ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (pow_ne_zero 2 hq0)
  by_contra h
  push Not at h
  refine (hw.integral_eval_pos_of_ae_nonneg hne ?_).ne' hzero
  filter_upwards [hae] with t ht
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_pow]
  exact mul_nonneg (by linarith) (sq_nonneg _)

/-- Let $\mu$ be a weight with $t \le b$ for $\mu$-almost every $t$. Then **every zero of $p_n$ lies
to the left of $b$**: if $p_n(x_0) = 0$, then $x_0 < b$. This is the mirror image of
`OrthogonalPolynomial.lt_root_family`, and follows [quarteroni2000numerical], §10.2, and
[kress1998numerical], §9.3. -/
theorem root_family_lt (hw : IsWeight μ) {b : ℝ} (hae : ∀ᵐ t ∂μ, t ≤ b) {n : ℕ} {x₀ : ℝ}
    (hx₀ : (family μ n).eval x₀ = 0) : x₀ < b := by
  obtain ⟨q, hq0, _, hzero⟩ := exists_integral_X_sub_C_mul_sq_eq_zero hw.integrable_eval
    (fun j _ => normSq_ne_zero hw j) hx₀
  have hne : (X - C x₀) * q ^ 2 ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (pow_ne_zero 2 hq0)
  by_contra h
  push Not at h
  have hzero' : ∫ t, (-((X - C x₀) * q ^ 2)).eval t ∂μ = 0 := by
    simp only [eval_neg]
    rw [integral_neg, hzero, neg_zero]
  refine (hw.integral_eval_pos_of_ae_nonneg (neg_ne_zero.mpr hne) ?_).ne' hzero'
  filter_upwards [hae] with t ht
  simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
  rw [neg_mul_eq_neg_mul]
  exact mul_nonneg (by linarith) (sq_nonneg _)

/-- Let $\mu$ be a weight with $\mu(\mathbb{R} \setminus [a, b]) = 0$. Then **every zero of $p_n$
lies in the open interval $(a, b)$**: if $p_n(x_0) = 0$, then $a < x_0 < b$. This follows
[quarteroni2000numerical], §10.2, and [kress1998numerical], §9.3.

The proof combines `OrthogonalPolynomial.lt_root_family` and
`OrthogonalPolynomial.root_family_lt`. -/
theorem root_family_mem_Ioo (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) {n : ℕ}
    {x₀ : ℝ} (hx₀ : (family μ n).eval x₀ = 0) : x₀ ∈ Set.Ioo a b := by
  have hae : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  exact ⟨lt_root_family hw (hae.mono fun _ ht => ht.1) hx₀,
    root_family_lt hw (hae.mono fun _ ht => ht.2) hx₀⟩

/-- Every root of $p_n$ lies in the interior of a bounded interval carrying the measure if
the measure is carried by no set of at most $n$ points. -/
theorem root_family_mem_Ioo_of_measure_compl_ne_zero [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {n : ℕ}
    (hm : ∀ s : Finset ℝ, s.card ≤ n → μ (↑s : Set ℝ)ᶜ ≠ 0) {x₀ : ℝ}
    (hx₀ : (family μ n).eval x₀ = 0) : x₀ ∈ Set.Ioo a b := by
  let hint := integrable_eval_of_measure_compl_Icc_eq_zero hsupp
  obtain ⟨q, _, hq, hzero⟩ := exists_integral_X_sub_C_mul_sq_eq_zero hint
    (fun _ hj => normSq_ne_zero_of_card_lt hint (fun s hs => hm s hs.le) hj) hx₀
  let g (t : ℝ) := ((X - C x₀) * q ^ 2).eval t
  have hg (t : ℝ) : g t = (t - x₀) * (q.eval t) ^ 2 := by simp [g, eval_mul, eval_pow]
  have hgsupp : μ (Function.support g) ≠ 0 := by
    refine measure_support_ne_zero_of_eval (family_ne_zero μ n) (hm _ ?_) (fun t ht => ?_)
    · exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans
        (natDegree_eq_of_degree_eq_some (degree_family μ n)).le)
    · rw [hq, eval_mul, eval_sub, eval_X, eval_C, mul_ne_zero_iff] at ht
      rw [hg]
      exact mul_ne_zero ht.1 (pow_ne_zero 2 ht.2)
  have hmem : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := MeasureTheory.ae_iff.2 hsupp
  constructor
  · by_contra! h
    have hpos : 0 ≤ᵐ[μ] g := hmem.mono fun t ht => by
      exact (hg t).symm ▸ mul_nonneg (sub_nonneg.2 (h.trans ht.1)) (sq_nonneg _)
    have h := (integral_pos_iff_support_of_nonneg_ae hpos (hint _)).2 (pos_iff_ne_zero.2 hgsupp)
    exact h.ne' hzero
  · by_contra! h
    have hpos : 0 ≤ᵐ[μ] fun t => -g t := hmem.mono fun t ht => by
      change 0 ≤ -g t
      rw [hg]
      exact neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.2 (ht.2.trans h)) (sq_nonneg _))
    have h := (integral_pos_iff_support_of_nonneg_ae hpos (hint _).neg).2
      (pos_iff_ne_zero.2 (by simpa using hgsupp))
    rw [integral_neg, hzero, neg_zero] at h
    exact lt_irrefl _ h

/-! ### The three-term recurrence -/

/-- The **recurrence coefficient**
$$\alpha_n = \frac{\int x \, p_n(x)^2 \, d\mu}{\|p_n\|^2}$$
of the three-term recurrence of the monic orthogonal polynomials. It is $0$ if $\|p_n\|^2 = 0$. -/
def alpha (μ : Measure ℝ) (n : ℕ) : ℝ :=
  (∫ x, x * (family μ n).eval x ^ 2 ∂μ) / normSq μ n

/-- The **recurrence coefficient**
$$\beta_n = \frac{\|p_{n+1}\|^2}{\|p_n\|^2}$$
of the three-term recurrence of the monic orthogonal polynomials. It is $0$ if $\|p_n\|^2 = 0$. -/
def beta (μ : Measure ℝ) (n : ℕ) : ℝ := normSq μ (n + 1) / normSq μ n

/-- For every measure, $x p_n - p_{n+1}$ has degree less than $n + 1$. -/
private theorem degree_X_mul_family_sub_lt (μ : Measure ℝ) (n : ℕ) :
    (X * family μ n - family μ (n + 1)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
  have h1 : (X * family μ n).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_X, degree_family]
    push_cast
    exact add_comm _ _
  have h2 : (family μ (n + 1)).degree = ((n + 1 : ℕ) : WithBot ℕ) := degree_family μ (n + 1)
  have hne : X * family μ n ≠ 0 := mul_ne_zero X_ne_zero (family_ne_zero μ n)
  have hlc : (X * family μ n).leadingCoeff = (family μ (n + 1)).leadingCoeff := by
    rw [leadingCoeff_mul, monic_X, (monic_family μ n).leadingCoeff,
      (monic_family μ (n + 1)).leadingCoeff, one_mul]
  simpa [h1] using degree_sub_lt_left (h1.trans h2.symm) hne hlc

/-- If polynomial evaluations are integrable and the norms below degree $n+1$ are nonzero,
then $\int x \, p_{n+1} p_n \, d\mu = \|p_{n+1}\|^2$. -/
theorem integral_X_mul_family_succ_mul_family_of_integrable
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) {n : ℕ}
    (hnorm : ∀ j < n + 1, normSq μ j ≠ 0) :
    ∫ x, x * (family μ (n + 1)).eval x * (family μ n).eval x ∂μ = normSq μ (n + 1) := by
  have hsplit : ∀ x : ℝ, x * (family μ (n + 1)).eval x * (family μ n).eval x =
      (family μ (n + 1)).eval x ^ 2 +
        (family μ (n + 1)).eval x * (X * family μ n - family μ (n + 1)).eval x := by
    intro x
    simp only [eval_sub, eval_mul, eval_X]
    ring
  simp only [hsplit]
  have hsq := hint (family μ (n + 1) ^ 2)
  have hprod := hint (family μ (n + 1) * (X * family μ n - family μ (n + 1)))
  simp only [eval_pow] at hsq
  simp only [eval_mul] at hprod
  have hprod' : Integrable (fun x => (family μ (n + 1)).eval x *
      (X * family μ n - family μ (n + 1)).eval x) μ := hprod
  rw [integral_add hsq hprod', integral_family_mul_of_degree_lt_of_integrable hint hnorm
    (degree_X_mul_family_sub_lt μ n), add_zero]
  rfl

/-- For a weight $\mu$, $\int x \, p_{n+1} p_n \, d\mu = \|p_{n+1}\|^2$. -/
theorem integral_X_mul_family_succ_mul_family (hw : IsWeight μ) (n : ℕ) :
    ∫ x, x * (family μ (n + 1)).eval x * (family μ n).eval x ∂μ = normSq μ (n + 1) :=
  integral_X_mul_family_succ_mul_family_of_integrable hw.integrable_eval
    (fun j _ => normSq_ne_zero hw j)

/-- For every measure $\mu$, the first monic orthogonal polynomial is $p_1 = x - \alpha_0$. This is
the first Gram–Schmidt step, so no orthogonality is needed. -/
theorem family_one (μ : Measure ℝ) : family μ 1 = X - C (alpha μ 0) := by
  rw [family_eq, alpha, normSq]
  simp

/-- Multiplication by $x$ moves from one factor to the other: $\int x \, p_m p_k \, d\mu = \int p_m
\cdot (x p_k) \, d\mu$. -/
private theorem integral_X_mul_family_mul_family (μ : Measure ℝ) (m k : ℕ) :
    ∫ x, x * (family μ m).eval x * (family μ k).eval x ∂μ
      = ∫ x, (family μ m).eval x * (X * family μ k).eval x ∂μ :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [eval_mul, eval_X]; ring)

private theorem integral_family_mul_self (μ : Measure ℝ) (m : ℕ) :
    ∫ x, (family μ m).eval x * (family μ m).eval x ∂μ = normSq μ m :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => (sq ((family μ m).eval x)).symm)

private theorem integral_X_mul_family_mul_self (μ : Measure ℝ) (m : ℕ) :
    ∫ x, x * (family μ m).eval x * (family μ m).eval x ∂μ
      = ∫ x, x * (family μ m).eval x ^ 2 ∂μ :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- The three-term recurrence of the monic orthogonal polynomials at degree $n+2$ needs
integrable polynomial evaluations and nonzero norms only through degree $n+1$:
$$p_{n+2} = (x - \alpha_{n+1}) \, p_{n+1} - \beta_n \, p_n.$$
This includes the first vanishing-norm polynomial for a finite distribution. -/
theorem three_term_recurrence_of_integrable
    (hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ) {n : ℕ}
    (hnorm : ∀ j < n + 2, normSq μ j ≠ 0) :
    family μ (n + 2) =
      (X - C (alpha μ (n + 1))) * family μ (n + 1) - C (beta μ n) * family μ n := by
  have hort {i j : ℕ} (hi : i ≤ n + 2) (hj : j ≤ n + 2) (hne : i ≠ j) :
      ∫ x, (family μ i).eval x * (family μ j).eval x ∂μ = 0 :=
    integral_family_mul_family_of_ne_of_integrable hint hnorm hi hj hne
  have hint_mul (p q : ℝ[X]) : Integrable (fun x => p.eval x * q.eval x) μ := by
    simpa only [eval_mul] using hint (p * q)
  refine sub_eq_zero.mp (eq_zero_of_degree_lt_of_integrable hint hnorm ?_ ?_)
  · have hrw : family μ (n + 2) -
        ((X - C (alpha μ (n + 1))) * family μ (n + 1) - C (beta μ n) * family μ n) =
        -(X * family μ (n + 1) - family μ (n + 2)) +
          (C (alpha μ (n + 1)) * family μ (n + 1) + C (beta μ n) * family μ n) := by ring
    rw [hrw]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · rw [degree_neg]
      exact degree_X_mul_family_sub_lt μ (n + 1)
    · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact degree_C_mul_family_lt μ _ (by omega)
      · exact degree_C_mul_family_lt μ _ (by omega)
  · intro k hk
    have hi1 : Integrable (fun x => (family μ (n + 2)).eval x * (family μ k).eval x) μ :=
      hint_mul _ _
    have hi2 : Integrable
        (fun x => x * (family μ (n + 1)).eval x * (family μ k).eval x) μ :=
      (hint (X * family μ (n + 1) * family μ k)).congr
        (Filter.Eventually.of_forall fun x => by simp [mul_assoc])
    have hi3 : Integrable (fun x => alpha μ (n + 1) *
        ((family μ (n + 1)).eval x * (family μ k).eval x)) μ :=
      (hint_mul _ _).const_mul _
    have hi4 : Integrable (fun x => beta μ n *
        ((family μ n).eval x * (family μ k).eval x)) μ :=
      (hint_mul _ _).const_mul _
    have hi12 : Integrable (fun x => (family μ (n + 2)).eval x * (family μ k).eval x -
        x * (family μ (n + 1)).eval x * (family μ k).eval x) μ := hi1.sub hi2
    have hi123 : Integrable (fun x => (family μ (n + 2)).eval x * (family μ k).eval x -
        x * (family μ (n + 1)).eval x * (family μ k).eval x +
        alpha μ (n + 1) * ((family μ (n + 1)).eval x * (family μ k).eval x)) μ := hi12.add hi3
    have hev : ∀ x : ℝ,
        (family μ (n + 2) -
            ((X - C (alpha μ (n + 1))) * family μ (n + 1) - C (beta μ n) * family μ n)).eval x *
          (family μ k).eval x =
          (family μ (n + 2)).eval x * (family μ k).eval x -
            x * (family μ (n + 1)).eval x * (family μ k).eval x +
            alpha μ (n + 1) * ((family μ (n + 1)).eval x * (family μ k).eval x) +
            beta μ n * ((family μ n).eval x * (family μ k).eval x) := by
      intro x
      simp only [eval_sub, eval_mul, eval_X, eval_C]
      ring
    simp only [hev]
    rw [integral_add hi123 hi4, integral_add hi12 hi3, integral_sub hi1 hi2,
      integral_const_mul, integral_const_mul,
      hort (i := n + 2) (j := k) le_rfl hk.le (by omega),
      integral_X_mul_family_mul_family]
    rcases lt_trichotomy k n with hkn | hkn | hkn
    · rw [integral_family_mul_of_degree_lt_of_integrable hint
        (fun j hj => hnorm j (by omega : j < n + 2)) (degree_X_mul_family_lt μ (by omega)),
        hort (i := n + 1) (j := k) (by omega) hk.le (by omega),
        hort (i := n) (j := k) (by omega) hk.le (by omega)]
      ring
    · rw [hkn, ← integral_X_mul_family_mul_family,
        integral_X_mul_family_succ_mul_family_of_integrable hint (n := n)
          (fun j hj => hnorm j (by omega)),
        hort (i := n + 1) (j := n) (by omega) (by omega) (by omega), integral_family_mul_self]
      simp only [beta]
      rw [div_mul_cancel₀ _ (hnorm n (by omega))]
      ring
    · rw [show k = n + 1 by omega, ← integral_X_mul_family_mul_family,
        integral_X_mul_family_mul_self, integral_family_mul_self,
        hort (i := n) (j := n + 1) (by omega) (by omega) (by omega)]
      simp only [alpha]
      rw [div_mul_cancel₀ _ (hnorm (n + 1) (by omega))]
      ring

/-- The **three-term recurrence** of the monic orthogonal polynomials for a weight is
$$p_{n+2} = (x - \alpha_{n+1}) \, p_{n+1} - \beta_n \, p_n.$$
Together with `OrthogonalPolynomial.family_one`, it determines the whole family from $p_0=1$.
This is the content of Exercises 3.5.5–3.5.6 of [han2009theoretical]. -/
theorem three_term_recurrence (hw : IsWeight μ) (n : ℕ) :
    family μ (n + 2) =
      (X - C (alpha μ (n + 1))) * family μ (n + 1) - C (beta μ n) * family μ n :=
  three_term_recurrence_of_integrable hw.integrable_eval (fun j _ => normSq_ne_zero hw j)

/-! ### Reading the recurrence coefficients off a recurrence -/

/-- For every measure $\mu$ and every real $a$: if $p_1 = x - a$, then $\alpha_0 = a$. -/
theorem alpha_zero_eq_of_family_one {a : ℝ} (h : family μ 1 = X - C a) : alpha μ 0 = a := by
  have h1 := family_one μ
  rw [h] at h1
  have := congrArg (fun p : ℝ[X] => p.coeff 0) h1
  simpa using this.symm

/-- **A three-term recurrence determines the recurrence coefficients.** Let $\mu$ be a weight, and
let $a, b \in \mathbb{R}$ satisfy
$$p_{n+2} = (x - a) \, p_{n+1} - b \, p_n.$$
Then $a = \alpha_{n+1}$ and $b = \beta_n$.

Subtracting `OrthogonalPolynomial.three_term_recurrence` leaves
$(\alpha_{n+1} - a) p_{n+1} = (\beta_n - b) p_n$, and the two sides have different degrees
unless both vanish. This computes the recurrence coefficients of the classical weights from
their classical recurrences, without any integration. -/
theorem alpha_succ_eq_and_beta_eq_of_recurrence (hw : IsWeight μ) {n : ℕ} {a b : ℝ}
    (h : family μ (n + 2) = (X - C a) * family μ (n + 1) - C b * family μ n) :
    alpha μ (n + 1) = a ∧ beta μ n = b := by
  have hrec := three_term_recurrence hw n
  rw [h] at hrec
  have hkey : C (alpha μ (n + 1) - a) * family μ (n + 1) = C (b - beta μ n) * family μ n := by
    simp only [C_sub]
    linear_combination hrec
  have ha : alpha μ (n + 1) = a := by
    by_contra hne
    have hne' : alpha μ (n + 1) - a ≠ 0 := sub_ne_zero.mpr hne
    have hdeg := congrArg Polynomial.degree hkey
    rw [degree_C_mul hne', degree_family] at hdeg
    have hle : (C (b - beta μ n) * family μ n).degree ≤ n := by
      refine (degree_mul_le _ _).trans ?_
      rw [degree_family]
      calc (C (b - beta μ n) : ℝ[X]).degree + (n : WithBot ℕ) ≤ 0 + (n : WithBot ℕ) := by
            gcongr; exact degree_C_le
        _ = (n : WithBot ℕ) := zero_add _
    rw [← hdeg] at hle
    exact absurd hle (by exact_mod_cast Nat.not_succ_le_self n)
  refine ⟨ha, ?_⟩
  rw [ha, sub_self, C_0, zero_mul] at hkey
  rcases mul_eq_zero.mp hkey.symm with h0 | h0
  · exact (sub_eq_zero.mp (C_eq_zero.mp h0)).symm
  · exact absurd h0 (family_ne_zero μ n)

/-! ### The Christoffel–Darboux identity -/

/-- The **Christoffel–Darboux kernel** of $\mu$ with parameter $t \in \mathbb{R}$, as a polynomial
in $x$:
$$K_N(x, t) = \sum_{k=0}^{N} \frac{p_k(t)}{\|p_k\|^2} \, p_k(x).$$
For a weight $\mu$, it is the reproducing kernel of the polynomials of degree at most $N$ in
$L^2(\mu)$. -/
def cdKernel (μ : Measure ℝ) (N : ℕ) (t : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1), C ((family μ k).eval t / normSq μ k) * family μ k

/-- For a weight $\mu$, the squared norms satisfy $\|p_{N+1}\|^2 = \beta_N \|p_N\|^2$. -/
theorem normSq_succ (hw : IsWeight μ) (N : ℕ) :
    normSq μ (N + 1) = beta μ N * normSq μ N := by
  rw [beta, div_mul_cancel₀ _ (normSq_ne_zero hw N)]

/-- The **Christoffel–Darboux identity** for the monic orthogonal polynomials. Let $\mu$ be a
weight, let $N \in \mathbb{N}$ and let $t \in \mathbb{R}$. Then, as polynomials in $x$,
$$\|p_N\|^2 \, (x - t) \, K_N(x, t) = p_{N+1}(x) \, p_N(t) - p_N(x) \, p_{N+1}(t).$$
[han2009theoretical], Theorem 3.7.3, states the identity for the orthonormal polynomials.

The proof is an induction on $N$ with the three-term recurrence. The induction step is
$$p_{N+2}(x) p_{N+1}(t) - p_{N+1}(x) p_{N+2}(t) = (x - t) \, p_{N+1}(x) p_{N+1}(t) + \beta_N
  \bigl(p_{N+1}(x) p_N(t) - p_N(x) p_{N+1}(t)\bigr).$$
The kernel is `OrthogonalPolynomial.cdKernel μ N t`. -/
theorem christoffel_darboux (hw : IsWeight μ) (N : ℕ) (t : ℝ) :
    C (normSq μ N) * ((X - C t) * cdKernel μ N t) =
      family μ (N + 1) * C ((family μ N).eval t) - family μ N * C ((family μ (N + 1)).eval t) := by
  induction N with
  | zero =>
    rw [cdKernel, zero_add, Finset.sum_range_one, family_zero, family_one]
    simp only [eval_one, one_div, mul_one, eval_sub, eval_X, eval_C, C_sub, C_1]
    rw [show C (normSq μ 0) * ((X - C t) * C (normSq μ 0)⁻¹) =
      (C (normSq μ 0) * C (normSq μ 0)⁻¹) * (X - C t) by ring, ← C_mul,
      mul_inv_cancel₀ (normSq_ne_zero hw 0), C_1]
    ring
  | succ N ih =>
    have hne : normSq μ (N + 1) ≠ 0 := normSq_ne_zero hw (N + 1)
    have hK : cdKernel μ (N + 1) t = cdKernel μ N t +
        C ((family μ (N + 1)).eval t / normSq μ (N + 1)) * family μ (N + 1) := by
      rw [cdKernel, Finset.sum_range_succ]
      rfl
    have e1 : C (normSq μ (N + 1)) * ((X - C t) *
        (C ((family μ (N + 1)).eval t / normSq μ (N + 1)) * family μ (N + 1))) =
        (X - C t) * (C ((family μ (N + 1)).eval t) * family μ (N + 1)) := by
      rw [show C (normSq μ (N + 1)) * ((X - C t) *
          (C ((family μ (N + 1)).eval t / normSq μ (N + 1)) * family μ (N + 1))) =
          (X - C t) * ((C (normSq μ (N + 1)) *
            C ((family μ (N + 1)).eval t / normSq μ (N + 1))) * family μ (N + 1)) by ring,
        ← C_mul, mul_div_cancel₀ _ hne]
    have e2 : C (normSq μ (N + 1)) * ((X - C t) * cdKernel μ N t) =
        C (beta μ N) * (family μ (N + 1) * C ((family μ N).eval t) -
          family μ N * C ((family μ (N + 1)).eval t)) := by
      rw [normSq_succ hw N, C_mul, mul_assoc, ih]
    rw [hK, mul_add, mul_add, e1, e2, three_term_recurrence hw N]
    simp only [eval_sub, eval_mul, eval_X, eval_C, C_sub, C_mul]
    ring

/-- For a weight $\mu$, the Christoffel–Darboux kernel is positive on the diagonal:
$$K_N(t, t) = \sum_{k=0}^{N} \frac{p_k(t)^2}{\|p_k\|^2} > 0.$$
The term with $k = 0$ is $1 / \|p_0\|^2 > 0$. -/
theorem eval_cdKernel_self_pos (hw : IsWeight μ) (N : ℕ) (t : ℝ) :
    0 < (cdKernel μ N t).eval t := by
  rw [cdKernel, eval_finsetSum, Finset.sum_range_succ']
  simp only [eval_mul, eval_C, family_zero, eval_one, mul_one]
  refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun k _ => ?_) ?_
  · rw [div_mul_eq_mul_div, ← sq]
    exact div_nonneg (sq_nonneg _) (normSq_pos hw _).le
  · exact one_div_pos.mpr (normSq_pos hw 0)

/-- For a weight $\mu$, the Christoffel–Darboux kernel has integral $1$:
$$\int K_N(x, t) \, d\mu(x) = 1.$$
Only the constant term $p_0 / \|p_0\|^2$ contributes, because the other members of the family
are orthogonal to the constants. -/
theorem integral_eval_cdKernel (hw : IsWeight μ) (N : ℕ) (t : ℝ) :
    ∫ x, (cdKernel μ N t).eval x ∂μ = 1 := by
  simp only [cdKernel, eval_finsetSum, eval_mul, eval_C]
  rw [integral_finsetSum _ fun k _ => (hw.integrable_eval _).const_mul _, Finset.sum_range_succ']
  simp only [integral_const_mul, family_zero, eval_one, one_div]
  rw [Finset.sum_eq_zero fun k _ => ?_, zero_add]
  · have h0 : ∫ x, (1 : ℝ) ∂μ = normSq μ 0 := by
      rw [normSq, family_zero]
      simp
    rw [h0, inv_mul_cancel₀ (normSq_ne_zero hw 0)]
  · have h : ∫ x, (family μ (k + 1)).eval x ∂μ = 0 := by
      have := integral_family_mul_of_degree_lt hw (n := k + 1) (q := 1)
        (by rw [degree_one]; exact_mod_cast Nat.succ_pos k)
      simpa using this
    rw [h, mul_zero]

/-! ### The orthonormal polynomials -/

/-- The $L^2(\mu)$ norm $\|p_n\| = \sqrt{\|p_n\|^2}$ of the $n$-th monic orthogonal polynomial. -/
noncomputable def normOf (μ : Measure ℝ) (n : ℕ) : ℝ := Real.sqrt (normSq μ n)

/-- For a weight $\mu$, the norm $\|p_n\|$ is positive. -/
theorem normOf_pos (hw : IsWeight μ) (n : ℕ) : 0 < normOf μ n :=
  Real.sqrt_pos.2 (normSq_pos hw n)

/-- For a weight $\mu$, the square of the norm $\|p_n\|$ is $\|p_n\|^2 = \int p_n^2 \, d\mu$. -/
theorem sq_normOf (hw : IsWeight μ) (n : ℕ) : normOf μ n ^ 2 = normSq μ n :=
  Real.sq_sqrt (normSq_pos hw n).le

/-- The **orthonormal polynomials** of $\mu$: the monic orthogonal polynomials scaled to unit norm,
$$\hat p_n = \frac{1}{\|p_n\|} \, p_n.$$
This is the family with which [han2009theoretical], §3.7.2, works, where the normalization
$(p_n, p_n) = 1$ is taken without loss of generality.

If $\|p_n\| = 0$, then $\hat p_n = 0$, by the convention for division by zero. -/
noncomputable def orthonormalFamily (μ : Measure ℝ) (n : ℕ) : ℝ[X] :=
  C (normOf μ n)⁻¹ * family μ n

/-- The value of the orthonormal polynomial at $x$ is $\hat p_n(x) = p_n(x) / \|p_n\|$. -/
theorem eval_orthonormalFamily (μ : Measure ℝ) (n : ℕ) (x : ℝ) :
    (orthonormalFamily μ n).eval x = (normOf μ n)⁻¹ * (family μ n).eval x := by
  rw [orthonormalFamily, eval_mul, eval_C]

/-- Let $\mu$ be a weight, and let $m \neq n$. Then the orthonormal polynomials $\hat p_m$ and
$\hat p_n$ are orthogonal:
$$\int \hat p_m \hat p_n \, d\mu = 0.$$
-/
theorem integral_orthonormalFamily_mul (hw : IsWeight μ) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x, (orthonormalFamily μ m).eval x * (orthonormalFamily μ n).eval x ∂μ = 0 := by
  have h : ∀ x : ℝ, (orthonormalFamily μ m).eval x * (orthonormalFamily μ n).eval x
      = ((normOf μ m)⁻¹ * (normOf μ n)⁻¹) *
        ((family μ m).eval x * (family μ n).eval x) := fun x => by
    rw [eval_orthonormalFamily, eval_orthonormalFamily]; ring
  simp only [h]
  rw [integral_const_mul, integral_family_mul_family hw hmn, mul_zero]

/-- Let $\mu$ be a weight. Then the orthonormal polynomials have unit norm:
$$\int \hat p_n^2 \, d\mu = 1.$$
-/
theorem integral_orthonormalFamily_sq (hw : IsWeight μ) (n : ℕ) :
    ∫ x, (orthonormalFamily μ n).eval x ^ 2 ∂μ = 1 := by
  have hn := (normOf_pos hw n).ne'
  have h : ∀ x : ℝ, (orthonormalFamily μ n).eval x ^ 2
      = ((normOf μ n)⁻¹ ^ 2) * ((family μ n).eval x ^ 2) := fun x => by
    rw [eval_orthonormalFamily]; ring
  simp only [h]
  rw [integral_const_mul]
  change (normOf μ n)⁻¹ ^ 2 * normSq μ n = 1
  rw [← sq_normOf hw n]
  field_simp

/-- For a weight $\mu$, the orthonormal polynomial $\hat p_n$ has degree $n$. -/
theorem degree_orthonormalFamily (hw : IsWeight μ) (n : ℕ) :
    (orthonormalFamily μ n).degree = n := by
  rw [orthonormalFamily, degree_C_mul (by
    simpa using inv_ne_zero (normOf_pos hw n).ne'), degree_family]

/-- For every measure $\mu$, the leading coefficient $A_n$ of $\hat p_n$ is $1 / \|p_n\|$. -/
theorem leadingCoeff_orthonormalFamily (μ : Measure ℝ) (n : ℕ) :
    (orthonormalFamily μ n).leadingCoeff = (normOf μ n)⁻¹ := by
  rw [orthonormalFamily, leadingCoeff_mul, leadingCoeff_C, (monic_family μ n).leadingCoeff,
    mul_one]

/-- **Uniqueness of the monic orthogonal polynomials.** Let $\mu$ be a weight, and let $q$ be a
polynomial of degree $n$ with $\int q r \, d\mu = 0$ for every polynomial $r$ of degree less
than $n$. Then $q$ is its leading coefficient times $p_n$:
$$q = \operatorname{lc}(q) \, p_n.$$
This is Fact 1 of [golub2013matrix], §10.2.3.

The difference $q - \operatorname{lc}(q) p_n$ has degree less than $n$ and is orthogonal to
$p_0, \dots, p_{n-1}$, so it vanishes by `OrthogonalPolynomial.eq_zero_of_degree_lt`. -/
theorem eq_C_leadingCoeff_mul_family (hw : IsWeight μ) {n : ℕ} {q : ℝ[X]} (hq : q.degree = n)
    (horth : ∀ r : ℝ[X], r.degree < n → ∫ x, q.eval x * r.eval x ∂μ = 0) :
    q = C q.leadingCoeff * family μ n := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  set c := q.leadingCoeff with hcdef
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.2 hq0
  have hdegC : (C c * family μ n).degree = n := by
    rw [degree_C_mul hc0, degree_family]
  have hlt : (q - C c * family μ n).degree < n := by
    have h := degree_sub_lt_left (p := q) (q := C c * family μ n) (by rw [hq, hdegC]) hq0
      (by rw [leadingCoeff_mul, leadingCoeff_C, (monic_family μ n).leadingCoeff, mul_one])
    rwa [hq] at h
  refine sub_eq_zero.1 (eq_zero_of_degree_lt hw hlt fun j hj => ?_)
  have e : ∀ x, (q - C c * family μ n).eval x * (family μ j).eval x =
      q.eval x * (family μ j).eval x - c * ((family μ n).eval x * (family μ j).eval x) :=
    fun x => by simp only [eval_sub, eval_mul, eval_C]; ring
  simp_rw [e]
  rw [integral_sub (hw.integrable_eval_mul q _) ((hw.integrable_eval_mul _ _).const_mul c),
    integral_const_mul, horth _ (by rw [degree_family]; exact_mod_cast hj),
    integral_family_mul_family hw (by omega), mul_zero, sub_zero]

/-- **Uniqueness of the orthonormal polynomials up to sign.** Let $\mu$ be a weight, and let $q$ be
a polynomial of degree $n$ with $\int q r \, d\mu = 0$ for every polynomial $r$ of degree less
than $n$, and with $\int q^2 \, d\mu = 1$. Then
$$q = \hat p_n \quad \text{or} \quad q = -\hat p_n.$$
This is Fact 1 of [golub2013matrix], §10.2.3. -/
theorem eq_orthonormalFamily_or_eq_neg (hw : IsWeight μ) {n : ℕ} {q : ℝ[X]} (hq : q.degree = n)
    (horth : ∀ r : ℝ[X], r.degree < n → ∫ x, q.eval x * r.eval x ∂μ = 0)
    (hq1 : ∫ x, q.eval x ^ 2 ∂μ = 1) :
    q = orthonormalFamily μ n ∨ q = -orthonormalFamily μ n := by
  have hfam := eq_C_leadingCoeff_mul_family hw hq horth
  set c := q.leadingCoeff
  have hsq : c ^ 2 * normSq μ n = 1 := by
    rw [← hq1, hfam, normSq]
    simp only [eval_mul, eval_C, mul_pow]
    exact (integral_const_mul _ _).symm
  have hc2 : c ^ 2 = (normOf μ n)⁻¹ ^ 2 := by
    rw [inv_pow, sq_normOf hw]
    field_simp [(normSq_pos hw n).ne']
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hc2 with h | h
  · left
    rw [hfam, h, orthonormalFamily]
  · right
    rw [hfam, h, orthonormalFamily, C_neg, neg_mul]

/-! ### The three-term recurrence of the orthonormal polynomials -/

/-- The coefficient $a_n = \|p_n\| / \|p_{n+1}\|$ of $x$ in the three-term recurrence of the
orthonormal polynomials.

It is the ratio $A_{n+1} / A_n$ of consecutive leading coefficients
(`OrthogonalPolynomial.cdA_eq_leadingCoeff_div`), which is the form in which
[han2009theoretical], Theorem 3.7.3, states it. -/
noncomputable def cdA (μ : Measure ℝ) (n : ℕ) : ℝ := normOf μ n / normOf μ (n + 1)

/-- The constant coefficient $b_n = -\alpha_n a_n$ of the three-term recurrence of the orthonormal
polynomials, where $\alpha_n$ is the recurrence coefficient of the monic family. -/
noncomputable def cdB (μ : Measure ℝ) (n : ℕ) : ℝ := -(alpha μ n * cdA μ n)

/-- The coefficient
$$c_n = \frac{\|p_n\|^2}{\|p_{n-1}\| \, \|p_{n+1}\|}$$
of the three-term recurrence of the orthonormal polynomials. Only the values at $n \ge 1$ are
used; at $n = 0$ the index $n - 1$ is truncated subtraction, so
$c_0 = \|p_0\|^2 / (\|p_0\| \, \|p_1\|)$. -/
noncomputable def cdC (μ : Measure ℝ) (n : ℕ) : ℝ :=
  normOf μ n * normOf μ n / (normOf μ (n - 1) * normOf μ (n + 1))

/-- For a weight $\mu$, the coefficient $a_n = \|p_n\| / \|p_{n+1}\|$ is positive. -/
theorem cdA_pos (hw : IsWeight μ) (n : ℕ) : 0 < cdA μ n :=
  div_pos (normOf_pos hw n) (normOf_pos hw (n + 1))

/-- Let $\mu$ be a weight. Then the recurrence coefficient $a_n$ is the ratio of the leading
coefficients of consecutive orthonormal polynomials:
$$a_n = \frac{\operatorname{lc}(\hat p_{n+1})}{\operatorname{lc}(\hat p_n)}.$$
This is the form in which the Christoffel–Darboux identity is usually stated. -/
theorem cdA_eq_leadingCoeff_div (hw : IsWeight μ) (n : ℕ) :
    cdA μ n = (orthonormalFamily μ (n + 1)).leadingCoeff /
      (orthonormalFamily μ n).leadingCoeff := by
  have h0 := (normOf_pos hw n).ne'
  have h1 := (normOf_pos hw (n + 1)).ne'
  rw [leadingCoeff_orthonormalFamily, leadingCoeff_orthonormalFamily, cdA]
  field_simp

/-- For a weight $\mu$, the first step of the three-term recurrence of the orthonormal polynomials
is $\hat p_1 = (a_0 x + b_0) \, \hat p_0$. -/
theorem orthonormalFamily_one (hw : IsWeight μ) :
    orthonormalFamily μ 1 = (C (cdA μ 0) * X + C (cdB μ 0)) * orthonormalFamily μ 0 := by
  have h0 := (normOf_pos hw 0).ne'
  have h1 := (normOf_pos hw 1).ne'
  have e1 : cdA μ 0 * (normOf μ 0)⁻¹ = (normOf μ 1)⁻¹ := by
    rw [cdA]; field_simp
  have e2 : cdB μ 0 * (normOf μ 0)⁻¹ = -(alpha μ 0 * (normOf μ 1)⁻¹) := by
    rw [cdB, cdA]; field_simp
  rw [orthonormalFamily, orthonormalFamily, family_one, family_zero, mul_one]
  have hsplit : (C (cdA μ 0) * X + C (cdB μ 0)) * C (normOf μ 0)⁻¹
      = C (cdA μ 0 * (normOf μ 0)⁻¹) * X + C (cdB μ 0 * (normOf μ 0)⁻¹) := by
    simp only [C_mul]; ring
  rw [hsplit, e1, e2, C_neg, C_mul]
  ring

/-- The **three-term recurrence of the orthonormal polynomials**. Let $\mu$ be a weight. Then for
every $n$,
$$\hat p_{n+2} = (a_{n+1} x + b_{n+1}) \, \hat p_{n+1} - c_{n+1} \, \hat p_n,$$
with $a_n$, $b_n$ and $c_n$ as in `OrthogonalPolynomial.cdA`, `OrthogonalPolynomial.cdB` and
`OrthogonalPolynomial.cdC`. This is the form that the Christoffel–Darboux identity for the
orthonormal family uses. -/
theorem orthonormalFamily_recurrence (hw : IsWeight μ) (n : ℕ) :
    orthonormalFamily μ (n + 2)
      = (C (cdA μ (n + 1)) * X + C (cdB μ (n + 1))) * orthonormalFamily μ (n + 1)
        - C (cdC μ (n + 1)) * orthonormalFamily μ n := by
  have h0 := (normOf_pos hw n).ne'
  have h1 := (normOf_pos hw (n + 1)).ne'
  have h2 := (normOf_pos hw (n + 2)).ne'
  have e1 : cdA μ (n + 1) * (normOf μ (n + 1))⁻¹ = (normOf μ (n + 2))⁻¹ := by
    rw [cdA]; field_simp
  have e2 : cdB μ (n + 1) * (normOf μ (n + 1))⁻¹
      = -(alpha μ (n + 1) * (normOf μ (n + 2))⁻¹) := by
    rw [cdB, cdA]; field_simp
  have e3 : cdC μ (n + 1) * (normOf μ n)⁻¹ = beta μ n * (normOf μ (n + 2))⁻¹ := by
    have hb : beta μ n = normOf μ (n + 1) ^ 2 / normOf μ n ^ 2 := by
      rw [beta, sq_normOf hw, sq_normOf hw]
    rw [cdC, hb]
    simp only [Nat.add_sub_cancel]
    field_simp
  rw [orthonormalFamily, orthonormalFamily, orthonormalFamily, three_term_recurrence hw n]
  have hsplit : (C (cdA μ (n + 1)) * X + C (cdB μ (n + 1))) *
        (C (normOf μ (n + 1))⁻¹ * family μ (n + 1))
      - C (cdC μ (n + 1)) * (C (normOf μ n)⁻¹ * family μ n)
      = (C (cdA μ (n + 1) * (normOf μ (n + 1))⁻¹) * X
          + C (cdB μ (n + 1) * (normOf μ (n + 1))⁻¹)) * family μ (n + 1)
        - C (cdC μ (n + 1) * (normOf μ n)⁻¹) * family μ n := by
    simp only [C_mul]; ring
  rw [hsplit, e1, e2, e3, C_neg, C_mul, C_mul]
  ring

/-- For a weight $\mu$, the coefficients of the orthonormal recurrence satisfy
$c_{n+1} a_n = a_{n+1}$. -/
theorem cdC_mul_cdA (hw : IsWeight μ) (n : ℕ) : cdC μ (n + 1) * cdA μ n = cdA μ (n + 1) := by
  have h0 := (normOf_pos hw n).ne'
  have h1 := (normOf_pos hw (n + 1)).ne'
  have h2 := (normOf_pos hw (n + 2)).ne'
  rw [cdC, cdA, cdA]
  simp only [Nat.add_sub_cancel]
  field_simp

/-! ### The Jacobi matrix -/

/-- The **Jacobi matrix** of $\mu$: the symmetric tridiagonal $n \times n$ matrix
$$J_n = \begin{bmatrix} \alpha_0 & \sqrt{\beta_0} & & \\ \sqrt{\beta_0} & \alpha_1 & \ddots & \\
  & \ddots & \ddots & \sqrt{\beta_{n-2}} \\ & & \sqrt{\beta_{n-2}} & \alpha_{n-1}
  \end{bmatrix}.$$
Its characteristic polynomial is $p_n$ (`OrthogonalPolynomial.charpoly_jacobiMatrix`), so the
Gauss nodes of $\mu$ are its eigenvalues. This is the Golub–Welsch method for the nodes, which
[quarteroni2000numerical], §10.6 (Programs 85–87), follows.

Rows and columns are indexed by `Fin n` from $0$. The square root is `Real.sqrt`, which is $0$
at negative arguments. -/
def jacobiMatrix (μ : Measure ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha μ i
    else if (j : ℕ) = i + 1 then Real.sqrt (beta μ i)
    else if (i : ℕ) = j + 1 then Real.sqrt (beta μ j)
    else 0

/-- The entries of the Jacobi matrix: $\alpha_i$ at $(i, i)$, $\sqrt{\beta_i}$ at $(i, i + 1)$,
$\sqrt{\beta_j}$ at $(j + 1, j)$, and $0$ elsewhere. -/
theorem jacobiMatrix_apply (μ : Measure ℝ) {n : ℕ} (i j : Fin n) :
    jacobiMatrix μ n i j =
      if (i : ℕ) = j then alpha μ i
      else if (j : ℕ) = i + 1 then Real.sqrt (beta μ i)
      else if (i : ℕ) = j + 1 then Real.sqrt (beta μ j)
      else 0 := rfl

/-- For every measure $\mu$ and every $n$, the Jacobi matrix $J_n$ is symmetric. -/
theorem jacobiMatrix_isSymm (μ : Measure ℝ) (n : ℕ) : (jacobiMatrix μ n).IsSymm := by
  ext i j
  rw [Matrix.transpose_apply]
  rcases eq_or_ne (i : ℕ) j with h | h
  · rw [Fin.ext h]
  · simp only [jacobiMatrix_apply, h, Ne.symm h, ite_false]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- The leading $n \times n$ submatrix of the characteristic matrix of $J_{n+1}$ is the
characteristic matrix of $J_n$. -/
private theorem charmatrix_jacobiMatrix_submatrix (μ : Measure ℝ) (n : ℕ) :
    (Matrix.charmatrix (jacobiMatrix μ (n + 1))).submatrix Fin.castSucc Fin.castSucc =
      Matrix.charmatrix (jacobiMatrix μ n) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply,
    Fin.castSucc_inj, jacobiMatrix_apply, Fin.val_castSucc]

/-- **The characteristic polynomial of the Jacobi matrix is the orthogonal polynomial.** Let $\mu$
be a weight. Then for every $n$,
$$\det(x I - J_n) = p_n.$$
Hence the Gauss nodes of $\mu$ are the eigenvalues of $J_n$ (Golub–Welsch). This underlies
[quarteroni2000numerical], §10.6, Programs 85–87.

Laplace expansion of the tridiagonal determinant $D_n = \det(x I - J_n)$ along its last row
gives $D_{n+2} = (x - \alpha_{n+1}) D_{n+1} - \beta_n D_n$, because the square of the
off-diagonal entry $\sqrt{\beta_n}$ is $\beta_n \ge 0$. This is
`OrthogonalPolynomial.three_term_recurrence`, with the same initial values $1$ and
$x - \alpha_0$. -/
theorem charpoly_jacobiMatrix_of_integrable
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) (n : ℕ)
    (hnorm : ∀ j < n, normSq μ j ≠ 0) :
    (jacobiMatrix μ n).charpoly = family μ n := by
  have hrec : ∀ m, (jacobiMatrix μ (m + 2)).charpoly =
      (X - C (alpha μ (m + 1))) * (jacobiMatrix μ (m + 1)).charpoly -
        C (beta μ m) * (jacobiMatrix μ m).charpoly := by
    intro m
    have hn (k : ℕ) : 0 ≤ normSq μ k := integral_nonneg (fun t => sq_nonneg _)
    have hβ : 0 ≤ beta μ m := div_nonneg (hn _) (hn _)
    have hdet : ∀ k, (jacobiMatrix μ k).charpoly = (Matrix.charmatrix (jacobiMatrix μ k)).det :=
      fun k => rfl
    rw [hdet, hdet, hdet, Matrix.det_succ_succ_of_last_row_col]
    · rw [charmatrix_jacobiMatrix_submatrix, ← Matrix.submatrix_submatrix,
        charmatrix_jacobiMatrix_submatrix, charmatrix_jacobiMatrix_submatrix]
      have h1 : Matrix.charmatrix (jacobiMatrix μ (m + 2)) (Fin.last (m + 1)) (Fin.last (m + 1)) =
          X - C (alpha μ (m + 1)) := by
        simp [Matrix.charmatrix_apply_eq, jacobiMatrix_apply]
      have hne : Fin.last (m + 1) ≠ Fin.castSucc (Fin.last m) := by simp [Fin.ext_iff]
      have h2 : Matrix.charmatrix (jacobiMatrix μ (m + 2)) (Fin.last (m + 1))
          (Fin.castSucc (Fin.last m)) = -C (Real.sqrt (beta μ m)) := by
        simp only [Matrix.charmatrix_apply_ne _ _ _ hne, jacobiMatrix_apply, Fin.val_last,
          Fin.val_castSucc]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_true]
      have h3 : Matrix.charmatrix (jacobiMatrix μ (m + 2)) (Fin.castSucc (Fin.last m))
          (Fin.last (m + 1)) = -C (Real.sqrt (beta μ m)) := by
        simp only [Matrix.charmatrix_apply_ne _ _ _ hne.symm, jacobiMatrix_apply, Fin.val_last,
          Fin.val_castSucc]
        rw [ite_eq_right (by omega), ite_true]
      rw [h1, h2, h3, neg_mul_neg, ← C_mul, Real.mul_self_sqrt hβ]
    · intro i
      have hne : Fin.last (m + 1) ≠ Fin.castSucc (Fin.castSucc i) := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]; omega
      simp only [Matrix.charmatrix_apply_ne _ _ _ hne, jacobiMatrix_apply, Fin.val_last,
        Fin.val_castSucc]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), map_zero,
        neg_zero]
    · intro i
      have hne : Fin.castSucc (Fin.castSucc i) ≠ Fin.last (m + 1) := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]; omega
      simp only [Matrix.charmatrix_apply_ne _ _ _ hne, jacobiMatrix_apply, Fin.val_last,
        Fin.val_castSucc]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), map_zero,
        neg_zero]
  have h0 : (jacobiMatrix μ 0).charpoly = family μ 0 := by
    rw [family_zero, Matrix.charpoly, Matrix.det_isEmpty]
  have h1 : (jacobiMatrix μ 1).charpoly = family μ 1 := by
    rw [family_one, Matrix.charpoly, Matrix.det_fin_one]
    simp [Matrix.charmatrix_apply_eq, jacobiMatrix_apply]
  revert hnorm
  induction n using Nat.twoStepInduction with
  | zero => exact fun _ => h0
  | one => exact fun _ => h1
  | more m ih₀ ih₁ =>
    intro hnorm
    rw [hrec, ih₀ (fun j hj => hnorm j (by omega)), ih₁ (fun j hj => hnorm j (by omega)),
      three_term_recurrence_of_integrable hint hnorm]

/-- The Jacobi matrix of a weight has the monic orthogonal polynomial as its characteristic
polynomial. -/
theorem charpoly_jacobiMatrix (hw : IsWeight μ) (n : ℕ) :
    (jacobiMatrix μ n).charpoly = family μ n :=
  charpoly_jacobiMatrix_of_integrable hw.integrable_eval n (fun j _ => normSq_ne_zero hw j)

/-! ### The truncated expansion as a best approximation -/

namespace IsWeight

/-- For a weight $\mu$, every polynomial is in $L^2(\mu)$. -/
theorem memLp (hw : IsWeight μ) (p : ℝ[X]) : MemLp (fun x => p.eval x) 2 μ :=
  (memLp_two_iff_integrable_sq p.continuous.aestronglyMeasurable).2 (hw.integrable_eval_sq p)

/-- For a weight $\mu$, the linear map that sends a polynomial to its class in $L^2(\mu)$. -/
def toLpₗ (hw : IsWeight μ) : ℝ[X] →ₗ[ℝ] Lp ℝ 2 μ where
  toFun p := (hw.memLp p).toLp _
  map_add' p q := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by simp)
  map_smul' c p := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by simp)

/-- The class of $p$ in $L^2(\mu)$ is represented, $\mu$-almost everywhere, by the polynomial
function $x \mapsto p(x)$. -/
theorem coeFn_toLpₗ (hw : IsWeight μ) (p : ℝ[X]) :
    ⇑(hw.toLpₗ p) =ᵐ[μ] fun x => p.eval x := (hw.memLp p).coeFn_toLp

/-- For a weight $\mu$, the $L^2(\mu)$ inner product of the classes of two polynomials $p$ and $q$
is $\int p q \, d\mu$. -/
theorem inner_toLpₗ (hw : IsWeight μ) (p q : ℝ[X]) :
    inner ℝ (hw.toLpₗ p) (hw.toLpₗ q) = ∫ x, p.eval x * q.eval x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLpₗ p, hw.coeFn_toLpₗ q] with x hp hq
  rw [hp, hq]
  simp [RCLike.inner_apply, mul_comm]

end IsWeight

/-- For a weight $\mu$, the image in $L^2(\mu)$ of the polynomials of degree at most $N$ is the span
of the classes of $p_0, \dots, p_N$. -/
theorem map_degreeLE_toLpₗ (hw : IsWeight μ) (N : ℕ) :
    (Polynomial.degreeLE ℝ N).map hw.toLpₗ =
      Submodule.span ℝ (Set.range fun k : Fin (N + 1) => hw.toLpₗ (family μ k)) := by
  rw [← Polynomial.Sequence.span_degreeLE (sequence μ)
      (fun i _ => by simp [(monic_family μ i).leadingCoeff]), Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨family μ k, ⟨k, Nat.lt_succ_iff.mp k.2, rfl⟩, rfl⟩

/-- Let $\mu$ be a weight, let $N \in \mathbb{N}$ and let $u \in L^2(\mu)$. Then the truncated
expansion
$$\sum_{k=0}^{N} \frac{\langle p_k, u \rangle}{\|p_k\|^2} \, p_k$$
is a best approximation of $u$ in $L^2(\mu)$ from the polynomials of degree at most $N$: it is
such a polynomial, and no other such polynomial is closer to $u$. This is (3.5.2) of
[han2009theoretical].

The polynomials of degree at most $N$ are the image of `Polynomial.degreeLE ℝ N` under
`OrthogonalPolynomial.IsWeight.toLpₗ`, and the best approximation is `IsBestApprox`. -/
theorem isBestApprox_truncation (hw : IsWeight μ) (N : ℕ) (u : Lp ℝ 2 μ) :
    IsBestApprox ((Polynomial.degreeLE ℝ N).map hw.toLpₗ : Set (Lp ℝ 2 μ)) u
      (∑ k : Fin (N + 1),
        (inner ℝ (hw.toLpₗ (family μ k)) u / normSq μ k) • hw.toLpₗ (family μ k)) := by
  rw [map_degreeLE_toLpₗ hw N, isBestApprox_sum_iff]
  intro j
  rw [Finset.sum_eq_single j]
  · rw [hw.inner_toLpₗ, integral_family_mul_self, div_mul_cancel₀ _ (normSq_ne_zero hw j)]
  · intro i _ hij
    have hne : ((j : ℕ)) ≠ ((i : ℕ)) := fun h => hij (Fin.val_injective h).symm
    rw [hw.inner_toLpₗ, integral_family_mul_family hw hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-!
### Completeness: the orthonormal polynomials as a Hilbert basis

For a weight carried by a compact interval, the polynomials are dense in $L^2(\mu)$. Then an
orthonormal family of polynomials with one member of each degree is a Hilbert basis: the expansion
of every $u \in L^2(\mu)$ converges to $u$ in $L^2(\mu)$, and Parseval's identity holds.
-/

namespace IsWeight

/-- **The polynomials are dense in $L^2(\mu)$** for a weight carried by a compact interval. Let
$\mu$ be a weight with $\mu(\mathbb{R} \setminus [a, b]) = 0$. Then the classes of the
polynomials are dense in $L^2(\mu)$.

The bounded continuous functions are dense in $L^2$ of a finite Borel measure on $\mathbb{R}$
(`BoundedContinuousFunction.toLp_denseRange`). The Weierstrass theorem approximates such a
function uniformly on $[a, b]$, and for a finite measure carried by $[a, b]$ a uniform bound is
an $L^2$ bound (`MeasureTheory.Lp.norm_le_of_ae_bound`). -/
theorem denseRange_toLpₗ (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) :
    DenseRange (hw.toLpₗ : ℝ[X] → Lp ℝ 2 μ) := by
  have := hw.isFiniteMeasure
  -- a uniform bound is an `L²` bound, with a constant depending only on the total mass
  obtain ⟨M, hM0, hMle⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ (F : Lp ℝ 2 μ) (C : ℝ), 0 ≤ C →
      (∀ᵐ x ∂μ, ‖F x‖ ≤ C) → ‖F‖ ≤ M * C := by
    refine ⟨_, ?_, fun F C hC h => Lp.norm_le_of_ae_bound hC h⟩
    positivity
  have hae : ∀ᵐ x ∂μ, x ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  rw [Metric.denseRange_iff]
  intro F ε hε
  set δ : ℝ := ε / 2 / (M + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  -- a bounded continuous function close to `F` in `L²`
  obtain ⟨g, hg⟩ := Metric.denseRange_iff.1
    (BoundedContinuousFunction.toLp_denseRange (p := 2) ℝ μ ℝ (by simp)) F (ε / 2) (by linarith)
  -- a polynomial uniformly close to it on the interval
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b
    ((g : C(ℝ, ℝ)).restrict (Set.Icc a b)) δ hδ0
  refine ⟨p, lt_of_le_of_lt (dist_triangle F (BoundedContinuousFunction.toLp 2 μ ℝ g)
    (hw.toLpₗ p)) ?_⟩
  have hkey : ∀ y ∈ Set.Icc a b, |Polynomial.eval y p - g y| ≤ δ := by
    intro y hy
    have h := ContinuousMap.norm_coe_le_norm
      (p.toContinuousMapOn (Set.Icc a b) - (g : C(ℝ, ℝ)).restrict (Set.Icc a b)) ⟨y, hy⟩
    simpa [Real.norm_eq_abs] using h.trans hp.le
  have hbound : ‖BoundedContinuousFunction.toLp 2 μ ℝ g - hw.toLpₗ p‖ ≤ M * δ := by
    refine hMle _ δ hδ0.le ?_
    filter_upwards [Lp.coeFn_sub (BoundedContinuousFunction.toLp 2 μ ℝ g) (hw.toLpₗ p),
      BoundedContinuousFunction.coeFn_toLp (p := 2) (𝕜 := ℝ) (μ := μ) g, hw.coeFn_toLpₗ p, hae]
      with x hsub hgx hpx hx
    rw [hsub, Pi.sub_apply, hgx, hpx, Real.norm_eq_abs, abs_sub_comm]
    exact hkey x hx
  have hd : δ * (M + 1) = ε / 2 := by rw [hδ]; field_simp
  have hdist : dist (BoundedContinuousFunction.toLp 2 μ ℝ g) (hw.toLpₗ p) ≤ M * δ := by
    rw [dist_eq_norm]; exact hbound
  linarith

end IsWeight

/-- Let $\mu$ be a weight, and let $(q_n)$ be polynomials with $\deg q_n = n$. Then the span of the
classes of the $q_n$ in $L^2(\mu)$ is the image of all polynomials. -/
theorem span_range_toLpₗ (hw : IsWeight μ) {q : ℕ → ℝ[X]} (hdeg : ∀ n, (q n).degree = n) :
    Submodule.span ℝ (Set.range (⇑hw.toLpₗ ∘ q)) = LinearMap.range hw.toLpₗ := by
  have hunit : ∀ i, IsUnit (q i).leadingCoeff := by
    intro i
    refine isUnit_iff_ne_zero.2 (Polynomial.leadingCoeff_ne_zero.2 fun h => ?_)
    have := hdeg i
    rw [h, Polynomial.degree_zero] at this
    simp at this
  rw [Set.range_comp, Submodule.span_image,
    Polynomial.Sequence.span (S := ⟨q, hdeg⟩) hunit, Submodule.map_top]

/-- Let $\mu$ be a weight, and let $(q_n)$ be polynomials with $\deg q_n = n$. Then for every $N$,
the span of the classes of $q_0, \dots, q_N$ in $L^2(\mu)$ is the image of the polynomials of
degree at most $N$. -/
theorem map_degreeLE_toLpₗ_of_degree_eq (hw : IsWeight μ) {q : ℕ → ℝ[X]}
    (hdeg : ∀ n, (q n).degree = n) (N : ℕ) :
    (Polynomial.degreeLE ℝ N).map hw.toLpₗ =
      Submodule.span ℝ (Set.range fun k : Fin (N + 1) => hw.toLpₗ (q k)) := by
  have hunit : ∀ i ≤ N, IsUnit (q i).leadingCoeff := by
    intro i _
    refine isUnit_iff_ne_zero.2 (Polynomial.leadingCoeff_ne_zero.2 fun h => ?_)
    have := hdeg i
    rw [h, Polynomial.degree_zero] at this
    simp at this
  rw [← Polynomial.Sequence.span_degreeLE (S := ⟨q, hdeg⟩) hunit, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨q k, ⟨k, Nat.lt_succ_iff.mp k.2, rfl⟩, rfl⟩

/-- Let $\mu$ be a weight, and let $(q_n)$ be polynomials with $\deg q_n = n$ whose classes are
orthonormal in $L^2(\mu)$. Then for every $N$ and every $u \in L^2(\mu)$, **the truncated
expansion**
$$\sum_{k=0}^{N} \langle q_k, u \rangle \, q_k$$
**is a best approximation of $u$** in $L^2(\mu)$ from the polynomials of degree at most $N$.

This is `OrthogonalPolynomial.isBestApprox_truncation` for a family that is already normalized,
so that the coefficients are the plain inner products. -/
theorem isBestApprox_truncation_of_degree_eq (hw : IsWeight μ) {q : ℕ → ℝ[X]}
    (hdeg : ∀ n, (q n).degree = n) (hon : Orthonormal ℝ fun n => hw.toLpₗ (q n)) (N : ℕ)
    (u : Lp ℝ 2 μ) :
    IsBestApprox ((Polynomial.degreeLE ℝ N).map hw.toLpₗ : Set (Lp ℝ 2 μ)) u
      (∑ k : Fin (N + 1), inner ℝ (hw.toLpₗ (q k)) u • hw.toLpₗ (q k)) := by
  classical
  have hon' : Orthonormal ℝ fun k : Fin (N + 1) => hw.toLpₗ (q k) :=
    hon.comp (fun k : Fin (N + 1) => (k : ℕ)) Fin.val_injective
  rw [map_degreeLE_toLpₗ_of_degree_eq hw hdeg N, isBestApprox_sum_iff]
  intro j
  simp [orthonormal_iff_ite.1 hon' j]

/-- Let $\mu$ be a weight with $\mu(\mathbb{R} \setminus [a, b]) = 0$, and let $(q_n)$ be
polynomials with $\deg q_n = n$ whose classes are orthonormal in $L^2(\mu)$. Then **the classes
of the $q_n$ form a Hilbert basis of $L^2(\mu)$**, indexed by $\mathbb{N}$.

The elements of the basis are the classes of the $q_n$
(`OrthogonalPolynomial.coe_hilbertBasisOfDegreeEq`). Completeness is
`OrthogonalPolynomial.IsWeight.denseRange_toLpₗ`. -/
noncomputable def hilbertBasisOfDegreeEq (hw : IsWeight μ) {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {q : ℕ → ℝ[X]} (hdeg : ∀ n, (q n).degree = n)
    (hon : Orthonormal ℝ fun n => hw.toLpₗ (q n)) : HilbertBasis ℕ ℝ (Lp ℝ 2 μ) := by
  refine HilbertBasis.mk hon ?_
  rw [show (Set.range fun n => hw.toLpₗ (q n)) = Set.range (⇑hw.toLpₗ ∘ q) from rfl,
    span_range_toLpₗ hw hdeg]
  intro x _
  have hx : x ∈ closure (Set.range ⇑hw.toLpₗ) := hw.denseRange_toLpₗ hsupp x
  rwa [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe] at hx

/-- The $n$-th element of `OrthogonalPolynomial.hilbertBasisOfDegreeEq` is the class of $q_n$ in
$L^2(\mu)$. -/
@[simp]
theorem coe_hilbertBasisOfDegreeEq (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    {q : ℕ → ℝ[X]} (hdeg : ∀ n, (q n).degree = n)
    (hon : Orthonormal ℝ fun n => hw.toLpₗ (q n)) :
    ⇑(hilbertBasisOfDegreeEq hw hsupp hdeg hon) = fun n => hw.toLpₗ (q n) :=
  HilbertBasis.coe_mk hon _

/-- For a weight $\mu$, the classes of the orthonormal polynomials $\hat p_n$ are orthonormal in
$L^2(\mu)$. -/
theorem orthonormal_toLpₗ_orthonormalFamily (hw : IsWeight μ) :
    Orthonormal ℝ fun n => hw.toLpₗ (orthonormalFamily μ n) := by
  constructor
  · intro n
    have h : ‖hw.toLpₗ (orthonormalFamily μ n)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hw.inner_toLpₗ]
      simpa only [← sq] using integral_orthonormalFamily_sq hw n
    nlinarith [norm_nonneg (hw.toLpₗ (orthonormalFamily μ n))]
  · intro m n hmn
    rw [hw.inner_toLpₗ]
    exact integral_orthonormalFamily_mul hw hmn

/-- Let $\mu$ be a weight with $\mu(\mathbb{R} \setminus [a, b]) = 0$. Then **the orthonormal
polynomials $\hat p_n$ form a Hilbert basis of $L^2(\mu)$**: every $u \in L^2(\mu)$ is the sum
of its orthogonal expansion, and Parseval's identity holds. [han2009theoretical], Example 3.4.8,
asserts this completeness for the Legendre polynomials.

The elements of the basis are the classes of the $\hat p_n$
(`OrthogonalPolynomial.coe_hilbertBasis`). -/
noncomputable def hilbertBasis (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) :
    HilbertBasis ℕ ℝ (Lp ℝ 2 μ) :=
  hilbertBasisOfDegreeEq hw hsupp (degree_orthonormalFamily hw)
    (orthonormal_toLpₗ_orthonormalFamily hw)

/-- The $n$-th element of `OrthogonalPolynomial.hilbertBasis` is the class of the orthonormal
polynomial $\hat p_n$ in $L^2(\mu)$. -/
@[simp]
theorem coe_hilbertBasis (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) :
    ⇑(hilbertBasis hw hsupp) = fun n => hw.toLpₗ (orthonormalFamily μ n) :=
  coe_hilbertBasisOfDegreeEq _ _ _ _

end OrthogonalPolynomial

/-! ### The Legendre family -/

namespace Polynomial

/-! ### Leibniz rules for the iterated derivative -/

private lemma iterate_derivative_quad_mul (g : ℝ[X]) (k : ℕ) :
    derivative^[k + 2] ((X ^ 2 - 1) * g) =
      (X ^ 2 - 1) * derivative^[k + 2] g + 2 * ((k : ℝ[X]) + 2) * X * derivative^[k + 1] g +
        ((k : ℝ[X]) + 2) * ((k : ℝ[X]) + 1) * derivative^[k] g := by
  induction k with
  | zero =>
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, derivative_add,
      derivative_mul, derivative_sub, derivative_pow, derivative_X, derivative_one,
      derivative_ofNat, map_zero, map_natCast, map_ofNat, Nat.cast_ofNat]
    push_cast
    ring
  | succ k ih =>
    have h1 : derivative (derivative^[k] g) = derivative^[k + 1] g :=
      (Function.iterate_succ_apply' derivative k g).symm
    have h2 : derivative (derivative^[k + 1] g) = derivative^[k + 2] g :=
      (Function.iterate_succ_apply' derivative (k + 1) g).symm
    have h3 : derivative (derivative^[k + 2] g) = derivative^[k + 3] g :=
      (Function.iterate_succ_apply' derivative (k + 2) g).symm
    rw [show k + 1 + 2 = k + 2 + 1 from rfl,
      Function.iterate_succ_apply' derivative (k + 2) ((X ^ 2 - 1) * g), ih]
    simp only [derivative_add, derivative_mul, derivative_sub, derivative_pow, derivative_X,
      derivative_one, derivative_natCast, derivative_ofNat, map_ofNat,
      Nat.cast_ofNat, h1, h2, h3]
    push_cast
    ring

/-! ### The Legendre polynomials -/

/-- The $n$-th **Legendre polynomial**, defined by Rodrigues' formula:
$$P_n = \frac{1}{2^n \, n!} \, \frac{d^n}{dx^n} (x^2 - 1)^n.$$
-/
def legendre (n : ℕ) : ℝ[X] :=
  C ((2 ^ n * n ! : ℝ)⁻¹) * derivative^[n] ((X ^ 2 - 1) ^ n)

/-- The normalizing constant $2^n n!$ of Rodrigues' formula. -/
private def legFac (n : ℕ) : ℝ := 2 ^ n * n !

private lemma legendre_eq (n : ℕ) :
    legendre n = C (legFac n)⁻¹ * derivative^[n] ((X ^ 2 - 1) ^ n) := rfl

private lemma legFac_pos (n : ℕ) : 0 < legFac n := by
  have : 0 < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  simpa [legFac] using by positivity

private lemma legFac_ne_zero (n : ℕ) : legFac n ≠ 0 := (legFac_pos n).ne'

private lemma legFac_succ (n : ℕ) : legFac (n + 1) = 2 * ((n : ℝ) + 1) * legFac n := by
  simp only [legFac, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Rodrigues' formula solved for the iterated derivative:
$\frac{d^n}{dx^n} (x^2 - 1)^n = 2^n n! \, P_n$. -/
private lemma iterate_derivative_pow_eq (n : ℕ) :
    derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n) = C (legFac n) * legendre n := by
  rw [legendre_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (legFac_ne_zero n), C_1, one_mul]

/-! ### The first two Legendre polynomials -/

/-- The zeroth Legendre polynomial is $P_0 = 1$. -/
theorem legendre_zero : legendre 0 = 1 := by
  simp [legendre_eq, legFac]

private lemma derivative_quad : derivative (X ^ 2 - 1 : ℝ[X]) = 2 * X := by
  have h : (X ^ 2 - 1 : ℝ[X]) = X * X - 1 := by ring
  rw [h]
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, sub_zero, mul_one,
    one_mul]
  ring

/-- The first Legendre polynomial is $P_1 = x$. -/
theorem legendre_one : legendre 1 = X := by
  have h2 : (C (2 : ℝ)⁻¹ : ℝ[X]) * 2 = 1 := by
    rw [show (2 : ℝ[X]) = C (2 : ℝ) from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  rw [legendre_eq]
  simp only [legFac, pow_one, Nat.factorial_one, Nat.cast_one, mul_one, Function.iterate_one,
    derivative_quad]
  linear_combination (X : ℝ[X]) * h2

/-! ### The two structural identities -/

private lemma quad_mul_derivative_pow (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative ((X ^ 2 - 1) ^ (n + 1))
      = C (2 * ((n : ℝ) + 1)) * ((X ^ 2 - 1) ^ (n + 1) * X) := by
  rw [derivative_pow_succ, derivative_quad]
  simp only [map_mul, map_add, map_natCast, map_ofNat, map_one]
  ring

private lemma quad_mul_iterate_derivative_succ (j : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative^[j + 3] ((X ^ 2 - 1) ^ (j + 2))
      = ((j : ℝ[X]) + 3) * (((j : ℝ[X]) + 2) * derivative^[j + 1] ((X ^ 2 - 1) ^ (j + 2))) := by
  have hkey := congrArg (fun p : ℝ[X] => derivative^[j + 2] p) (quad_mul_derivative_pow (j + 1))
  simp only [show j + 1 + 1 = j + 2 from rfl] at hkey
  rw [iterate_derivative_quad_mul, iterate_derivative_C_mul, iterate_derivative_mul_X] at hkey
  simp only [← Function.iterate_succ_apply, nsmul_eq_mul, show j + 2 - 1 = j + 1 from rfl,
    map_mul, map_add, map_natCast, map_ofNat, map_one] at hkey
  push_cast at hkey
  linear_combination hkey

private lemma quad_mul_iterate_derivative (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative^[n + 2] ((X ^ 2 - 1) ^ (n + 1))
      = ((n : ℝ[X]) + 2) * (((n : ℝ[X]) + 1) * derivative^[n] ((X ^ 2 - 1) ^ (n + 1))) := by
  cases n with
  | zero =>
    have hd2 : derivative^[0 + 2] ((X ^ 2 - 1 : ℝ[X]) ^ (0 + 1)) = 2 := by
      rw [pow_one, show (0 + 2) = 1 + 1 from rfl, Function.iterate_add_apply,
        Function.iterate_one, derivative_quad]
      simp
    rw [hd2]
    simp only [Nat.cast_zero, zero_add, Function.iterate_zero_apply, pow_one, one_mul]
    ring
  | succ j =>
    have h := quad_mul_iterate_derivative_succ j
    rw [show j + 1 + 2 = j + 3 from rfl, show j + 1 + 1 = j + 2 from rfl]
    push_cast
    linear_combination h

private lemma iterate_derivative_pow_succ_succ (n : ℕ) :
    derivative^[n + 2] ((X ^ 2 - 1 : ℝ[X]) ^ (n + 2))
      = 2 * ((n : ℝ[X]) + 2) *
        (((n : ℝ[X]) + 1) * derivative^[n] ((X ^ 2 - 1) ^ (n + 1))
          + X * derivative^[n + 1] ((X ^ 2 - 1) ^ (n + 1))) := by
  have hu : ((X ^ 2 - 1 : ℝ[X]) ^ (n + 2)) = (X ^ 2 - 1) * (X ^ 2 - 1) ^ (n + 1) := by ring
  rw [hu, iterate_derivative_quad_mul]
  linear_combination quad_mul_iterate_derivative n

private lemma quad_mul_derivative_iterate (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (derivative^[n + 1] ((X ^ 2 - 1) ^ (n + 1)))
      = ((n : ℝ[X]) + 2) * (((n : ℝ[X]) + 1) * derivative^[n] ((X ^ 2 - 1) ^ (n + 1))) := by
  rw [← Function.iterate_succ_apply' derivative (n + 1)]
  exact quad_mul_iterate_derivative n

/-! ### Translation to the Legendre polynomials -/

private lemma natCast_succ_mul_iterate (n : ℕ) :
    ((n : ℝ[X]) + 1) * derivative^[n] ((X ^ 2 - 1) ^ (n + 1))
      = C (legFac (n + 1)) * (legendre (n + 2) - X * legendre (n + 1)) := by
  have hB := iterate_derivative_pow_succ_succ n
  rw [iterate_derivative_pow_eq (n + 2), iterate_derivative_pow_eq (n + 1)] at hB
  have hfac : legFac (n + 2) = 2 * ((n : ℝ) + 2) * legFac (n + 1) := by
    rw [legFac_succ (n + 1)]; push_cast; ring
  rw [hfac] at hB
  simp only [map_mul, map_add, map_natCast, map_ofNat] at hB
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 2) := by positivity
  have hne : (2 * ((n : ℝ[X]) + 2)) ≠ 0 := by
    have h2 : (2 * ((n : ℝ[X]) + 2)) = C (2 * ((n : ℝ) + 2)) := by
      simp only [map_mul, map_add, map_natCast, map_ofNat]
    rw [h2]
    exact C_ne_zero.mpr hpos.ne'
  refine mul_left_cancel₀ hne ?_
  linear_combination -hB

private lemma quad_mul_derivative_legendre_succ (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (legendre (n + 1))
      = ((n : ℝ[X]) + 2) * (legendre (n + 2) - X * legendre (n + 1)) := by
  have hA := quad_mul_derivative_iterate n
  rw [iterate_derivative_pow_eq (n + 1), derivative_C_mul, natCast_succ_mul_iterate n] at hA
  refine mul_left_cancel₀ (C_ne_zero.mpr (legFac_ne_zero (n + 1))) ?_
  linear_combination hA

/-- The Legendre polynomials satisfy $(x^2 - 1) P_n' = (n + 1) (P_{n+1} - x P_n)$ for every $n$. -/
theorem quad_mul_derivative_legendre (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (legendre n)
      = ((n : ℝ[X]) + 1) * (legendre (n + 1) - X * legendre n) := by
  cases n with
  | zero => simp [legendre_zero, legendre_one]
  | succ j =>
    have h := quad_mul_derivative_legendre_succ j
    rw [show j + 1 + 1 = j + 2 from rfl]
    push_cast
    linear_combination h

/-- The Legendre polynomials satisfy $P_{n+1}' = x P_n' + (n + 1) P_n$ for every $n$. -/
theorem derivative_legendre_succ (n : ℕ) :
    derivative (legendre (n + 1))
      = X * derivative (legendre n) + ((n : ℝ[X]) + 1) * legendre n := by
  cases n with
  | zero => simp [legendre_zero, legendre_one]
  | succ j =>
    have hbox : derivative (((j : ℝ[X]) + 1) * derivative^[j] ((X ^ 2 - 1) ^ (j + 1)))
        = derivative (C (legFac (j + 1)) * (legendre (j + 2) - X * legendre (j + 1))) := by
      rw [natCast_succ_mul_iterate j]
    simp only [derivative_mul, derivative_sub, derivative_add, derivative_natCast,
      derivative_one, derivative_C, derivative_X, zero_add, zero_mul, one_mul, add_zero] at hbox
    rw [← Function.iterate_succ_apply' derivative j, iterate_derivative_pow_eq (j + 1)] at hbox
    rw [show j + 1 + 1 = j + 2 from rfl]
    push_cast
    refine mul_left_cancel₀ (C_ne_zero.mpr (legFac_ne_zero (j + 1))) ?_
    linear_combination -hbox

/-- The **Legendre differential equation**: for every $n$,
$$(x^2 - 1) P_n'' + 2x P_n' = n (n + 1) P_n.$$
-/
theorem legendre_ode (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (derivative (legendre n)) + 2 * X * derivative (legendre n)
      = (n : ℝ[X]) * ((n : ℝ[X]) + 1) * legendre n := by
  have h1 : 2 * X * derivative (legendre n)
        + (X ^ 2 - 1 : ℝ[X]) * derivative (derivative (legendre n))
      = ((n : ℝ[X]) + 1) * (derivative (legendre (n + 1))
        - (legendre n + X * derivative (legendre n))) := by
    rw [← derivative_quad, ← derivative_mul, quad_mul_derivative_legendre n]
    simp only [derivative_mul, derivative_sub, derivative_add, derivative_natCast,
      derivative_one, derivative_X, zero_add, zero_mul, one_mul, add_zero]
  linear_combination h1 + ((n : ℝ[X]) + 1) * derivative_legendre_succ n

/-- The **three-term recurrence** of the Legendre polynomials: for every $n$,
$$(n + 2) P_{n+2} = (2n + 3) \, x P_{n+1} - (n + 1) P_n.$$
This is the recurrence $(n + 1) P_{n+1} = (2n + 1) x P_n - n P_{n-1}$ with the index shifted, so
that no subtraction of natural numbers occurs. -/
theorem legendre_recurrence (n : ℕ) :
    ((n : ℝ[X]) + 2) * legendre (n + 2)
      = (2 * (n : ℝ[X]) + 3) * X * legendre (n + 1) - ((n : ℝ[X]) + 1) * legendre n := by
  have h1 := quad_mul_derivative_legendre n
  have h2 := derivative_legendre_succ n
  have h3 := quad_mul_derivative_legendre (n + 1)
  rw [show n + 1 + 1 = n + 2 from rfl] at h3
  push_cast at h3
  linear_combination (-1 : ℝ[X]) * h3 + (X ^ 2 - 1 : ℝ[X]) * h2 + (X : ℝ[X]) * h1

/-! ### Degree -/

private lemma monic_quad : ((X : ℝ[X]) ^ 2 - 1).Monic := by
  have h : ((X : ℝ[X]) ^ 2 - 1) = X ^ 2 - C 1 := by rw [C_1]
  rw [h]
  exact monic_X_pow_sub_C 1 two_ne_zero

private lemma natDegree_quad_pow (n : ℕ) : (((X : ℝ[X]) ^ 2 - 1) ^ n).natDegree = n * 2 := by
  have h : ((X : ℝ[X]) ^ 2 - 1) = X ^ 2 - C 1 := by rw [C_1]
  rw [monic_quad.natDegree_pow, h, natDegree_X_pow_sub_C]

private lemma coeff_iterate_derivative_pow (n : ℕ) :
    (derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n)).coeff n = ((n + n).descFactorial n : ℝ) := by
  have hc : (((X : ℝ[X]) ^ 2 - 1) ^ n).coeff (n + n) = 1 := by
    have h := (monic_quad.pow n).coeff_natDegree
    rw [natDegree_quad_pow] at h
    rw [show n + n = n * 2 by ring]
    exact h
  rw [coeff_iterate_derivative, hc]
  simp

private lemma coeff_iterate_derivative_pow_ne_zero (n : ℕ) :
    (derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n)).coeff n ≠ 0 := by
  rw [coeff_iterate_derivative_pow]
  have h : (n + n).descFactorial n ≠ 0 := by
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  exact_mod_cast h

private lemma natDegree_iterate_derivative_pow (n : ℕ) :
    (derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n)).natDegree = n := by
  refine le_antisymm ?_ (le_natDegree_of_ne_zero (coeff_iterate_derivative_pow_ne_zero n))
  have h := natDegree_iterate_derivative (((X : ℝ[X]) ^ 2 - 1) ^ n) n
  rw [natDegree_quad_pow] at h
  omega

/-- For every $n$, the Legendre polynomial $P_n$ is nonzero. -/
theorem legendre_ne_zero (n : ℕ) : legendre n ≠ 0 := by
  rw [legendre_eq]
  refine mul_ne_zero (C_ne_zero.mpr (inv_ne_zero (legFac_ne_zero n))) ?_
  intro h
  exact coeff_iterate_derivative_pow_ne_zero n (by rw [h, coeff_zero])

/-- For every $n$, the Legendre polynomial $P_n$ has natural degree $n$. -/
theorem natDegree_legendre (n : ℕ) : (legendre n).natDegree = n := by
  rw [legendre_eq, natDegree_C_mul (inv_ne_zero (legFac_ne_zero n))]
  exact natDegree_iterate_derivative_pow n

/-- For every $n$, the Legendre polynomial $P_n$ has degree $n$. -/
theorem degree_legendre (n : ℕ) : (legendre n).degree = n := by
  rw [degree_eq_natDegree (legendre_ne_zero n), natDegree_legendre]

/-- **The explicit form of the Legendre polynomials**: for every $k$,
$$P_k = 2^{-k} \sum_{l=0}^{\lfloor k/2 \rfloor} (-1)^l \binom{k}{l} \binom{2k - 2l}{k} \, x^{k -
  2l}.$$
This is (10.12) of [quarteroni2000numerical].

The proof expands $(x^2 - 1)^k$ in Rodrigues' formula by the binomial theorem and differentiates
$k$ times term by term. The derivative removes the terms with $2l > k$. -/
theorem legendre_eq_sum (k : ℕ) :
    legendre k = C ((2 : ℝ) ^ k)⁻¹ * ∑ l ∈ Finset.range (k / 2 + 1),
      C ((-1) ^ l * (k.choose l : ℝ) * ((2 * k - 2 * l).choose k : ℝ)) * X ^ (k - 2 * l) := by
  have hexp : ((X : ℝ[X]) ^ 2 - 1) ^ k = ∑ m ∈ Finset.range (k + 1),
      C ((-1) ^ (m + k) * (k.choose m : ℝ)) * X ^ (2 * m) := by
    rw [sub_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [C_mul, C_pow, C_neg, C_1, map_natCast, one_pow, mul_one, pow_mul]
    ring
  have hder : derivative^[k] (((X : ℝ[X]) ^ 2 - 1) ^ k) = ∑ m ∈ Finset.range (k + 1),
      C ((-1) ^ (m + k) * (k.choose m : ℝ) * ((2 * m).descFactorial k : ℝ)) * X ^ (2 * m - k) := by
    rw [hexp, iterate_derivative_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul, ← mul_assoc, ← C_mul]
  have hsub : Finset.range (k / 2 + 1) ⊆ Finset.range (k + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hvanish : ∀ l ∈ Finset.range (k + 1), l ∉ Finset.range (k / 2 + 1) →
      C ((-1) ^ l * (k.choose l : ℝ) * ((2 * k - 2 * l).choose k : ℝ)) * X ^ (k - 2 * l) = 0 := by
    intro l hl hl'
    have : 2 * k - 2 * l < k := by
      rw [Finset.mem_range] at hl hl'
      omega
    rw [Nat.choose_eq_zero_of_lt this]
    simp
  rw [Finset.sum_subset hsub hvanish, legendre, hder, Finset.mul_sum, Finset.mul_sum]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [add_tsub_cancel_right]
  have hlk : l ≤ k := by
    simp only [Finset.mem_range] at hl
    omega
  have hfac : ((k ! : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  by_cases h2 : 2 * l ≤ k
  · have e1 : 2 * (k - l) - k = k - 2 * l := by omega
    have e2 : 2 * (k - l) = 2 * k - 2 * l := by omega
    have e3 : k - l + k = l + 2 * (k - l) := by omega
    rw [e1, e2, e3, pow_add, pow_mul, neg_one_sq, one_pow, mul_one, Nat.choose_symm hlk,
      Nat.descFactorial_eq_factorial_mul_choose, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
    congr 2
    push_cast
    field_simp
  · have h3 : 2 * (k - l) < k := by omega
    have h4 : 2 * k - 2 * l < k := by omega
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr h3, Nat.choose_eq_zero_of_lt h4]
    simp

/-! ### Value at the right endpoint -/

/-- For every $n$, the Legendre polynomial satisfies $P_n(1) = 1$. -/
theorem legendre_eval_one (n : ℕ) : (legendre n).eval 1 = 1 := by
  have hsplit : ((X : ℝ[X]) ^ 2 - 1) ^ n = (X - C 1) ^ n * (X + C 1) ^ n := by
    rw [← mul_pow, C_1]; ring
  rw [legendre_eq, hsplit, iterate_derivative_mul, eval_mul, eval_C, eval_finsetSum,
    Finset.sum_eq_single 0]
  · rw [Nat.sub_zero, Nat.choose_zero_right, Function.iterate_zero_apply,
      iterate_derivative_X_sub_pow_self]
    simp only [one_smul, eval_mul, eval_natCast, eval_pow, eval_add, eval_X, eval_C, legFac]
    rw [show ((1 : ℝ) + 1) = 2 by norm_num]
    field_simp
  · intro k hk hk0
    rw [Finset.mem_range] at hk
    rw [iterate_derivative_X_sub_pow, show n - (n - k) = k by omega]
    simp [hk0]
  · intro h
    simp at h

/-! ### Orthogonality -/

/-- The integral $\int_{-1}^{1} p(x) \, dx$ of a polynomial. -/
private def legInt (p : ℝ[X]) : ℝ := ∫ x in (-1 : ℝ)..1, p.eval x

private lemma legInt_intervalIntegrable (p : ℝ[X]) :
    IntervalIntegrable (fun x => p.eval x) MeasureTheory.volume (-1) 1 :=
  (p.differentiable (𝕜 := ℝ)).continuous.intervalIntegrable _ _

private lemma legInt_sub (p q : ℝ[X]) : legInt (p - q) = legInt p - legInt q := by
  simp only [legInt, eval_sub]
  exact intervalIntegral.integral_sub (legInt_intervalIntegrable p) (legInt_intervalIntegrable q)

private lemma legInt_C_mul (a : ℝ) (p : ℝ[X]) : legInt (C a * p) = a * legInt p := by
  simp only [legInt, eval_mul, eval_C]
  exact intervalIntegral.integral_const_mul a _

private lemma legInt_mul (p q : ℝ[X]) :
    legInt (p * q) = ∫ x in (-1 : ℝ)..1, p.eval x * q.eval x := by
  simp only [legInt, eval_mul]

private lemma legInt_one : legInt 1 = 2 := by
  simp only [legInt, eval_one, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  norm_num

private lemma legInt_derivative (p : ℝ[X]) : legInt (derivative p) = p.eval 1 - p.eval (-1) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => p.hasDerivAt x)
    (legInt_intervalIntegrable (derivative p))

private lemma legInt_derivative_quad_mul (p : ℝ[X]) :
    legInt (derivative ((X ^ 2 - 1) * p)) = 0 := by
  rw [legInt_derivative]
  simp

/-- For all $m$ and $n$, the derivative of $(x^2 - 1)(P_m' P_n - P_m P_n')$ is
$\bigl(m(m + 1) - n(n + 1)\bigr) P_m P_n$, by the two Legendre differential equations. -/
private lemma derivative_wronskian (m n : ℕ) :
    derivative ((X ^ 2 - 1 : ℝ[X]) *
        (derivative (legendre m) * legendre n - legendre m * derivative (legendre n)))
      = C ((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1)) * (legendre m * legendre n) := by
  have hC : (C ((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1)) : ℝ[X])
      = (m : ℝ[X]) * ((m : ℝ[X]) + 1) - (n : ℝ[X]) * ((n : ℝ[X]) + 1) := by
    simp only [map_sub, map_mul, map_add, map_natCast, map_one]
  rw [hC, derivative_mul, derivative_quad]
  simp only [derivative_sub, derivative_mul]
  linear_combination legendre n * legendre_ode m - legendre m * legendre_ode n

private lemma legInt_legendre_mul_legendre_of_ne {m n : ℕ} (h : m ≠ n) :
    legInt (legendre m * legendre n) = 0 := by
  have key := legInt_derivative_quad_mul
    (derivative (legendre m) * legendre n - legendre m * derivative (legendre n))
  rw [derivative_wronskian, legInt_C_mul] at key
  have hne : ((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1)) ≠ 0 := by
    intro hz
    apply h
    have hfac : ((m : ℝ) - (n : ℝ)) * ((m : ℝ) + (n : ℝ) + 1) = 0 := by linear_combination hz
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact_mod_cast sub_eq_zero.mp h1
    · have hpos : (0 : ℝ) < (m : ℝ) + (n : ℝ) + 1 := by positivity
      exact absurd h2 hpos.ne'
  exact (mul_eq_zero.mp key).resolve_left hne

/-- Let $m \neq n$. Then the Legendre polynomials $P_m$ and $P_n$ are orthogonal on $[-1, 1]$:
$$\int_{-1}^{1} P_m(x) P_n(x) \, dx = 0.$$
-/
theorem integral_legendre_mul_legendre_of_ne {m n : ℕ} (h : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre n).eval x = 0 := by
  rw [← legInt_mul]
  exact legInt_legendre_mul_legendre_of_ne h

/-! ### The $L^2$ norm -/

private lemma legInt_recurrence (n j : ℕ) :
    ((n : ℝ) + 2) * legInt (legendre (n + 2) * legendre j)
      = (2 * (n : ℝ) + 3) * legInt (X * legendre (n + 1) * legendre j)
        - ((n : ℝ) + 1) * legInt (legendre n * legendre j) := by
  have hpoly : C ((n : ℝ) + 2) * (legendre (n + 2) * legendre j)
      = C (2 * (n : ℝ) + 3) * (X * legendre (n + 1) * legendre j)
        - C ((n : ℝ) + 1) * (legendre n * legendre j) := by
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one]
    linear_combination legendre j * legendre_recurrence n
  have h := congrArg legInt hpoly
  rwa [legInt_C_mul, legInt_sub, legInt_C_mul, legInt_C_mul] at h

private lemma legInt_cross (n : ℕ) :
    (2 * (n : ℝ) + 3) * legInt (X * legendre (n + 1) * legendre n)
      = ((n : ℝ) + 1) * legInt (legendre n * legendre n) := by
  have h := legInt_recurrence n n
  rw [legInt_legendre_mul_legendre_of_ne (by omega : n + 2 ≠ n)] at h
  linarith

private lemma legInt_cross' (n : ℕ) :
    ((n : ℝ) + 2) * legInt (legendre (n + 2) * legendre (n + 2))
      = (2 * (n : ℝ) + 3) * legInt (X * legendre (n + 2) * legendre (n + 1)) := by
  have h := legInt_recurrence n (n + 2)
  rw [legInt_legendre_mul_legendre_of_ne (by omega : n ≠ n + 2)] at h
  have hcomm : legInt (X * legendre (n + 1) * legendre (n + 2))
      = legInt (X * legendre (n + 2) * legendre (n + 1)) := by
    congr 1
    ring
  rw [hcomm] at h
  linarith

private lemma legInt_sq_step (n : ℕ) :
    (2 * (n : ℝ) + 5) * legInt (legendre (n + 2) * legendre (n + 2))
      = (2 * (n : ℝ) + 3) * legInt (legendre (n + 1) * legendre (n + 1)) := by
  have h1 := legInt_cross' n
  have h2 := legInt_cross (n + 1)
  rw [show n + 1 + 1 = n + 2 from rfl] at h2
  push_cast at h2
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine mul_left_cancel₀ hpos.ne' ?_
  linear_combination (2 * (n : ℝ) + 5) * h1 + (2 * (n : ℝ) + 3) * h2

private lemma legInt_sq_aux (n : ℕ) :
    legInt (legendre n * legendre n) = 2 / (2 * (n : ℝ) + 1) ∧
      legInt (legendre (n + 1) * legendre (n + 1)) = 2 / (2 * (n : ℝ) + 3) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [legendre_zero, mul_one, legInt_one]
      norm_num
    · have h := legInt_cross 0
      simp only [Nat.cast_zero, mul_zero, zero_add, legendre_zero, legendre_one, mul_one,
        one_mul, legInt_one] at h
      simp only [Nat.cast_zero, mul_zero, zero_add, legendre_one]
      linarith
  | succ j ih =>
    refine ⟨?_, ?_⟩
    · rw [ih.2]
      push_cast
      ring_nf
    · have h := legInt_sq_step j
      rw [ih.2] at h
      rw [show j + 1 + 1 = j + 2 from rfl]
      push_cast
      have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
      field_simp at h ⊢
      linarith

/-- For every $n$, the squared $L^2$ norm of the Legendre polynomial on $[-1, 1]$ is
$$\int_{-1}^{1} P_n(x)^2 \, dx = \frac{2}{2n + 1}.$$
-/
theorem integral_legendre_sq (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre n).eval x ^ 2 = 2 / (2 * n + 1) := by
  have h := (legInt_sq_aux n).1
  rw [legInt_mul] at h
  simp only [pow_two]
  exact h

/-- The **orthogonality relations** of the Legendre polynomials: for all $m$ and $n$,
$$\int_{-1}^{1} P_m(x) P_n(x) \, dx = \begin{cases} \dfrac{2}{2n + 1} & \text{if } m = n, \\ 0 &
  \text{if } m \neq n. \end{cases}$$
-/
theorem integral_legendre_mul_legendre (m n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre n).eval x
      = if m = n then (2 : ℝ) / (2 * n + 1) else 0 := by
  split_ifs with h
  · subst h
    rw [← integral_legendre_sq]
    simp only [pow_two]
  · exact integral_legendre_mul_legendre_of_ne h

end Polynomial

/-! ### The Legendre family as an instance of the general theory -/

namespace OrthogonalPolynomial

/-- The **Legendre weight**: Lebesgue measure restricted to the interval $(-1, 1)$. -/
def legendreMeasure : Measure ℝ := volume.restrict (Set.Ioo (-1 : ℝ) 1)

/-- For every function $f \colon \mathbb{R} \to \mathbb{R}$, the integral against the Legendre
weight is the interval integral $\int_{-1}^{1} f(x) \, dx$. -/
theorem integral_legendreMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂legendreMeasure = ∫ x in (-1 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), legendreMeasure,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The Legendre weight is a weight: it has finite moments and is not carried by a finite set. -/
theorem isWeight_legendreMeasure : IsWeight legendreMeasure :=
  isWeight_volume_restrict_Ioo (by norm_num)

/-- The Legendre weight is carried by $[-1, 1]$: it gives no mass to $\mathbb{R} \setminus [-1, 1]$.

This is the hypothesis under which `OrthogonalPolynomial.hilbertBasisOfDegreeEq` and
`OrthogonalPolynomial.hilbertBasis` apply to it. -/
theorem legendreMeasure_compl_Icc : legendreMeasure (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have hempty : (Set.Icc (-1 : ℝ) 1)ᶜ ∩ Set.Ioo (-1 : ℝ) 1 = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun x hx => hx.1 (Set.Ioo_subset_Icc_self hx.2)
  rw [legendreMeasure, Measure.restrict_apply' measurableSet_Ioo, hempty, measure_empty]

/-! ### Identifying a classical family with the monic family -/

variable {μ : Measure ℝ}

/-- **An orthogonal family with one member of each degree is the monic family up to leading
coefficients.** Let $\mu$ be a weight, and let $(q_n)$ be polynomials with $\deg q_n = n$ and
$\int q_n q_m \, d\mu = 0$ for all $m < n$. Then for every $n$,
$$p_n = \frac{1}{\operatorname{lc}(q_n)} \, q_n.$$

The difference of the two monic polynomials of degree $n$ has lower degree and is orthogonal to
every polynomial of degree less than $n$, hence to itself, so it vanishes. This identifies the
Legendre, Chebyshev, Laguerre and Hermite polynomials with the monic family of their weights. -/
theorem family_eq_of_orthogonal (hw : IsWeight μ) {q : ℕ → ℝ[X]} (hdeg : ∀ n, (q n).degree = n)
    (horth : ∀ m n, m < n → ∫ x, (q n).eval x * (q m).eval x ∂μ = 0) (n : ℕ) :
    family μ n = C ((q n).leadingCoeff)⁻¹ * q n := by
  have hne : q n ≠ 0 := fun h => by
    have := hdeg n
    rw [h, degree_zero] at this
    exact absurd this (by simp)
  have hlc : (q n).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hne
  have hdeg' : (C ((q n).leadingCoeff)⁻¹ * q n).degree = (n : WithBot ℕ) := by
    rw [degree_mul, degree_C (inv_ne_zero hlc), zero_add, hdeg]
  have hmonic : (C ((q n).leadingCoeff)⁻¹ * q n).Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  refine sub_eq_zero.mp (eq_zero_of_degree_lt hw (n := n) ?_ ?_)
  · have h := degree_sub_lt_left (p := family μ n) (q := C ((q n).leadingCoeff)⁻¹ * q n)
      (by rw [degree_family, hdeg']) (family_ne_zero _ n)
      (by rw [(monic_family μ n).leadingCoeff, hmonic.leadingCoeff])
    rwa [degree_family] at h
  · intro k hk
    have h1 : ∫ x, (family μ n).eval x * (family μ k).eval x ∂μ = 0 :=
      integral_family_mul_family hw (Nat.ne_of_gt hk)
    have h2 : ∫ x, (C ((q n).leadingCoeff)⁻¹ * q n).eval x * (family μ k).eval x ∂μ = 0 := by
      have hev : ∀ x : ℝ, (C ((q n).leadingCoeff)⁻¹ * q n).eval x * (family μ k).eval x =
          ((q n).leadingCoeff)⁻¹ * ((q n).eval x * (family μ k).eval x) := by
        intro x
        simp only [eval_mul, eval_C]
        ring
      simp only [hev]
      rw [integral_const_mul, integral_mul_of_degree_lt_of_orthogonal hw hdeg horth
        (by rw [degree_family]; exact_mod_cast hk), mul_zero]
    have hev : ∀ x : ℝ, (family μ n - C ((q n).leadingCoeff)⁻¹ * q n).eval x *
        (family μ k).eval x =
        (family μ n).eval x * (family μ k).eval x -
          (C ((q n).leadingCoeff)⁻¹ * q n).eval x * (family μ k).eval x := by
      intro x
      simp only [eval_sub]
      ring
    simp only [hev]
    rw [integral_sub (hw.integrable_eval_mul _ _) (hw.integrable_eval_mul _ _), h1, h2, sub_zero]

/-- Let $\mu$ be a measure, and let $p_n = c \, q$ for a polynomial $q$ and a real number $c$. Then
$$\|p_n\|^2 = c^2 \int q^2 \, d\mu.$$
-/
theorem normSq_eq_of_family_eq {q : ℝ[X]} {c : ℝ} {n : ℕ} (h : family μ n = C c * q) :
    normSq μ n = c ^ 2 * ∫ x, q.eval x ^ 2 ∂μ := by
  rw [normSq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [h, eval_mul, eval_C]
  ring

/-- The Legendre polynomial $P_n$ is orthogonal, for the Legendre weight, to every polynomial $p$ of
degree less than $n$: $\int_{-1}^{1} P_n p \, dx = 0$. -/
theorem integral_legendre_mul_of_degree_lt {n : ℕ} {p : ℝ[X]} (hp : p.degree < n) :
    ∫ x, (legendre n).eval x * p.eval x ∂legendreMeasure = 0 :=
  integral_mul_of_degree_lt_of_orthogonal isWeight_legendreMeasure degree_legendre
    (fun m n hmn => by
      rw [integral_legendreMeasure]
      exact integral_legendre_mul_legendre_of_ne (Nat.ne_of_gt hmn)) hp

/-- For every $n$, the $n$-th monic orthogonal polynomial of the Legendre weight is the monic
rescaling of the Legendre polynomial:
$$p_n = \frac{1}{\operatorname{lc}(P_n)} \, P_n.$$
So the Legendre polynomials are an instance of the general theory. -/
theorem family_eq_legendre (n : ℕ) :
    family legendreMeasure n = C ((legendre n).leadingCoeff)⁻¹ * legendre n :=
  family_eq_of_orthogonal isWeight_legendreMeasure degree_legendre
    (fun m n hmn => by
      rw [integral_legendreMeasure]
      exact integral_legendre_mul_legendre_of_ne (Nat.ne_of_gt hmn)) n

end OrthogonalPolynomial

/-! ### The Chebyshev family -/

namespace Polynomial.Chebyshev

open Real

/-- The **orthogonality relations** of the Chebyshev polynomials $T_n$ for the weight
$(1 - x^2)^{-1/2}$ on $(-1, 1)$: for all $m$ and $n$,
$$\int_{-1}^{1} \frac{T_m(x) T_n(x)}{\sqrt{1 - x^2}} \, dx = \begin{cases} 0 & \text{if } m \neq
  n, \\ \pi & \text{if } m = n = 0, \\ \pi / 2 & \text{if } m = n \neq 0. \end{cases}$$
This is (3.5.8)–(3.5.9) of [han2009theoretical].

The polynomials are Mathlib's `Polynomial.Chebyshev.T ℝ n`. -/
theorem integral_T_mul_T_div_sqrt (m n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (T ℝ m).eval x * (T ℝ n).eval x / √(1 - x ^ 2) =
      if m ≠ n then 0 else if n = 0 then π else π / 2 := by
  have hmeas : ∫ x in (-1 : ℝ)..1, (T ℝ m).eval x * (T ℝ n).eval x / √(1 - x ^ 2) =
      ∫ x, (T ℝ m).eval x * (T ℝ n).eval x ∂measureT := by
    rw [integral_measureT]
    simp [div_eq_mul_inv]
  rw [hmeas]
  rcases eq_or_ne m n with rfl | hmn
  · rcases eq_or_ne m 0 with rfl | hm
    · simpa using integral_eval_T_real_mul_self_measureT_zero
    · simpa [hm] using integral_T_real_mul_self_measureT_of_ne_zero hm
  · simpa [hmn] using integral_eval_T_real_mul_eval_T_real_measureT_of_ne hmn

end Polynomial.Chebyshev

end
